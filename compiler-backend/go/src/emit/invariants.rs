//! Values a loop computes the same on every iteration, computed once before it.
//!
//! A range's bounds are worked out where the range's loop starts, and an array literal is built
//! where it is iterated. When that loop sits in another loop that never changes what they read,
//! the outer loop would repeat the same work on every iteration: `array.RangeSteps(1, size)` for
//! each placement of a queen, or a slice of three closures for each number checked against them.
//! Both are pure, so they move before the outermost loop that leaves their inputs alone.
//!
//! Two loops over the same range in one block, as a `length` and a `fold` of one `map`, share
//! the first's bounds.

use rustc_hash::{FxHashMap, FxHashSet};

use super::lengths::written_by_literals;
use crate::go_traversal::{self, Walk, each_expression_in_declaration};
use crate::naming::numbered;
use crate::syntax::{
    DeclarationNames, GoDeclaration, GoExpression, GoStatement, GoType, Name, statements_names,
};

/// `taken` tells which names a new local must not shadow.
pub fn hoist_loop_invariants(
    declarations: &mut [GoDeclaration],
    names: &mut [DeclarationNames],
    taken: &dyn Fn(&str) -> bool,
) {
    for (declaration, names) in declarations.iter_mut().zip(names) {
        let written_by_literals = written_by_literals(declaration);
        let mut function = Function { names: &mut names.names, written_by_literals, taken };
        if let GoDeclaration::Function { body, .. } = declaration {
            function.block(body);
        }
        each_expression_in_declaration(declaration, |value| {
            if let GoExpression::Function { body, .. } = value {
                function.block(body);
            }
        });
    }
}

struct Function<'a> {
    names: &'a mut FxHashSet<String>,
    written_by_literals: FxHashSet<String>,
    taken: &'a dyn Fn(&str) -> bool,
}

impl Walk for Function<'_> {
    /// Inner loops first, so that what leaves an inner loop can leave the outer one too.
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        let mut at = 0;
        while at < body.len() {
            self.statement(&mut body[at]);
            let hoisted = match loop_body(&mut body[at]) {
                Some(_) => self.invariants(&mut body[at]),
                None => vec![],
            };
            let count = hoisted.len();
            body.splice(at..at, hoisted);
            at += count + 1;
        }
        share_repeated_steps(body);
    }

    fn expression(&mut self, _: &mut GoExpression) {}
}

impl Function<'_> {
    /// Takes the loop's invariant steps and literals out of its body, and returns the
    /// definitions that compute them once.
    fn invariants(&mut self, looped: &mut GoStatement) -> Vec<GoStatement> {
        let names = loop_names(looped, &self.written_by_literals);
        let body = loop_body(looped).expect("invariant violated: only loops are searched");
        let mut hoisted = vec![];
        let mut at = 0;
        while at < body.len() {
            if let GoStatement::Define { names: defined, values } = &body[at]
                && let [value] = values.as_slice()
                && is_range_steps(value)
                && defined.iter().all(|name| names.bound_once(name))
                && is_invariant(value, &names)
            {
                hoisted.push(body.remove(at));
                continue;
            }
            let (current, rest) = body[at..].split_at_mut(1);
            if let GoStatement::Define { names: defined, values } = &current[0]
                && let ([defined], [value]) = (defined.as_slice(), values.as_slice())
                && is_iterable_literal(value)
                && names.bound_once(defined)
                && is_invariant(value, &names)
                && is_only_iterated(rest, defined)
            {
                hoisted.push(body.remove(at));
                continue;
            }
            if let GoStatement::Range { element, iterable, body: inner, .. } = &mut body[at]
                && is_iterable_literal(iterable)
                && is_invariant(iterable, &names)
                && !writes(inner, element)
            {
                let base =
                    if element == "_" { "elements".to_string() } else { format!("{element}s") };
                let local = self.fresh(&base);
                let literal = std::mem::replace(iterable, GoExpression::Identifier(local.clone()));
                hoisted.push(GoStatement::Define { names: vec![local], values: vec![literal] });
            }
            at += 1;
        }
        hoisted
    }

    fn fresh(&mut self, base: &str) -> String {
        let candidate = numbered(base, |name| self.names.contains(name) || (self.taken)(name));
        self.names.insert(candidate.clone());
        candidate
    }
}

struct LoopNames {
    /// Every variable the loop binds or writes, its own binders included.
    changed: FxHashSet<String>,
    bindings: FxHashMap<String, usize>,
}

impl LoopNames {
    fn bound_once(&self, name: &str) -> bool {
        name == "_" || self.bindings.get(name) == Some(&1)
    }
}

fn loop_names(looped: &mut GoStatement, written_by_literals: &FxHashSet<String>) -> LoopNames {
    let mut changed = written_by_literals.clone();
    let mut bindings: FxHashMap<String, usize> = FxHashMap::default();
    statements_names(std::slice::from_mut(looped), &mut |name| match name {
        Name::Binder(name) => {
            *bindings.entry(name.clone()).or_default() += 1;
            changed.insert(name.clone());
        }
        Name::Written(name) => {
            *bindings.entry(name.clone()).or_default() += 1;
            changed.insert(name.clone());
        }
        Name::Reference(_) => {}
    });
    LoopNames { changed, bindings }
}

fn loop_body(statement: &mut GoStatement) -> Option<&mut Vec<GoStatement>> {
    match statement {
        GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. }
        | GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. } => Some(body),
        _ => None,
    }
}

fn is_range_steps(value: &GoExpression) -> bool {
    matches!(value, GoExpression::Call { function, .. }
        if matches!(&**function, GoExpression::Qualified { package, name }
            if package == "array" && name == "RangeSteps"))
}

/// Whether the value reads nothing the loop changes. A function literal in it binds its own
/// names, which the rest of the loop must not bind too for them to be told apart.
fn is_invariant(value: &GoExpression, loop_names: &LoopNames) -> bool {
    let mut references = vec![];
    let mut bindings: FxHashMap<String, usize> = FxHashMap::default();
    let mut statement = [GoStatement::Expression(value.clone())];
    statements_names(&mut statement, &mut |name| match name {
        Name::Reference(name) => references.push(name.clone()),
        Name::Binder(name) | Name::Written(name) => {
            *bindings.entry(name.clone()).or_default() += 1;
        }
    });
    let own = bindings.iter().all(|(name, count)| loop_names.bindings.get(name) == Some(count));
    own && references
        .iter()
        .all(|name| bindings.contains_key(name) || !loop_names.changed.contains(name))
}

fn is_iterable_literal(value: &GoExpression) -> bool {
    matches!(value, GoExpression::Composite { type_: GoType::Slice(_), .. })
        && is_built_without_calls(value)
}

/// Whether the statements read the slice only by ranging over it, so that no iteration can
/// change what the next one sees.
fn is_only_iterated(statements: &mut [GoStatement], slice: &str) -> bool {
    let mut references = 0;
    statements_names(statements, &mut |name| {
        if let Name::Reference(name) | Name::Written(name) = name {
            references += usize::from(name == slice);
        }
    });
    let mut iterations = Iterations { slice, count: 0, written_element: false };
    statements.iter_mut().for_each(|statement| iterations.statement(statement));
    references == iterations.count && !iterations.written_element
}

struct Iterations<'s> {
    slice: &'s str,
    count: usize,
    written_element: bool,
}

impl Walk for Iterations<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Range { element, iterable, body, .. } = statement
            && matches!(iterable, GoExpression::Identifier(name) if name == self.slice)
        {
            self.count += 1;
            self.written_element |= writes(body, element);
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, _: &mut GoExpression) {}
}

/// Whether building the value calls nothing, which could run an effect; a function literal in
/// it is built, not called.
fn is_built_without_calls(value: &GoExpression) -> bool {
    match value {
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Utf16(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_)
        | GoExpression::Function { .. } => true,
        GoExpression::Composite { fields, .. } => {
            fields.iter().all(|(_, field)| is_built_without_calls(field))
        }
        GoExpression::Unary { operator, operand } => {
            matches!(*operator, "-" | "!" | "^") && is_built_without_calls(operand)
        }
        GoExpression::Field { value, .. } | GoExpression::Conversion { value, .. } => {
            is_built_without_calls(value)
        }
        GoExpression::Attributed { value, .. } => is_built_without_calls(value),
        _ => false,
    }
}

fn writes(body: &mut [GoStatement], variable: &str) -> bool {
    let mut written = false;
    statements_names(body, &mut |name| {
        if let Name::Written(name) = name {
            written |= name == variable;
        }
    });
    written
}

/// Gives a later `RangeSteps` of the same bounds the variables of the first, when nothing
/// between them writes what the bounds read.
fn share_repeated_steps(body: &mut Vec<GoStatement>) {
    let mut first = 0;
    while first < body.len() {
        if let GoStatement::Define { values, .. } = &body[first]
            && let [value] = values.as_slice()
            && is_range_steps(value)
        {
            share_steps_from(body, first);
        }
        first += 1;
    }
}

fn share_steps_from(body: &mut Vec<GoStatement>, first: usize) {
    let GoStatement::Define { values, .. } = &body[first] else { return };
    let steps = values[0].clone();
    let Some(bounds) = simple_names(&steps) else { return };
    let mut later = first + 1;
    while later < body.len() {
        let repeated = matches!(&body[later], GoStatement::Define { values, .. }
            if matches!(values.as_slice(), [value] if same_simple(value, &steps)));
        if repeated {
            let GoStatement::Define { names: repeated_names, .. } = body.remove(later) else {
                unreachable!("invariant violated: the repeated steps were just matched")
            };
            let GoStatement::Define { names: first_names, .. } = &mut body[first] else {
                unreachable!("invariant violated: the first steps were just matched")
            };
            let mut renamed: FxHashMap<String, String> = FxHashMap::default();
            for (first_name, repeated_name) in first_names.iter_mut().zip(repeated_names) {
                match (first_name.as_str(), repeated_name.as_str()) {
                    (_, "_") => {}
                    ("_", _) => *first_name = repeated_name,
                    _ => {
                        renamed.insert(repeated_name, first_name.clone());
                    }
                }
            }
            statements_names(&mut body[later..], &mut |name| {
                if let Name::Reference(name) = name
                    && let Some(shared) = renamed.get(name.as_str())
                {
                    *name = shared.clone();
                }
            });
            continue;
        }
        let mut written = false;
        statements_names(std::slice::from_mut(&mut body[later]), &mut |name| {
            if let Name::Written(name) | Name::Binder(name) = name {
                written |= bounds.contains(name.as_str());
            }
        });
        if written {
            return;
        }
        later += 1;
    }
}

/// The variables a value reads, when it is made of names, integers, arithmetic and calls only.
fn simple_names(value: &GoExpression) -> Option<FxHashSet<&str>> {
    let mut names = FxHashSet::default();
    collect_simple_names(value, &mut names).then_some(names)
}

fn collect_simple_names<'v>(value: &'v GoExpression, names: &mut FxHashSet<&'v str>) -> bool {
    match value {
        GoExpression::Identifier(name) => {
            names.insert(name);
            true
        }
        GoExpression::Qualified { .. } | GoExpression::Integer(_) => true,
        GoExpression::Binary { left, right, .. } => {
            collect_simple_names(left, names) && collect_simple_names(right, names)
        }
        GoExpression::Unary { operand, .. } => collect_simple_names(operand, names),
        GoExpression::Conversion { value, .. } => collect_simple_names(value, names),
        GoExpression::Call { function, arguments } => {
            collect_simple_names(function, names)
                && arguments.iter().all(|argument| collect_simple_names(argument, names))
        }
        _ => false,
    }
}

fn same_simple(left: &GoExpression, right: &GoExpression) -> bool {
    match (left, right) {
        (GoExpression::Identifier(left), GoExpression::Identifier(right)) => left == right,
        (
            GoExpression::Qualified { package, name },
            GoExpression::Qualified { package: right_package, name: right_name },
        ) => package == right_package && name == right_name,
        (GoExpression::Integer(left), GoExpression::Integer(right)) => left == right,
        (
            GoExpression::Binary { operator, left, right },
            GoExpression::Binary { operator: right_operator, left: other_left, right: other_right },
        ) => {
            operator == right_operator
                && same_simple(left, other_left)
                && same_simple(right, other_right)
        }
        (
            GoExpression::Unary { operator, operand },
            GoExpression::Unary { operator: right_operator, operand: right_operand },
        ) => operator == right_operator && same_simple(operand, right_operand),
        (
            GoExpression::Conversion { type_, value },
            GoExpression::Conversion { type_: right_type, value: right_value },
        ) => type_ == right_type && same_simple(value, right_value),
        (
            GoExpression::Call { function, arguments },
            GoExpression::Call { function: right_function, arguments: right_arguments },
        ) => {
            same_simple(function, right_function)
                && arguments.len() == right_arguments.len()
                && arguments
                    .iter()
                    .zip(right_arguments)
                    .all(|(left, right)| same_simple(left, right))
        }
        _ => false,
    }
}
