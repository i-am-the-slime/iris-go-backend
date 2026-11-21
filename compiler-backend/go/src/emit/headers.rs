//! Mutable arrays read through one load of their slice.
//!
//! A mutable array is a pointer to a slice, so that a push can replace the
//! slice. Every `(*array)[i]` and `len(*array)` loads the slice header again,
//! as Go cannot tell that a store to an element leaves the header alone.
//!
//! Some code cannot change any array's header: it assigns nothing through a
//! pointer (a push assigns `*array`), makes no closure, and calls only
//! builtins that measure, the pure part of the runtime, and functions that
//! cannot change a header either. In such code the slice `*array` is the
//! same at every point, and an element written through one copy of it is
//! written in the array.
//!
//! - A function that cannot change a header and only reads, writes and
//!   measures the elements of an array parameter takes the slice itself:
//!   `func get(array []float64, i int32)`, called as `get(*xs, i)`.
//! - A loop that cannot change a header reads each array it indexes once,
//!   before it starts: `elements := *xs`.
//! - A function that cannot change a header but is also used as a value, so
//!   that its signature stays, reads each array parameter once on entry.

use rustc_hash::{FxHashMap, FxHashSet};

use super::locals::NUMBERED;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};
use crate::walk::{self, Walk};

/// Runtime functions in `prim` that compute from their arguments alone. The
/// others run effects they are handed, as `STFor` and `RunEffectFn2` do.
const PURE_RUNTIME: &[&str] = &[
    "Number", "Int", "String", "Show", "Char", "CodeUnit", "Big", "Num", "Eq", "Ord", "To",
    "From", "Append", "Rune",
];

pub(super) fn read_headers_once(declarations: &mut [GoDeclaration]) {
    let keeping = Keeping::of(declarations);
    let sliced = pass_slices(declarations, &keeping);
    for declaration in declarations.iter_mut() {
        let GoDeclaration::Function { name, .. } = declaration else { continue };
        let entry = keeping.functions.contains(name.as_str());
        let mut names = declaration.all_names();
        let GoDeclaration::Function { parameters, body, .. } = declaration else { unreachable!() };
        if entry {
            hoist_parameters(parameters, body, &sliced, &mut names);
        }
        hoist_in_loops(body, &keeping, &sliced, &mut names);
    }
}

/// The functions that cannot change an array's header.
struct Keeping {
    functions: FxHashSet<String>,
}

impl Keeping {
    fn of(declarations: &mut [GoDeclaration]) -> Self {
        let mut functions: FxHashSet<String> = declarations
            .iter()
            .filter_map(|declaration| match declaration {
                GoDeclaration::Function { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect();
        loop {
            let mut keeping = Keeping { functions };
            let before = keeping.functions.len();
            let mut dropped = vec![];
            for declaration in declarations.iter_mut() {
                if let GoDeclaration::Function { name, body, .. } = declaration
                    && keeping.functions.contains(name.as_str())
                    && !keeping.keeps(body)
                {
                    dropped.push(name.clone());
                }
            }
            for name in dropped {
                keeping.functions.remove(&name);
            }
            if keeping.functions.len() == before {
                return keeping;
            }
            functions = keeping.functions;
        }
    }

    /// Whether the statements cannot change an array's header.
    fn keeps(&self, body: &mut [GoStatement]) -> bool {
        let mut keeps = !writes_through_pointer(body);
        for statement in body.iter_mut() {
            keeps &= !matches!(statement, GoStatement::Defer(_));
            walk::each_expression_in_statement(statement, |expression| match expression {
                GoExpression::Call { function, .. } => keeps &= self.keeps_call(function),
                GoExpression::Function { .. } => keeps = false,
                _ => {}
            });
        }
        keeps
    }

    fn keeps_call(&self, function: &GoExpression) -> bool {
        match function {
            GoExpression::Identifier(name) => {
                matches!(name.as_str(), "len" | "cap") || self.functions.contains(name.as_str())
            }
            GoExpression::Qualified { package, name } => {
                package == "prim" && PURE_RUNTIME.iter().any(|prefix| name.starts_with(prefix))
            }
            _ => false,
        }
    }
}

/// The parameters, by position, that each function takes as a slice.
type Sliced = FxHashMap<String, Vec<bool>>;

fn pass_slices(declarations: &mut [GoDeclaration], keeping: &Keeping) -> Sliced {
    let values = used_as_values(declarations);
    let mut sliced: Sliced = FxHashMap::default();
    loop {
        let mut changed = vec![];
        for declaration in declarations.iter_mut() {
            let GoDeclaration::Function { name, parameters, body, .. } = declaration else {
                continue;
            };
            if !keeping.functions.contains(name.as_str()) || values.contains(name.as_str()) {
                continue;
            }
            let arity = parameters.len();
            for (position, (parameter, type_)) in parameters.iter().enumerate() {
                let GoType::Pointer(inner) = type_ else { continue };
                let own = Some((name.as_str(), position));
                if matches!(**inner, GoType::Slice(_)) && only_indexed(body, parameter, &sliced, own) {
                    changed.push((name.clone(), position, arity));
                }
            }
        }
        if changed.is_empty() {
            return sliced;
        }
        for (name, position, arity) in &changed {
            let positions = sliced.entry(name.clone()).or_insert_with(|| vec![false; *arity]);
            positions[*position] = true;
        }
        let newly: FxHashMap<&str, Vec<usize>> = changed.iter().fold(
            FxHashMap::default(),
            |mut by_name, (name, position, _)| {
                by_name.entry(name.as_str()).or_default().push(*position);
                by_name
            },
        );
        for declaration in declarations.iter_mut() {
            walk::each_expression_in_declaration(declaration, |expression| {
                if let GoExpression::Call { function, arguments } = expression
                    && let GoExpression::Identifier(callee) = &**function
                    && let Some(positions) = newly.get(callee.as_str())
                {
                    for position in positions {
                        let argument = std::mem::replace(
                            &mut arguments[*position],
                            GoExpression::Boolean(false),
                        );
                        arguments[*position] = match argument {
                            GoExpression::Address(inner) => *inner,
                            argument => deref(argument),
                        };
                    }
                }
            });
        }
        for declaration in declarations.iter_mut() {
            let GoDeclaration::Function { name, parameters, body, .. } = declaration else {
                continue;
            };
            let Some(positions) = newly.get(name.as_str()) else { continue };
            for position in positions {
                let (parameter, type_) = &mut parameters[*position];
                let GoType::Pointer(inner) = type_ else { unreachable!("a sliced pointer") };
                *type_ = (**inner).clone();
                replace_dereferences(body, parameter, parameter);
            }
        }
    }
}

/// The functions some code refers to other than by calling them.
fn used_as_values(declarations: &mut [GoDeclaration]) -> FxHashSet<String> {
    struct Values(FxHashSet<String>);
    impl Walk for Values {
        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Call { function, arguments } => {
                    if !matches!(&**function, GoExpression::Identifier(_)) {
                        self.expression(function);
                    }
                    arguments.iter_mut().for_each(|argument| self.expression(argument));
                }
                GoExpression::Identifier(name) => {
                    self.0.insert(name.clone());
                }
                _ => walk::expression(self, value),
            }
        }
    }
    let mut values = Values(FxHashSet::default());
    for declaration in declarations.iter_mut() {
        walk::declaration(&mut values, declaration);
    }
    values.0
}

/// Whether the code uses `array` only to index, measure, or hand its slice to
/// a function that takes the slice.
/// `own` is the function and position the array is a parameter of, whose
/// recursive calls pass it on as it is.
fn only_indexed(
    body: &mut [GoStatement],
    array: &str,
    sliced: &Sliced,
    own: Option<(&str, usize)>,
) -> bool {
    struct Uses<'a> {
        array: &'a str,
        sliced: &'a Sliced,
        own: Option<(&'a str, usize)>,
        indexed: usize,
        other: bool,
    }
    impl Walk for Uses<'_> {
        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Index { value: base, index } if is_dereference(base, self.array) => {
                    self.indexed += 1;
                    self.expression(index);
                }
                GoExpression::Call { function, arguments } => {
                    let positions = match &**function {
                        GoExpression::Identifier(name) if matches!(name.as_str(), "len" | "cap") => {
                            Some(vec![true; arguments.len()])
                        }
                        GoExpression::Identifier(name) => self.sliced.get(name.as_str()).cloned(),
                        _ => None,
                    };
                    let callee = match &**function {
                        GoExpression::Identifier(name) => Some(name.clone()),
                        _ => None,
                    };
                    self.expression(function);
                    for (position, argument) in arguments.iter_mut().enumerate() {
                        let takes_slice = positions
                            .as_ref()
                            .is_some_and(|positions| positions.get(position) == Some(&true));
                        let passed_on = self.own.is_some_and(|(own, own_position)| {
                            callee.as_deref() == Some(own) && position == own_position
                        }) && matches!(argument, GoExpression::Identifier(name) if name == self.array);
                        if takes_slice && is_dereference(argument, self.array) || passed_on {
                            self.indexed += 1;
                        } else {
                            self.expression(argument);
                        }
                    }
                }
                GoExpression::Identifier(name) if name == self.array => self.other = true,
                GoExpression::Function { .. } => {
                    let mut inner = Uses { indexed: 0, other: false, ..*self };
                    walk::expression(&mut inner, value);
                    self.other |= inner.other || inner.indexed > 0;
                }
                _ => walk::expression(self, value),
            }
        }
    }
    let mut uses = Uses { array, sliced, own, indexed: 0, other: false };
    body.iter_mut().for_each(|statement| uses.statement(statement));
    !uses.other && uses.indexed > 0
}

/// Reads each array parameter that the function only indexes once, on entry.
fn hoist_parameters(
    parameters: &[(String, GoType)],
    body: &mut Vec<GoStatement>,
    sliced: &Sliced,
    names: &mut FxHashSet<String>,
) {
    let mut hoisted = vec![];
    for (array, type_) in parameters {
        let GoType::Pointer(inner) = type_ else { continue };
        if !matches!(**inner, GoType::Slice(_)) || dereferences(body, array) < 2 {
            continue;
        }
        if !only_indexed(body, array, sliced, None) {
            continue;
        }
        hoisted.push(hoist(body, array, names));
    }
    body.splice(0..0, hoisted);
}

/// Before each outermost loop that cannot change a header, reads once each
/// array the loop only indexes.
fn hoist_in_loops(
    block: &mut Vec<GoStatement>,
    keeping: &Keeping,
    sliced: &Sliced,
    names: &mut FxHashSet<String>,
) {
    let mut position = 0;
    while position < block.len() {
        let statement = &mut block[position];
        if is_loop(statement) && keeping.keeps(std::slice::from_mut(statement)) {
            let arrays: Vec<String> = dereferenced(statement)
                .into_iter()
                .filter(|array| {
                    !binds(statement, array)
                        && only_indexed(std::slice::from_mut(statement), array, sliced, None)
                })
                .collect();
            let hoisted: Vec<GoStatement> = arrays
                .iter()
                .map(|array| hoist(std::slice::from_mut(statement), array, names))
                .collect();
            let count = hoisted.len();
            block.splice(position..position, hoisted);
            position += count + 1;
            continue;
        }
        each_nested_block(statement, |nested| hoist_in_loops(nested, keeping, sliced, names));
        position += 1;
    }
}

fn hoist(body: &mut [GoStatement], array: &str, names: &mut FxHashSet<String>) -> GoStatement {
    let elements = fresh("elements", names);
    replace_dereferences(body, array, &elements);
    let read = deref(GoExpression::Identifier(array.to_string()));
    GoStatement::Define { names: vec![elements], values: vec![read] }
}

fn is_loop(statement: &GoStatement) -> bool {
    matches!(
        statement,
        GoStatement::Range { .. }
            | GoStatement::Counting { .. }
            | GoStatement::CountingDown { .. }
            | GoStatement::Loop(_)
            | GoStatement::LabeledLoop { .. }
    )
}

fn each_nested_block(statement: &mut GoStatement, mut visit: impl FnMut(&mut Vec<GoStatement>)) {
    match statement {
        GoStatement::If { then, otherwise, .. } => {
            visit(then);
            visit(otherwise);
        }
        GoStatement::Switch { cases, default, .. } => {
            cases.iter_mut().for_each(|case| visit(&mut case.body));
            if let Some(default) = default {
                visit(&mut default.body);
            }
        }
        GoStatement::IfAssert { then: body, .. }
        | GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. }
        | GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. } => visit(body),
        _ => {}
    }
}

/// The names the statement dereferences.
fn dereferenced(statement: &mut GoStatement) -> Vec<String> {
    let mut found = vec![];
    walk::each_expression_in_statement(statement, |expression| {
        if let GoExpression::Unary { operator: "*", operand } = expression
            && let GoExpression::Identifier(name) = &**operand
            && !found.contains(name)
        {
            found.push(name.clone());
        }
    });
    found
}

/// Whether the statement binds `name` itself, so that it is not one value
/// throughout.
fn binds(statement: &mut GoStatement, name: &str) -> bool {
    let mut found = false;
    let mut binder = |bound: &str| found |= bound == name;
    struct Binders<'a, F: FnMut(&str)>(&'a mut F);
    impl<F: FnMut(&str)> Walk for Binders<'_, F> {
        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Define { names, .. } => names.iter().for_each(|name| (self.0)(name)),
                GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => (self.0)(name),
                GoStatement::Assign { targets, .. } => {
                    for target in targets.iter() {
                        if let GoExpression::Identifier(name) = target {
                            (self.0)(name);
                        }
                    }
                }
                GoStatement::Range { index, element, .. } => {
                    index.iter().for_each(|index| (self.0)(index));
                    (self.0)(element);
                }
                GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                    (self.0)(variable)
                }
                _ => {}
            }
            walk::statement(self, statement);
        }
    }
    Binders(&mut binder).statement(statement);
    found
}

/// Whether the function assigns a whole pointed-to value, as a push does.
fn writes_through_pointer(body: &mut [GoStatement]) -> bool {
    struct Writes(bool);
    impl Walk for Writes {
        fn statement(&mut self, statement: &mut GoStatement) {
            if let GoStatement::Assign { targets, .. } = statement {
                self.0 |= targets
                    .iter()
                    .any(|target| matches!(target, GoExpression::Unary { operator: "*", .. }));
            }
            walk::statement(self, statement);
        }
    }
    let mut writes = Writes(false);
    body.iter_mut().for_each(|statement| writes.statement(statement));
    writes.0
}

/// How often the function dereferences `array` to read or write its elements
/// or length: zero when it uses the pointer any other way.
fn dereferences(body: &mut Vec<GoStatement>, array: &str) -> usize {
    struct Count<'a> {
        array: &'a str,
        dereferences: usize,
        other: bool,
    }
    impl Walk for Count<'_> {
        fn statement(&mut self, statement: &mut GoStatement) {
            if let GoStatement::Assign { targets, .. } = statement
                && targets.iter().any(|target| is_dereference(target, self.array))
            {
                self.other = true;
            }
            walk::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                _ if is_dereference(value, self.array) => self.dereferences += 1,
                GoExpression::Identifier(name) if name == self.array => self.other = true,
                _ => walk::expression(self, value),
            }
        }
    }
    let mut count = Count { array, dereferences: 0, other: false };
    count.block(body);
    if count.other { 0 } else { count.dereferences }
}

fn replace_dereferences(body: &mut [GoStatement], array: &str, elements: &str) {
    for statement in body {
        walk::each_expression_in_statement(statement, |expression| {
            if is_dereference(expression, array) {
                *expression = GoExpression::Identifier(elements.to_string());
            }
        });
    }
}

fn is_dereference(value: &GoExpression, array: &str) -> bool {
    matches!(value, GoExpression::Unary { operator: "*", operand }
        if matches!(&**operand, GoExpression::Identifier(name) if name == array))
}

fn deref(value: GoExpression) -> GoExpression {
    GoExpression::Unary { operator: "*", operand: Box::new(value) }
}

fn fresh(base: &str, names: &mut FxHashSet<String>) -> String {
    let mut candidate = format!("{base}{NUMBERED}");
    let mut counter = 2;
    while names.contains(&candidate) {
        candidate = format!("{base}{NUMBERED}{counter}");
        counter += 1;
    }
    names.insert(candidate.clone());
    candidate
}
