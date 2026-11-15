//! String lengths, which a Go string has to count.
//!
//! A JavaScript string knows its length; a Go string has to be walked to count
//! its UTF-16 code units or its code points. Two kinds of use make that walk
//! quadratic, and both are rewritten here.
//!
//! `Data.String.CodePoints.uncons` asks for the length only to tell 0, 1 and
//! more apart, so a parser that unconses its input character by character
//! would walk the rest of the input at every step. Where a length is only
//! compared with integer literals, counting up to one past the largest of them
//! gives every comparison the same answer, and `prim.CodeUnitLengthUpTo` and
//! `direct.CodePointLengthUpTo` stop there.
//!
//! A loop that indexes a string until it reaches the string's length asks for
//! the length on every iteration. Where the loop never changes the string,
//! the length is counted once, before the loop.

use rustc_hash::FxHashSet;

use crate::naming::numbered;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType, Name, statements_names};

use crate::walk::{self, Walk, each_expression_in_declaration, each_expression_in_statement};
use super::views::{carried_unchanged, view_invariant_strings};

pub fn count_lengths_up_to_comparisons(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        walk::declaration(&mut Capped, declaration);
    }
}

/// Rewrites a block, and every block and expression inside it, once each.
struct Capped;

impl Walk for Capped {
    fn expression(&mut self, value: &mut GoExpression) {
        walk::expression(self, value);
        counted_code_points(value);
        compared_length(value);
    }

    fn statement(&mut self, statement: &mut GoStatement) {
        walk::statement(self, statement);
        if let GoStatement::Switch { value: Some(value), cases, .. } = statement
            && let Some(largest) = largest_literal(cases.iter().flat_map(|case| &case.values))
        {
            cap(value, largest);
        }
    }

    fn block(&mut self, body: &mut Vec<GoStatement>) {
        body.iter_mut().for_each(|statement| self.statement(statement));
        switched_lengths(body);
    }
}

/// `len(direct.ToCodePointArray(nil, nil, s))`, the code point length as
/// `Data.String.CodePoints.length` defines it, counts the code points without
/// building the array. `direct.CodePointLength` counts them as an `int32`, so
/// the Int the length becomes needs no conversion, and the Go `int` that
/// `len` was needs one.
fn counted_code_points(value: &mut GoExpression) {
    if let GoExpression::Conversion { type_: GoType::Named(name), value: converted } = value
        && name == "int32"
        && let GoExpression::Conversion { type_: GoType::Int, value: counted } = &mut **converted
        && is_code_point_length(counted)
    {
        *value = std::mem::replace(&mut **counted, GoExpression::Integer(0));
        return;
    }
    let GoExpression::Call { function, arguments } = value else { return };
    if !matches!(&**function, GoExpression::Identifier(name) if name == "len") {
        return;
    }
    let [GoExpression::Call { function: converted, arguments: converted_arguments }] =
        arguments.as_mut_slice()
    else {
        return;
    };
    if !matches!(&**converted, GoExpression::Qualified { package, name }
        if package == "direct" && name == "ToCodePointArray")
    {
        return;
    }
    let Some(string) = converted_arguments.pop() else { return };
    let counted = GoExpression::Call {
        function: Box::new(GoExpression::Qualified {
            package: "direct".into(),
            name: "CodePointLength".into(),
        }),
        arguments: vec![string],
    };
    *value = GoExpression::Conversion { type_: GoType::Int, value: Box::new(counted) };
}

fn is_code_point_length(value: &GoExpression) -> bool {
    matches!(value, GoExpression::Call { function, .. }
        if matches!(&**function, GoExpression::Qualified { package, name }
            if package == "direct" && name == "CodePointLength"))
}

/// `length(s) op literal` or `literal op length(s)`, the length possibly
/// under a conversion.
fn compared_length(value: &mut GoExpression) {
    let GoExpression::Binary { operator, left, right } = value else { return };
    if !matches!(*operator, "==" | "!=" | "<" | "<=" | ">" | ">=") {
        return;
    }
    let (length, literal) = match (&**left, &**right) {
        (_, GoExpression::Integer(literal)) => (&mut **left, *literal),
        (GoExpression::Integer(literal), _) => (&mut **right, *literal),
        _ => return,
    };
    cap(length, literal);
}

/// `scrutinee := length(s)` followed, past declarations of the variables the
/// cases assign, by `switch scrutinee` over integer literals, with
/// `scrutinee` used nowhere else.
fn switched_lengths(body: &mut [GoStatement]) {
    for at in 0..body.len().saturating_sub(1) {
        let (head, rest) = body.split_at_mut(at + 1);
        let GoStatement::Define { names, values } = &mut head[at] else { continue };
        let [name] = names.as_slice() else { continue };
        let declared = rest
            .iter()
            .take_while(|statement| matches!(statement, GoStatement::Variable { value: None, .. }))
            .count();
        let Some(GoStatement::Switch {
            value: Some(GoExpression::Identifier(switched)),
            cases,
            ..
        }) = rest.get(declared)
        else {
            continue;
        };
        if switched != name {
            continue;
        }
        let Some(largest) = largest_literal(cases.iter().flat_map(|case| &case.values)) else {
            continue;
        };
        let mut uses = 0;
        for statement in rest.iter_mut() {
            each_expression_in_statement(statement, |e| {
                if matches!(e, GoExpression::Identifier(used) if used == name) {
                    uses += 1;
                }
            });
        }
        if uses == 1 {
            cap(&mut values[0], largest);
        }
    }
}

/// The largest of the values when all of them are integer literals.
fn largest_literal<'a>(values: impl Iterator<Item = &'a GoExpression>) -> Option<i64> {
    let mut largest = None;
    for value in values {
        let GoExpression::Integer(literal) = value else { return None };
        largest = Some(largest.map_or(*literal, |l: i64| l.max(*literal)));
    }
    largest
}

/// Turns a length, possibly under a conversion, into its count up to
/// `literal + 1`.
fn cap(length: &mut GoExpression, literal: i64) {
    let call = match length {
        GoExpression::Conversion { value, .. } => &mut **value,
        call => call,
    };
    let GoExpression::Call { function, arguments } = call else { return };
    let GoExpression::Qualified { package, name } = &mut **function else { return };
    let Some(capped) = counted_up_to(package, name) else { return };
    if arguments.len() != 1 || literal < 0 {
        return;
    }
    *name = capped.into();
    arguments.insert(0, GoExpression::Integer(literal + 1));
}

/// The function that counts what the length function `package.name` counts,
/// stopping at a limit.
fn counted_up_to(package: &str, name: &str) -> Option<&'static str> {
    match (package, name) {
        ("prim", "CodeUnitLength") => Some("CodeUnitLengthUpTo"),
        ("direct", "CodePointLength") => Some("CodePointLengthUpTo"),
        _ => None,
    }
}

/// Views, once before each loop, the strings the loop indexes without
/// changing them, and counts the lengths of strings the loop never changes.
/// `taken` tells which names a new local must not shadow.
pub fn hoist_loop_invariant_lengths(
    declarations: &mut [GoDeclaration],
    taken: &dyn Fn(&str) -> bool,
) {
    for declaration in declarations {
        let mut names = FxHashSet::default();
        let mut locals = FxHashSet::default();
        declaration.for_each_name_mut(&mut |name| {
            if let Name::Binder(name) = &name {
                locals.insert(name.to_string());
            }
            let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
            names.insert(name.clone());
        });
        let written_by_literals = written_by_literals(declaration);
        let mut function = Function { names, locals, written_by_literals, taken };
        function.declaration(declaration);
    }
}

struct Function<'a> {
    /// Every name the declaration uses, so that a hoisted length shadows none.
    names: FxHashSet<String>,
    /// The variables the declaration binds, which no other code can change.
    locals: FxHashSet<String>,
    /// The variables that a function literal writes, which a loop calling it
    /// changes without writing them itself.
    written_by_literals: FxHashSet<String>,
    taken: &'a dyn Fn(&str) -> bool,
}

impl Walk for Function<'_> {
    /// The loops in a block, outside function literals, outermost first.
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        let mut at = 0;
        while at < body.len() {
            let changed = match &body[at] {
                GoStatement::Loop(_)
                | GoStatement::LabeledLoop { .. }
                | GoStatement::Range { .. }
                | GoStatement::Counting { .. }
                | GoStatement::CountingDown { .. } => self.changed(&mut body[at]),
                _ => FxHashSet::default(),
            };
            let lengths = match &mut body[at] {
                GoStatement::Loop(looped) | GoStatement::LabeledLoop { body: looped, .. } => {
                    let mut hoisted = self.views(looped, &changed);
                    hoisted.extend(self.invariant_lengths(looped, &changed));
                    hoisted
                }
                GoStatement::Range { body: looped, .. }
                | GoStatement::Counting { body: looped, .. }
                | GoStatement::CountingDown { body: looped, .. } => self.views(looped, &changed),
                _ => vec![],
            };
            let hoisted = lengths.len();
            for (local, length) in lengths.into_iter().rev() {
                body.insert(at, GoStatement::Define { names: vec![local], values: vec![length] });
            }
            at += hoisted;
            self.statement(&mut body[at]);
            at += 1;
        }
    }

    fn expression(&mut self, _: &mut GoExpression) {}
}

impl Function<'_> {
    /// The loops of the declaration's body and of every function literal in it.
    fn declaration(&mut self, declaration: &mut GoDeclaration) {
        if let GoDeclaration::Function { body, .. } = declaration {
            self.block(body);
        }
        each_expression_in_declaration(declaration, |value| {
            if let GoExpression::Function { body, .. } = value {
                self.block(body);
            }
        });
    }

    /// Replaces each length of a string the loop never changes with a new
    /// local, and returns the locals with the lengths they hold.
    fn invariant_lengths(
        &mut self,
        looped: &mut [GoStatement],
        changed: &FxHashSet<String>,
    ) -> Vec<(String, GoExpression)> {
        let mut hoisted: Vec<(String, GoExpression)> = vec![];
        let mut locals: Vec<((&'static str, String), String)> = vec![];
        for statement in looped.iter_mut() {
            each_expression_in_statement(statement, |value| {
                let Some(counted) = length_of_variable(value) else { return };
                if changed.contains(&counted.1) {
                    return;
                }
                let local = match locals.iter().find(|(length, _)| *length == counted) {
                    Some((_, local)) => local.clone(),
                    None => {
                        let local = self.fresh(format!("{}Length", counted.1));
                        locals.push((counted, local.clone()));
                        hoisted.push((local.clone(), value.clone()));
                        local
                    }
                };
                *value = GoExpression::Identifier(local);
            });
        }
        hoisted
    }

    fn views(
        &mut self,
        looped: &mut Vec<GoStatement>,
        changed: &FxHashSet<String>,
    ) -> Vec<(String, GoExpression)> {
        let locals = std::mem::take(&mut self.locals);
        let views = view_invariant_strings(looped, changed, &locals, &mut |base| self.fresh(base));
        self.locals = locals;
        views
    }

    /// The variables a loop, its binders included, may change.
    fn changed(&self, looped: &mut GoStatement) -> FxHashSet<String> {
        let mut changed = self.written_by_literals.clone();
        let looped = std::slice::from_mut(looped);
        statements_names(looped, &mut |name| {
            if let Name::Written(name) | Name::Binder(name) = name {
                changed.insert(name.clone());
            }
        });
        if let [GoStatement::Loop(body) | GoStatement::LabeledLoop { body, .. }] = looped {
            for carried in carried_unchanged(body, &self.written_by_literals) {
                changed.remove(&carried);
            }
        }
        changed
    }

    fn fresh(&mut self, base: String) -> String {
        let candidate = numbered(&base, |name| self.names.contains(name) || (self.taken)(name));
        self.names.insert(candidate.clone());
        candidate
    }
}

/// The variables written inside the declaration's function literals.
fn written_by_literals(declaration: &mut GoDeclaration) -> FxHashSet<String> {
    let mut written = FxHashSet::default();
    each_expression_in_declaration(declaration, |value| {
        let GoExpression::Function { body, .. } = value else { return };
        statements_names(body, &mut |name| {
            if let Name::Written(name) = name {
                written.insert(name.clone());
            }
        });
    });
    written
}

/// When `value` counts a variable's length in full, the variable and what
/// the count is, named by the function that counts it up to a limit.
fn length_of_variable(value: &GoExpression) -> Option<(&'static str, String)> {
    let GoExpression::Call { function, arguments } = value else { return None };
    let GoExpression::Qualified { package, name } = &**function else { return None };
    let [GoExpression::Identifier(string)] = arguments.as_slice() else { return None };
    Some((counted_up_to(package, name)?, string.clone()))
}
