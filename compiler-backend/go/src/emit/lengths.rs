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

use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType, Name, statements_names};

use super::ranges::{each_expression, each_expression_in_statement};

pub fn count_lengths_up_to_comparisons(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        match declaration {
            GoDeclaration::Function { body, .. } => block(body),
            GoDeclaration::Variable { value, .. } => expression(value),
            _ => {}
        }
    }
}

/// Rewrites a block, and every block and expression inside it, once each.
fn block(body: &mut [GoStatement]) {
    for statement in body.iter_mut() {
        statement_parts(statement);
    }
    switched_lengths(body);
}

fn expression(value: &mut GoExpression) {
    match value {
        GoExpression::Function { body, .. } => block(body),
        GoExpression::Call { function, arguments } => {
            expression(function);
            arguments.iter_mut().for_each(expression);
        }
        GoExpression::Binary { left, right, .. } => {
            expression(left);
            expression(right);
        }
        GoExpression::Index { value, index } => {
            expression(value);
            expression(index);
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. }
        | GoExpression::TypeAssertion { value, .. }
        | GoExpression::Spread(value)
        | GoExpression::Instantiation { function: value, .. } => expression(value),
        GoExpression::Composite { fields, .. } => {
            fields.iter_mut().for_each(|(_, value)| expression(value))
        }
        _ => {}
    }
    counted_code_points(value);
    compared_length(value);
}

fn statement_parts(statement: &mut GoStatement) {
    match statement {
        GoStatement::Define { values, .. } => values.iter_mut().for_each(expression),
        GoStatement::Variable { value: Some(value), .. }
        | GoStatement::Return(Some(value))
        | GoStatement::Expression(value)
        | GoStatement::Defer(value) => expression(value),
        GoStatement::Assign { targets, values } => {
            targets.iter_mut().for_each(expression);
            values.iter_mut().for_each(expression);
        }
        GoStatement::If { condition, then, otherwise } => {
            expression(condition);
            block(then);
            block(otherwise);
        }
        GoStatement::Switch { value, cases, default } => {
            if let Some(value) = value {
                expression(value);
                if let Some(largest) = largest_literal(cases.iter().flat_map(|case| &case.values)) {
                    cap(value, largest);
                }
            }
            for case in cases {
                case.values.iter_mut().for_each(expression);
                block(&mut case.body);
            }
            if let Some(default) = default {
                default.covers.iter_mut().for_each(expression);
                block(&mut default.body);
            }
        }
        GoStatement::IfAssert { value, then, .. } => {
            expression(value);
            block(then);
        }
        GoStatement::Range { iterable, body, .. } => {
            expression(iterable);
            block(body);
        }
        GoStatement::Counting { start, end, body, .. } => {
            expression(start);
            expression(end);
            block(body);
        }
        GoStatement::CountingDown { start, body, .. } => {
            expression(start);
            block(body);
        }
        GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. }
        | GoStatement::Block(body) => block(body),
        _ => {}
    }
}

/// `len(direct.ToCodePointArray(nil, nil, s))`, the code point length as
/// `Data.String.CodePoints.length` defines it, counts the code points without
/// building the array.
fn counted_code_points(value: &mut GoExpression) {
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
    *value = GoExpression::Call {
        function: Box::new(GoExpression::Qualified {
            package: "direct".into(),
            name: "CodePointLength".into(),
        }),
        arguments: vec![string],
    };
}

/// `length(s) op literal` or `literal op length(s)`, length possibly
/// converted to `int32`.
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
            each_expression_in_statement(statement, &mut |e| {
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

/// Turns a length, possibly under an `int32` conversion, into its count up to
/// `literal + 1`.
fn cap(length: &mut GoExpression, literal: i64) {
    let call = match length {
        GoExpression::Conversion { type_: GoType::Named(name), value } if name == "int32" => {
            &mut **value
        }
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

/// Counts, once before each loop, the lengths of strings the loop never
/// changes. `taken` tells which names a new local must not shadow.
pub fn hoist_loop_invariant_lengths(
    declarations: &mut [GoDeclaration],
    taken: &dyn Fn(&str) -> bool,
) {
    for declaration in declarations {
        let mut names = FxHashSet::default();
        declaration.for_each_name_mut(&mut |name| {
            let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
            names.insert(name.clone());
        });
        let written_by_literals = written_by_literals(declaration);
        let mut function = Function { names, written_by_literals, taken };
        match declaration {
            GoDeclaration::Function { body, .. } => function.body(body),
            GoDeclaration::Variable { value, .. } => function.literals(value),
            _ => {}
        }
    }
}

struct Function<'a> {
    /// Every name the declaration uses, so that a hoisted length shadows none.
    names: FxHashSet<String>,
    /// The variables that a function literal writes, which a loop calling it
    /// changes without writing them itself.
    written_by_literals: FxHashSet<String>,
    taken: &'a dyn Fn(&str) -> bool,
}

impl Function<'_> {
    fn body(&mut self, body: &mut Vec<GoStatement>) {
        self.loops(body);
        for statement in body.iter_mut() {
            each_expression_in_statement(statement, &mut |value| self.literal(value));
        }
    }

    fn literals(&mut self, value: &mut GoExpression) {
        each_expression(value, &mut |value| self.literal(value));
    }

    fn literal(&mut self, value: &mut GoExpression) {
        if let GoExpression::Function { body, .. } = value {
            self.loops(body);
        }
    }

    /// The loops in a block, outside function literals, outermost first.
    fn loops(&mut self, body: &mut Vec<GoStatement>) {
        let mut at = 0;
        while at < body.len() {
            let lengths = match &mut body[at] {
                GoStatement::Loop(looped) | GoStatement::LabeledLoop { body: looped, .. } => {
                    self.invariant_lengths(looped)
                }
                _ => vec![],
            };
            let hoisted = lengths.len();
            for (local, length) in lengths.into_iter().rev() {
                body.insert(at, GoStatement::Define { names: vec![local], values: vec![length] });
            }
            at += hoisted;
            match &mut body[at] {
                GoStatement::If { then, otherwise, .. } => {
                    self.loops(then);
                    self.loops(otherwise);
                }
                GoStatement::Switch { cases, default, .. } => {
                    for case in cases {
                        self.loops(&mut case.body);
                    }
                    if let Some(default) = default {
                        self.loops(&mut default.body);
                    }
                }
                GoStatement::IfAssert { then: body, .. }
                | GoStatement::Range { body, .. }
                | GoStatement::Counting { body, .. }
                | GoStatement::CountingDown { body, .. }
                | GoStatement::Loop(body)
                | GoStatement::LabeledLoop { body, .. }
                | GoStatement::Block(body) => self.loops(body),
                _ => {}
            }
            at += 1;
        }
    }

    /// Replaces each length of a string the loop never changes with a new
    /// local, and returns the locals with the lengths they hold.
    fn invariant_lengths(&mut self, looped: &mut [GoStatement]) -> Vec<(String, GoExpression)> {
        let mut changed = self.written_by_literals.clone();
        statements_names(looped, &mut |name| {
            if let Name::Written(name) | Name::Binder(name) = name {
                changed.insert(name.clone());
            }
        });
        let mut hoisted: Vec<(String, GoExpression)> = vec![];
        let mut locals: Vec<((&'static str, String), String)> = vec![];
        for statement in looped.iter_mut() {
            each_expression_in_statement(statement, &mut |value| {
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

    fn fresh(&mut self, base: String) -> String {
        let mut candidate = base.clone();
        let mut counter = 2;
        while self.names.contains(&candidate) || (self.taken)(&candidate) {
            candidate = format!("{base}{counter}");
            counter += 1;
        }
        self.names.insert(candidate.clone());
        candidate
    }
}

/// The variables written inside the declaration's function literals.
fn written_by_literals(declaration: &mut GoDeclaration) -> FxHashSet<String> {
    let mut written = FxHashSet::default();
    let mut literal = |value: &mut GoExpression| {
        let GoExpression::Function { body, .. } = value else { return };
        statements_names(body, &mut |name| {
            if let Name::Written(name) = name {
                written.insert(name.clone());
            }
        });
    };
    match declaration {
        GoDeclaration::Function { body, .. } => {
            for statement in body.iter_mut() {
                each_expression_in_statement(statement, &mut literal);
            }
        }
        GoDeclaration::Variable { value, .. } => each_expression(value, &mut literal),
        _ => {}
    }
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
