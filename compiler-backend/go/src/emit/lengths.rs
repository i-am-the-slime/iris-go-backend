//! String lengths that are only compared with small integers.
//!
//! A JavaScript string knows its length; a Go string has to be walked to count
//! its UTF-16 code units. `Data.String.CodePoints.uncons` asks for the length
//! only to tell 0, 1 and more apart, so a parser that unconses its input
//! character by character would walk the rest of the input at every step.
//! Where a length is only compared with integer literals, counting up to one
//! past the largest of them gives every comparison the same answer, and
//! `prim.CodeUnitLengthUpTo` stops there.

use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

use super::ranges::each_expression_in_statement;

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
fn block(body: &mut Vec<GoStatement>) {
    switched_lengths(body);
    for statement in body.iter_mut() {
        statement_parts(statement);
    }
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
        | GoExpression::Spread(value) => expression(value),
        GoExpression::Composite { fields, .. } => {
            fields.iter_mut().for_each(|(_, value)| expression(value))
        }
        _ => {}
    }
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

/// `scrutinee := length(s)` directly followed by `switch scrutinee` over
/// integer literals, with `scrutinee` used nowhere else.
fn switched_lengths(body: &mut [GoStatement]) {
    for at in 0..body.len().saturating_sub(1) {
        let (head, rest) = body.split_at_mut(at + 1);
        let GoStatement::Define { names, values } = &mut head[at] else { continue };
        let [name] = names.as_slice() else { continue };
        let GoStatement::Switch { value: Some(GoExpression::Identifier(switched)), cases, .. } =
            &rest[0]
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

/// Turns `prim.CodeUnitLength(s)`, possibly under an `int32` conversion, into
/// `prim.CodeUnitLengthUpTo(literal + 1, s)`.
fn cap(length: &mut GoExpression, literal: i64) {
    let call = match length {
        GoExpression::Conversion { type_: GoType::Named(name), value } if name == "int32" => {
            &mut **value
        }
        call => call,
    };
    let GoExpression::Call { function, arguments } = call else { return };
    let GoExpression::Qualified { package, name } = &mut **function else { return };
    if package != "prim" || name != "CodeUnitLength" || arguments.len() != 1 || literal < 0 {
        return;
    }
    *name = "CodeUnitLengthUpTo".into();
    arguments.insert(0, GoExpression::Integer(literal + 1));
}
