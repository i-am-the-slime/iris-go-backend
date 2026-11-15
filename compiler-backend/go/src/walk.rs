//! One traversal of the Go AST for every pass that rewrites it.
//!
//! A pass implements [`Walk`] and overrides what it cares about: a hook sees a
//! node, does its own work, and calls [`expression`], [`statement`] or the
//! default `block` to carry on into the node's children, before or after its
//! own work as the pass needs. Function literals are expressions, so a pass
//! that tracks scopes overrides `expression` and handles `Function` itself.

use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

pub trait Walk {
    fn expression(&mut self, value: &mut GoExpression) {
        expression(self, value)
    }

    fn statement(&mut self, statement: &mut GoStatement) {
        self::statement(self, statement)
    }

    /// A list of statements: a function body, a branch or a loop body.
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        body.iter_mut().for_each(|statement| self.statement(statement))
    }
}

/// The declaration's code: a function's body or a variable's value.
pub fn declaration(walk: &mut (impl Walk + ?Sized), declaration: &mut GoDeclaration) {
    match declaration {
        GoDeclaration::Function { body, .. } => walk.block(body),
        GoDeclaration::Variable { value, .. } => walk.expression(value),
        _ => {}
    }
}

/// The children of an expression, in source order.
pub fn expression<W: Walk + ?Sized>(walk: &mut W, value: &mut GoExpression) {
    match value {
        GoExpression::Function { body, .. } => walk.block(body),
        GoExpression::Call { function, arguments } => {
            walk.expression(function);
            arguments.iter_mut().for_each(|argument| walk.expression(argument));
        }
        GoExpression::Binary { left, right, .. } => {
            walk.expression(left);
            walk.expression(right);
        }
        GoExpression::Index { value, index } => {
            walk.expression(value);
            walk.expression(index);
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. }
        | GoExpression::TypeAssertion { value, .. }
        | GoExpression::Spread(value)
        | GoExpression::Instantiation { function: value, .. } => walk.expression(value),
        GoExpression::Composite { fields, .. } => {
            fields.iter_mut().for_each(|(_, field)| walk.expression(field))
        }
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Utf16(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_)
        | GoExpression::Type(_) => {}
    }
}

/// The children of a statement, in source order: expressions and blocks.
pub fn statement<W: Walk + ?Sized>(walk: &mut W, statement: &mut GoStatement) {
    match statement {
        GoStatement::Define { values, .. } => {
            values.iter_mut().for_each(|value| walk.expression(value))
        }
        GoStatement::Variable { value: Some(value), .. }
        | GoStatement::Return(Some(value))
        | GoStatement::Expression(value)
        | GoStatement::Defer(value) => walk.expression(value),
        GoStatement::Assign { targets, values } => {
            targets.iter_mut().chain(values).for_each(|value| walk.expression(value))
        }
        GoStatement::If { condition, then, otherwise } => {
            walk.expression(condition);
            walk.block(then);
            walk.block(otherwise);
        }
        GoStatement::Switch { value, cases, default } => {
            if let Some(value) = value {
                walk.expression(value);
            }
            for case in cases {
                case.values.iter_mut().for_each(|value| walk.expression(value));
                walk.block(&mut case.body);
            }
            if let Some(default) = default {
                default.covers.iter_mut().for_each(|value| walk.expression(value));
                walk.block(&mut default.body);
            }
        }
        GoStatement::IfAssert { value, then: body, .. }
        | GoStatement::Range { iterable: value, body, .. }
        | GoStatement::CountingDown { start: value, body, .. } => {
            walk.expression(value);
            walk.block(body);
        }
        GoStatement::Counting { start, end, body, .. } => {
            walk.expression(start);
            walk.expression(end);
            walk.block(body);
        }
        GoStatement::Loop(body) | GoStatement::LabeledLoop { body, .. } => walk.block(body),
        GoStatement::Variable { value: None, .. }
        | GoStatement::Return(None)
        | GoStatement::Continue
        | GoStatement::Break
        | GoStatement::BreakTo(_) => {}
    }
}

/// Calls `visit` on every expression in a statement and its blocks, children
/// first, function literals' bodies included.
pub fn each_expression_in_statement(
    statement: &mut GoStatement,
    visit: impl FnMut(&mut GoExpression),
) {
    Each(visit).statement(statement)
}

/// [`each_expression_in_statement`] over the code of a declaration.
pub fn each_expression_in_declaration(
    declaration: &mut GoDeclaration,
    visit: impl FnMut(&mut GoExpression),
) {
    self::declaration(&mut Each(visit), declaration)
}

struct Each<F>(F);

impl<F: FnMut(&mut GoExpression)> Walk for Each<F> {
    fn expression(&mut self, value: &mut GoExpression) {
        expression(self, value);
        (self.0)(value);
    }
}

/// Calls `visit` on a block and every block nested in its statements, outer
/// blocks first, outside function literals.
pub fn each_block(body: &mut Vec<GoStatement>, visit: impl FnMut(&mut Vec<GoStatement>)) {
    Blocks(visit).block(body)
}

struct Blocks<F>(F);

impl<F: FnMut(&mut Vec<GoStatement>)> Walk for Blocks<F> {
    fn expression(&mut self, _: &mut GoExpression) {}

    fn block(&mut self, body: &mut Vec<GoStatement>) {
        (self.0)(body);
        body.iter_mut().for_each(|statement| self.statement(statement));
    }
}

/// [`each_block`] over a declaration's body, function literals' bodies included.
pub fn each_block_in_declaration(
    declaration: &mut GoDeclaration,
    visit: impl FnMut(&mut Vec<GoStatement>),
) {
    self::declaration(&mut Nested(visit), declaration)
}

struct Nested<F>(F);

impl<F: FnMut(&mut Vec<GoStatement>)> Walk for Nested<F> {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        (self.0)(body);
        body.iter_mut().for_each(|statement| self.statement(statement));
    }
}
