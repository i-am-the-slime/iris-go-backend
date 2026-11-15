//! Drops the definitions that emission left without a reference.
//!
//! A local is defined when the program reads it, but a read whose result is Unit emits as
//! `struct{}{}` without the value it was read from. A record or loop element whose every read
//! was such a field is then defined and never used, which Go rejects. A definition is dropped
//! only when its value has no effect and cannot fail, so the program does what it did before.

use rustc_hash::FxHashSet;

use crate::syntax::{GoDeclaration, GoExpression, GoStatement, Name, statements_names};

pub(super) fn drop_unreferenced_definitions(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let GoDeclaration::Function { body, .. } = declaration else { continue };
        // Dropping a definition can leave the definitions its value read without a reference.
        while drop_unreferenced(body) {}
    }
}

fn drop_unreferenced(body: &mut Vec<GoStatement>) -> bool {
    let referenced = referenced_names(body);
    let mut dropped = false;
    each_block(body, &mut |block| {
        block.retain(|statement| {
            let unreferenced = matches!(statement, GoStatement::Define { names, values }
                if matches!(names.as_slice(), [name] if !referenced.contains(name))
                    && matches!(values.as_slice(), [value] if is_inert(value)));
            dropped |= unreferenced;
            !unreferenced
        });
        for statement in block.iter_mut() {
            if let GoStatement::Range { element, .. } = statement
                && element != "_"
                && !referenced.contains(element)
            {
                *element = "_".into();
                dropped = true;
            }
        }
    });
    dropped
}

/// Every name the statements read or write; a write counts, since Go accepts a local that is
/// only written through a field or an index.
fn referenced_names(body: &mut [GoStatement]) -> FxHashSet<String> {
    let mut referenced = FxHashSet::default();
    statements_names(body, &mut |name| {
        if let Name::Reference(name) | Name::Written(name) = name {
            referenced.insert(name.clone());
        }
    });
    referenced
}

/// Whether evaluating the value has no effect and cannot panic.
fn is_inert(value: &GoExpression) -> bool {
    match value {
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_)
        | GoExpression::Function { .. } => true,
        GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. } => is_inert(value),
        GoExpression::Composite { fields, .. } => fields.iter().all(|(_, value)| is_inert(value)),
        GoExpression::Call { .. }
        | GoExpression::Binary { .. }
        | GoExpression::Unary { .. }
        | GoExpression::Index { .. }
        | GoExpression::TypeAssertion { .. }
        | GoExpression::Type(_)
        | GoExpression::Spread(_)
        | GoExpression::Instantiation { .. } => false,
    }
}

/// Visits a block and every block nested in it, in function literals too.
fn each_block(block: &mut Vec<GoStatement>, visit: &mut dyn FnMut(&mut Vec<GoStatement>)) {
    visit(block);
    for statement in block.iter_mut() {
        statement_blocks(statement, visit);
    }
}

fn statement_blocks(statement: &mut GoStatement, visit: &mut dyn FnMut(&mut Vec<GoStatement>)) {
    match statement {
        GoStatement::Define { values, .. } => {
            values.iter_mut().for_each(|value| expression_blocks(value, visit));
        }
        GoStatement::Variable { value, .. } | GoStatement::Return(value) => {
            if let Some(value) = value {
                expression_blocks(value, visit);
            }
        }
        GoStatement::Assign { targets, values } => {
            targets.iter_mut().chain(values).for_each(|value| expression_blocks(value, visit));
        }
        GoStatement::Expression(value) | GoStatement::Defer(value) => {
            expression_blocks(value, visit);
        }
        GoStatement::If { condition, then, otherwise } => {
            expression_blocks(condition, visit);
            each_block(then, visit);
            each_block(otherwise, visit);
        }
        GoStatement::IfAssert { value, then, .. } => {
            expression_blocks(value, visit);
            each_block(then, visit);
        }
        GoStatement::Switch { value, cases, default } => {
            if let Some(value) = value {
                expression_blocks(value, visit);
            }
            for case in cases {
                case.values.iter_mut().for_each(|value| expression_blocks(value, visit));
                each_block(&mut case.body, visit);
            }
            if let Some(default) = default {
                default.covers.iter_mut().for_each(|value| expression_blocks(value, visit));
                each_block(&mut default.body, visit);
            }
        }
        GoStatement::Range { iterable: start, body, .. }
        | GoStatement::CountingDown { start, body, .. } => {
            expression_blocks(start, visit);
            each_block(body, visit);
        }
        GoStatement::Counting { start, end, body, .. } => {
            expression_blocks(start, visit);
            expression_blocks(end, visit);
            each_block(body, visit);
        }
        GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. }
        | GoStatement::Block(body) => each_block(body, visit),
        GoStatement::Continue | GoStatement::Break | GoStatement::BreakTo(_) => {}
    }
}

fn expression_blocks(expression: &mut GoExpression, visit: &mut dyn FnMut(&mut Vec<GoStatement>)) {
    match expression {
        GoExpression::Function { body, .. } => each_block(body, visit),
        GoExpression::Call { function, arguments } => {
            expression_blocks(function, visit);
            arguments.iter_mut().for_each(|argument| expression_blocks(argument, visit));
        }
        GoExpression::Binary { left, right, .. }
        | GoExpression::Index { value: left, index: right } => {
            expression_blocks(left, visit);
            expression_blocks(right, visit);
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. }
        | GoExpression::TypeAssertion { value, .. }
        | GoExpression::Spread(value)
        | GoExpression::Instantiation { function: value, .. } => expression_blocks(value, visit),
        GoExpression::Composite { fields, .. } => {
            fields.iter_mut().for_each(|(_, value)| expression_blocks(value, visit));
        }
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_)
        | GoExpression::Type(_) => {}
    }
}
