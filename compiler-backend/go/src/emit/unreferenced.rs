//! Drops the definitions that emission left without a reference.
//!
//! A local is defined when the program reads it, but a read whose result is Unit emits as
//! `struct{}{}` without the value it was read from, and the code after a diverging statement is
//! cut. A record or loop element whose every read was such a field, or a local read only after a
//! `panic`, is then defined and never used, which Go rejects. A definition whose value has no
//! effect and cannot fail is dropped; one whose value is a call keeps the call.

use rustc_hash::FxHashSet;

use super::discarded;
use crate::go_traversal::{self, Walk, each_block_in_declaration};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

pub(super) fn drop_unreferenced_definitions(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        // Dropping a definition can leave the definitions its value read without a reference.
        while drop_unreferenced(declaration) {}
    }
}

fn drop_unreferenced(declaration: &mut GoDeclaration) -> bool {
    let read = read_names(declaration);
    let unread = |name: &String| name != "_" && !read.contains(name);
    let unread_target =
        |target: &GoExpression| matches!(target, GoExpression::Identifier(name) if unread(name));
    let mut dropped = false;
    each_block_in_declaration(declaration, |block| {
        for statement in std::mem::take(block) {
            match statement {
                // `_, _ :=` defines nothing, which Go rejects.
                GoStatement::Define { names, values }
                    if names.iter().all(|name| name == "_" || unread(name)) =>
                {
                    values.into_iter().for_each(|value| effects(value, block));
                    dropped = true;
                }
                GoStatement::Define { mut names, values } if names.iter().any(unread) => {
                    for name in names.iter_mut().filter(|name| unread(name)) {
                        *name = "_".into();
                    }
                    block.push(GoStatement::Define { names, values });
                    dropped = true;
                }
                GoStatement::Variable { name, value, .. } if unread(&name) => {
                    value.into_iter().for_each(|value| effects(value, block));
                    dropped = true;
                }
                GoStatement::Assign { targets, values } if targets.iter().all(unread_target) => {
                    values.into_iter().for_each(|value| effects(value, block));
                    dropped = true;
                }
                GoStatement::Assign { mut targets, values }
                    if targets.iter().any(unread_target) =>
                {
                    for target in targets.iter_mut().filter(|target| unread_target(target)) {
                        *target = GoExpression::Identifier("_".into());
                    }
                    block.push(GoStatement::Assign { targets, values });
                    dropped = true;
                }
                GoStatement::Range { index, element, iterable, body }
                    if index.as_ref().is_some_and(unread) || unread(&element) =>
                {
                    let index = index.filter(|index| !unread(index));
                    let element = if unread(&element) { "_".into() } else { element };
                    block.push(GoStatement::Range { index, element, iterable, body });
                    dropped = true;
                }
                GoStatement::IfAssert { name, value, type_, then } if unread(&name) => {
                    block.push(GoStatement::IfAssert { name: "_".into(), value, type_, then });
                    dropped = true;
                }
                GoStatement::If { condition, then, otherwise }
                    if then.is_empty() && otherwise.is_empty() && is_inert(&condition) =>
                {
                    dropped = true;
                }
                GoStatement::Switch { value, cases, default }
                    if value.as_ref().is_none_or(is_inert)
                        && cases.iter().all(|case| {
                            case.body.is_empty() && case.values.iter().all(is_inert)
                        })
                        && default.as_ref().is_none_or(|default| default.body.is_empty()) =>
                {
                    dropped = true;
                }
                statement => block.push(statement),
            }
        }
    });
    dropped
}

fn read_names(declaration: &mut GoDeclaration) -> FxHashSet<String> {
    struct Reads(FxHashSet<String>);

    impl Walk for Reads {
        fn statement(&mut self, statement: &mut GoStatement) {
            if let GoStatement::Assign { targets, values } = statement {
                for target in targets.iter_mut() {
                    if !matches!(target, GoExpression::Identifier(_)) {
                        self.expression(target);
                    }
                }
                values.iter_mut().for_each(|value| self.expression(value));
                return;
            }
            go_traversal::statement(self, statement);
        }

        fn expression(&mut self, expression: &mut GoExpression) {
            if let GoExpression::Identifier(name) = expression {
                self.0.insert(name.clone());
            }
            go_traversal::expression(self, expression);
        }
    }

    let mut reads = Reads(FxHashSet::default());
    go_traversal::declaration(&mut reads, declaration);
    reads.0
}

fn effects(value: GoExpression, out: &mut Vec<GoStatement>) {
    match value {
        GoExpression::Call { function, arguments } if is_value_only_builtin(&function) => {
            arguments.into_iter().for_each(|argument| effects(argument, out));
        }
        call @ GoExpression::Call { .. } => out.push(discarded(call)),
        GoExpression::Conversion { value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Unary { operand: value, .. }
        | GoExpression::TypeAssertion { value, .. }
        | GoExpression::Spread(value)
        | GoExpression::Instantiation { function: value, .. }
        | GoExpression::Attributed { value, .. } => effects(*value, out),
        GoExpression::Composite { fields, .. } => {
            fields.into_iter().for_each(|(_, field)| effects(field, out));
        }
        GoExpression::Binary { left, right, .. } => {
            effects(*left, out);
            effects(*right, out);
        }
        GoExpression::Index { value, index } => {
            effects(*value, out);
            effects(*index, out);
        }
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Utf16(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_)
        | GoExpression::Function { .. }
        | GoExpression::Type(_) => {}
    }
}

fn is_value_only_builtin(function: &GoExpression) -> bool {
    matches!(
        function,
        GoExpression::Identifier(name) if matches!(name.as_str(), "append" | "len" | "make" | "new")
    )
}

/// Whether evaluating the value has no effect and cannot panic.
fn is_inert(value: &GoExpression) -> bool {
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
        GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. }
        | GoExpression::Attributed { value, .. } => is_inert(value),
        GoExpression::Composite { fields, .. } => fields.iter().all(|(_, value)| is_inert(value)),
        // Integer division by zero panics, and so does dereferencing nil.
        GoExpression::Binary { operator, left, right } => {
            !matches!(*operator, "/" | "%") && is_inert(left) && is_inert(right)
        }
        GoExpression::Unary { operator, operand } => *operator != "*" && is_inert(operand),
        GoExpression::Call { .. }
        | GoExpression::Index { .. }
        | GoExpression::TypeAssertion { .. }
        | GoExpression::Type(_)
        | GoExpression::Spread(_)
        | GoExpression::Instantiation { .. } => false,
    }
}
