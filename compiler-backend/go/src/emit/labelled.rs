//! A labelled loop that never loops becomes the `if`/`else` it stands for.
//!
//! A case whose alternatives fall through to the next one on a failed test is emitted as
//!
//! ```go
//! matched:
//!     for {
//!         if test { first; break matched }
//!         second
//!         break matched
//!     }
//! ```
//!
//! where every path ends in `break matched`, a `return` or a `panic`. The loop is a block with an
//! early exit, and `if test { first } else { second }` says the same.

use super::statements_reference;
use crate::go_traversal::each_block_in_declaration;
use crate::syntax::{GoDeclaration, GoStatement};

pub(super) fn unlabel_blocks(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if let Some(statements) = unlooped(block, position) {
                    block.splice(position..=position, statements);
                } else {
                    position += 1;
                }
            }
        });
    }
}

/// The statements that replace the labelled loop at `position`, when every path through it
/// leaves it and the names it defines mean nothing else in the block around it.
fn unlooped(block: &mut [GoStatement], position: usize) -> Option<Vec<GoStatement>> {
    let GoStatement::LabeledLoop { label, body } = &block[position] else { return None };
    let statements = closed(body, label)?;
    let defined: Vec<String> = statements.iter().flat_map(defined_names).collect();
    let (before, rest) = block.split_at_mut(position);
    let after = &mut rest[1..];
    let clashes = defined.iter().any(|name| {
        before.iter().chain(after.iter()).any(|statement| defined_names(statement).contains(name))
            || statements_reference(before, name)
            || statements_reference(after, name)
    });
    (!clashes).then_some(statements)
}

/// The block with each exit from the loop turned into the end of the block, when no path through
/// it reaches its end, which would run the loop again.
fn closed(statements: &[GoStatement], label: &str) -> Option<Vec<GoStatement>> {
    let mut out = vec![];
    for (position, statement) in statements.iter().enumerate() {
        match statement {
            GoStatement::BreakTo(target) if target == label => return Some(out),
            GoStatement::Break => return Some(out),
            GoStatement::Continue => return None,
            GoStatement::Return(_) => {
                out.push(statement.clone());
                return Some(out);
            }
            statement if statement.is_panic() => {
                out.push(statement.clone());
                return Some(out);
            }
            GoStatement::If { condition, then, otherwise } if leaves(statement, label) => {
                let rest = &statements[position + 1..];
                let (then, otherwise) = match closed(then, label) {
                    Some(then) => (then, closed(&joined(otherwise, rest), label)?),
                    None => (closed(&joined(then, rest), label)?, closed(otherwise, label)?),
                };
                let condition = condition.clone();
                out.push(GoStatement::If { condition, then, otherwise });
                return Some(out);
            }
            statement if leaves(statement, label) => return None,
            statement => out.push(statement.clone()),
        }
    }
    None
}

/// Whether the statement leaves the labelled loop, or goes back to its start, from inside.
fn leaves(statement: &GoStatement, label: &str) -> bool {
    match statement {
        GoStatement::BreakTo(target) => target == label,
        GoStatement::Break | GoStatement::Continue => true,
        GoStatement::If { then, otherwise, .. } => {
            then.iter().chain(otherwise).any(|statement| leaves(statement, label))
        }
        GoStatement::IfAssert { then, .. } => then.iter().any(|statement| leaves(statement, label)),
        // A `break` in a switch leaves the switch, and a `continue` the loop around it.
        GoStatement::Switch { cases, default, .. } => cases
            .iter()
            .map(|case| &case.body)
            .chain(default.iter().map(|default| &default.body))
            .flatten()
            .any(|statement| match statement {
                GoStatement::Break => false,
                statement => leaves(statement, label),
            }),
        GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. }
        | GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. } => {
            body.iter().any(|statement| breaks_to(statement, label))
        }
        _ => false,
    }
}

/// Whether a `break` to the label is anywhere in the statement.
fn breaks_to(statement: &GoStatement, label: &str) -> bool {
    match statement {
        GoStatement::BreakTo(target) => target == label,
        GoStatement::If { then: body, otherwise: rest, .. } => {
            body.iter().chain(rest).any(|statement| breaks_to(statement, label))
        }
        GoStatement::Switch { cases, default, .. } => cases
            .iter()
            .map(|case| &case.body)
            .chain(default.iter().map(|default| &default.body))
            .flatten()
            .any(|statement| breaks_to(statement, label)),
        GoStatement::IfAssert { then: body, .. }
        | GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. }
        | GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. } => {
            body.iter().any(|statement| breaks_to(statement, label))
        }
        _ => false,
    }
}

fn joined(first: &[GoStatement], second: &[GoStatement]) -> Vec<GoStatement> {
    first.iter().chain(second).cloned().collect()
}

fn defined_names(statement: &GoStatement) -> Vec<String> {
    match statement {
        GoStatement::Define { names, .. } => names.clone(),
        GoStatement::Variable { name, .. } => vec![name.clone()],
        _ => vec![],
    }
}
