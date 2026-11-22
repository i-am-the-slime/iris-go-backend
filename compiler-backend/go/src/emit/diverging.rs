//! Ends each block at its first diverging statement.
//!
//! Emission produces a value for every expression, so a `panic` that stands for one is followed
//! by a zero-valued stand-in and by the code that uses it, which can never run. A `panic`, like
//! a `return`, `break` or `continue`, is a terminating statement in Go, so the block ends there.

use crate::go_traversal::each_block_in_declaration;
use crate::syntax::{GoDeclaration, GoStatement};

pub(super) fn end_blocks_at_divergence(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        each_block_in_declaration(declaration, |block| {
            if let Some(end) = block.iter().position(diverges) {
                block.truncate(end + 1);
            }
        });
    }
}

fn diverges(statement: &GoStatement) -> bool {
    match statement {
        statement if statement.is_panic() => true,
        GoStatement::Return(_)
        | GoStatement::Continue
        | GoStatement::Break
        | GoStatement::BreakTo(_) => true,
        _ => false,
    }
}
