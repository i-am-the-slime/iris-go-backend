//! A Maybe packed from a found call's two answers only to be tested and unpacked again reads
//! the answers instead:
//!
//! ```go
//! value, found := prim.CodeUnitCharAt(0, word)
//! var first maybe.Char
//! if found { first = maybe.Char(value) } else { first = maybe.NoChar }
//! if first != maybe.NoChar && rune(first) == 'a' { … }
//! ```
//!
//! tests `found && value == 'a'`. Every read of the Maybe must be such a test or unpacking, and
//! nothing may change the two answers after; the Maybe then goes.

use crate::go_traversal::{self, each_block_in_declaration};
use crate::syntax::{
    GoBinaryOperator, GoDeclaration, GoExpression, GoStatement, GoType, GoUnaryOperator,
};

use super::aliases::{mentions, writes};

pub(super) fn read_found_answers(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if !read_answers_at(block, position) {
                    position += 1;
                }
            }
        });
    }
}

struct Packed {
    maybe: String,
    value: String,
    found: String,
    nothing: GoExpression,
    unpacked: GoType,
}

fn read_answers_at(block: &mut Vec<GoStatement>, position: usize) -> bool {
    let Some(packed) = packed_at(block, position) else { return false };
    let rest = &mut block[position + 2..];
    let changed = rest.iter_mut().any(|statement| {
        writes(statement, &packed.maybe)
            || writes(statement, &packed.value)
            || writes(statement, &packed.found)
    });
    if changed {
        return false;
    }
    let mut rewritten: Vec<GoStatement> = rest.to_vec();
    for statement in &mut rewritten {
        go_traversal::each_expression_in_statement(statement, |expression| {
            if let Some(read) = answer_read(expression, &packed) {
                *expression = read;
            }
        });
    }
    if rewritten.iter_mut().any(|statement| mentions(statement, &packed.maybe)) {
        return false;
    }
    block.truncate(position);
    block.extend(rewritten);
    true
}

/// `var maybe T` followed by `if found { maybe = T(value) } else { maybe = nothing }`.
fn packed_at(block: &[GoStatement], position: usize) -> Option<Packed> {
    let GoStatement::Variable { name: maybe, value: None, .. } = block.get(position)? else {
        return None;
    };
    let GoStatement::If { condition: GoExpression::Identifier(found), then, otherwise } =
        block.get(position + 1)?
    else {
        return None;
    };
    let ([then], [otherwise]) = (then.as_slice(), otherwise.as_slice()) else { return None };
    let packing = assigned(then, maybe)?;
    let nothing = assigned(otherwise, maybe)?;
    let GoExpression::Conversion { value, .. } = packing else { return None };
    let GoExpression::Identifier(value) = value.as_ref() else { return None };
    if !matches!(nothing, GoExpression::Qualified { .. } | GoExpression::Identifier(_)) {
        return None;
    }
    Some(Packed {
        maybe: maybe.clone(),
        value: value.clone(),
        found: found.clone(),
        nothing: nothing.clone(),
        unpacked: GoType::Rune,
    })
}

fn assigned<'s>(statement: &'s GoStatement, target: &str) -> Option<&'s GoExpression> {
    let GoStatement::Assign { targets, values } = statement else { return None };
    match (targets.as_slice(), values.as_slice()) {
        ([GoExpression::Identifier(name)], [value]) if name == target => Some(value),
        _ => None,
    }
}

/// `found` for `maybe != nothing`, `!found` for `maybe == nothing`, and `value` for
/// `rune(maybe)`.
fn answer_read(expression: &GoExpression, packed: &Packed) -> Option<GoExpression> {
    let is_maybe = |value: &GoExpression| matches!(value, GoExpression::Identifier(name) if *name == packed.maybe);
    match expression {
        GoExpression::Binary { operator, left, right }
            if operator.is_equality() && is_maybe(left) && **right == packed.nothing =>
        {
            let found = GoExpression::Identifier(packed.found.clone());
            Some(match *operator {
                GoBinaryOperator::NotEqual => found,
                _ => {
                    GoExpression::Unary { operator: GoUnaryOperator::Not, operand: Box::new(found) }
                }
            })
        }
        GoExpression::Conversion { type_, value }
            if *type_ == packed.unpacked && is_maybe(value) =>
        {
            Some(GoExpression::Identifier(packed.value.clone()))
        }
        _ => None,
    }
}
