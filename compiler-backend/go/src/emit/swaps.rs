//! Two peeks of a mutable array, both found, poked back crosswise at the same indices are a
//! swap:
//!
//! ```go
//! if i < len(a) && j >= 0 && j < len(a) {
//!     a[i], a[j] = a[j], a[i]
//! }
//! ```
//!
//! rather than two optional values built, tested and taken apart again.

use crate::go_traversal;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

use super::aliases::mentions;

pub(super) fn swap_crosswise_pokes(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                let code: Vec<usize> = (position..block.len())
                    .filter(|index| !matches!(block[*index], GoStatement::Line(_)))
                    .take(5)
                    .collect();
                let swap = match code.as_slice() {
                    [first, .., last] if code.len() == 5 && *first == position => {
                        swap_at(block, &code, *last + 1)
                    }
                    _ => None,
                };
                match swap {
                    Some(swap) => {
                        block.splice(position..=code[4], [swap]);
                    }
                    None => position += 1,
                }
            }
        });
    }
}

/// The swap the five statements at `code` amount to: two peeks into variables, and a test of
/// both found whose only statements poke each back where the other was read.
fn swap_at(block: &mut [GoStatement], code: &[usize], end: usize) -> Option<GoStatement> {
    let first = peek(&block[code[0]], &block[code[1]])?;
    let second = peek(&block[code[2]], &block[code[3]])?;
    let GoStatement::If { condition: found, then, otherwise } = &block[code[4]] else {
        return None;
    };
    if !otherwise.is_empty() || !tests_both_found(found.unattributed(), &first, &second) {
        return None;
    }
    let pokes = without_lines(then);
    let [poke_first, poke_second] = pokes.as_slice() else { return None };
    let first_place = poke(poke_first, &first, &second.name)?;
    let second_place = poke(poke_second, &second, &first.name)?;
    let rest = &mut block[end..];
    if rest
        .iter_mut()
        .any(|statement| mentions(statement, &first.name) || mentions(statement, &second.name))
    {
        return None;
    }
    let condition = GoExpression::Binary {
        operator: "&&",
        left: Box::new(first.in_bounds),
        right: Box::new(second.in_bounds),
    };
    let swapped = GoStatement::Assign {
        targets: vec![first_place.clone(), second_place.clone()],
        values: vec![second_place, first_place],
    };
    Some(GoStatement::If { condition, then: vec![swapped], otherwise: vec![] })
}

struct Peek {
    name: String,
    in_bounds: GoExpression,
    found: GoExpression,
    nothing: GoExpression,
}

/// `var name T; if inBounds { name = found } else { name = nothing }`.
fn peek(declared: &GoStatement, chosen: &GoStatement) -> Option<Peek> {
    let GoStatement::Variable { name, value: None, .. } = declared else { return None };
    let GoStatement::If { condition, then, otherwise } = chosen else { return None };
    let found = assigned(then, name)?;
    let nothing = assigned(otherwise, name)?;
    let in_bounds = condition.unattributed().clone();
    Some(Peek { name: name.clone(), in_bounds, found, nothing })
}

fn without_lines(body: &[GoStatement]) -> Vec<&GoStatement> {
    body.iter().filter(|statement| !matches!(statement, GoStatement::Line(_))).collect()
}

fn assigned(body: &[GoStatement], name: &str) -> Option<GoExpression> {
    let code = without_lines(body);
    let [GoStatement::Assign { targets, values }] = code.as_slice() else { return None };
    let ([GoExpression::Identifier(target)], [value]) = (targets.as_slice(), values.as_slice())
    else {
        return None;
    };
    (target == name).then(|| value.unattributed().clone())
}

fn tests_both_found(condition: &GoExpression, first: &Peek, second: &Peek) -> bool {
    let GoExpression::Binary { operator: "&&", left, right } = condition else { return false };
    is_found(left, first) && is_found(right, second)
}

fn is_found(condition: &GoExpression, peek: &Peek) -> bool {
    let GoExpression::Binary { operator: "!=", left, right } = condition else { return false };
    matches!(&**left, GoExpression::Identifier(name) if *name == peek.name)
        && **right == peek.nothing
}

/// The place `if inBounds { place = value }` pokes, when its bounds are the peek's, `place` is
/// what the peek read and `value` takes apart only the other peek.
fn poke(statement: &GoStatement, peek: &Peek, other: &str) -> Option<GoExpression> {
    let GoStatement::If { condition, then, otherwise } = statement else { return None };
    if *condition.unattributed() != peek.in_bounds || !otherwise.is_empty() {
        return None;
    }
    let code = without_lines(then);
    let [GoStatement::Assign { targets, values }] = code.as_slice() else { return None };
    let ([place @ GoExpression::Index { .. }], [value]) = (targets.as_slice(), values.as_slice())
    else {
        return None;
    };
    if !contains(&peek.found, place) || !unwraps(value, other) {
        return None;
    }
    Some(place.clone())
}

fn contains(expression: &GoExpression, part: &GoExpression) -> bool {
    let mut found = false;
    let mut statement = GoStatement::Expression(expression.clone());
    go_traversal::each_expression_in_statement(&mut statement, |inner| found |= inner == part);
    found
}

fn unwraps(value: &GoExpression, name: &str) -> bool {
    match value {
        GoExpression::Identifier(read) => read == name,
        GoExpression::Conversion { value, .. } | GoExpression::Field { value, .. } => {
            unwraps(value, name)
        }
        GoExpression::Attributed { value, .. } => unwraps(value, name),
        _ => false,
    }
}
