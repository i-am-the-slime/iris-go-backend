//! Functions that count the set bits of an Int, recognised as Go's `bits.OnesCount`.
//!
//! PureScript has no population count, so programs write it bit by bit:
//!
//! ```purescript
//! populationCount 0 = 0
//! populationCount n = (n .&. 1) + populationCount (n `zshr` 1)
//! ```
//!
//! or clear the lowest set bit at each step, `1 + populationCount (n .&. (n - 1))`. Either
//! counts the ones of the Int's two's complement bits at whatever width it has, which is what
//! `bits.OnesCount(uint(n))` does in one instruction, so the function becomes that call.

use crate::foreign::{Comparison, Foreign, Operator};
use crate::monomorphic::{
    Alternative, Expression, ExpressionKind, Function, FunctionId, Guard, Guarded, Literal,
    LocalId, Pattern, PatternKind,
};
use crate::monotype::{Monotype, Monotypes};

/// The body of a function that counts its Int parameter's set bits, as one population count.
pub(super) fn population_count(
    function: &Function,
    id: FunctionId,
    monotypes: &Monotypes,
) -> Option<Expression> {
    let [parameter] = function.parameters.as_slice() else { return None };
    let is_int = |monotype| matches!(monotypes.get(monotype), Monotype::Int);
    if !is_int(parameter.monotype) || !is_int(function.result) {
        return None;
    }
    let (zero, step, bits) = split_at_zero(&function.body, parameter.id)?;
    if !is_int_literal(zero, 0) || !counts_one_bit(step, bits, id) {
        return None;
    }
    let operator = Foreign::Operator(Operator::IntPopulationCount).interned();
    let arguments = vec![parameter.expression()];
    Some(Expression::new(ExpressionKind::Foreign { foreign: operator, arguments }, function.result))
}

/// What the body gives at zero, what it gives otherwise, and the local that names the
/// parameter there: `case n of 0 -> …; m -> …` or `if n == 0 then … else …`.
fn split_at_zero(
    body: &Expression,
    parameter: LocalId,
) -> Option<(&Expression, &Expression, LocalId)> {
    match &body.kind {
        ExpressionKind::Case { scrutinees, alternatives } => {
            if let Some(split) = guarded_at_zero(alternatives, parameter) {
                return Some(split);
            }
            let [scrutinee] = scrutinees.as_slice() else { return None };
            let [at_zero, otherwise] = alternatives.as_slice() else { return None };
            if !is_local(scrutinee, parameter) {
                return None;
            }
            let [zero_pattern] = at_zero.patterns.as_slice() else { return None };
            if !matches!(zero_pattern.kind, PatternKind::Literal(Literal::Int(0))) {
                return None;
            }
            let [other_pattern] = otherwise.patterns.as_slice() else { return None };
            let bits = match &other_pattern.kind {
                PatternKind::Wildcard => parameter,
                PatternKind::Variable(local) => local.id,
                _ => return None,
            };
            Some((unconditional(at_zero)?, unconditional(otherwise)?, bits))
        }
        ExpressionKind::If { condition, then, otherwise } => {
            is_zero_test(condition, parameter).then_some((then, otherwise, parameter))
        }
        _ => None,
    }
}

/// `n | n == 0 = … | otherwise = …`, a case of guards alone.
fn guarded_at_zero(
    alternatives: &[Alternative],
    parameter: LocalId,
) -> Option<(&Expression, &Expression, LocalId)> {
    let [alternative] = alternatives else { return None };
    let binds_nothing = |pattern: &Pattern| matches!(pattern.kind, PatternKind::Wildcard);
    let Guarded::Guards(branches) = &alternative.body else { return None };
    let [at_zero, otherwise] = branches.as_slice() else { return None };
    let [Guard::Boolean(condition)] = at_zero.guards.as_slice() else { return None };
    let always = match otherwise.guards.as_slice() {
        [] => true,
        [Guard::Boolean(condition)] => {
            matches!(condition.kind, ExpressionKind::Literal(Literal::Boolean(true)))
        }
        _ => false,
    };
    let decides = alternative.patterns.iter().all(binds_nothing) && always;
    (decides && is_zero_test(condition, parameter)).then_some((
        &at_zero.body,
        &otherwise.body,
        parameter,
    ))
}

/// `n == 0` or `0 == n`.
fn is_zero_test(condition: &Expression, parameter: LocalId) -> bool {
    is_operation(condition, Operator::Compare(Comparison::Equal), |[left, right]| {
        is_local(left, parameter) && is_int_literal(right, 0)
    }) || is_operation(condition, Operator::Compare(Comparison::Equal), |[left, right]| {
        is_int_literal(left, 0) && is_local(right, parameter)
    })
}

/// `(n .&. 1) + count (n zshr 1)` or `1 + count (n .&. (n - 1))`, either way round.
fn counts_one_bit(step: &Expression, bits: LocalId, id: FunctionId) -> bool {
    let Some((Operator::IntAdd, [left, right])) = operation(step) else { return false };
    let counts = |counted: &Expression, rest: &Expression| {
        let Some(argument) = recursive_argument(rest, id) else { return false };
        let masks_lowest_bit = is_operation(counted, Operator::IntAnd, |[value, mask]| {
            is_local(value, bits) && is_int_literal(mask, 1)
        });
        let lowest_bit = masks_lowest_bit
            && is_operation(argument, Operator::IntZeroFillShiftRight, |[value, shift]| {
                is_local(value, bits) && is_int_literal(shift, 1)
            });
        let lowest_cleared = is_int_literal(counted, 1)
            && is_operation(argument, Operator::IntAnd, |[value, below]| {
                let one_less = is_operation(below, Operator::IntSubtract, |[value, one]| {
                    is_local(value, bits) && is_int_literal(one, 1)
                });
                is_local(value, bits) && one_less
            });
        lowest_bit || lowest_cleared
    };
    counts(left, right) || counts(right, left)
}

fn recursive_argument(expression: &Expression, id: FunctionId) -> Option<&Expression> {
    let ExpressionKind::Apply { function, arguments } = &expression.kind else { return None };
    let [argument] = arguments.as_slice() else { return None };
    matches!(function.kind, ExpressionKind::Function(called) if called == id).then_some(argument)
}

fn unconditional(alternative: &Alternative) -> Option<&Expression> {
    match &alternative.body {
        Guarded::Unconditional(body) => Some(body),
        Guarded::Guards(_) => None,
    }
}

fn operation(expression: &Expression) -> Option<(Operator, &[Expression; 2])> {
    let ExpressionKind::Foreign { foreign, arguments } = &expression.kind else { return None };
    let Foreign::Operator(operator) = foreign else { return None };
    Some((*operator, arguments.as_slice().try_into().ok()?))
}

fn is_operation(
    expression: &Expression,
    expected: Operator,
    operands: impl Fn(&[Expression; 2]) -> bool,
) -> bool {
    operation(expression).is_some_and(|(operator, arguments)| {
        operator == expected
            && (operands(arguments) || commutes(operator) && operands(&swapped(arguments)))
    })
}

fn commutes(operator: Operator) -> bool {
    matches!(operator, Operator::IntAnd | Operator::IntAdd)
}

fn swapped(arguments: &[Expression; 2]) -> [Expression; 2] {
    [arguments[1].clone(), arguments[0].clone()]
}

fn is_local(expression: &Expression, local: LocalId) -> bool {
    matches!(expression.kind, ExpressionKind::Local(id) if id == local)
}

fn is_int_literal(expression: &Expression, value: i64) -> bool {
    matches!(expression.kind, ExpressionKind::Literal(Literal::Int(literal)) if literal == value)
}
