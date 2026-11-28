use crate::syntax::{GoBinaryOperator, GoExpression, GoUnaryOperator};

/// A comparison, a combination of comparisons, or a constant.
pub(super) fn is_test(value: &GoExpression) -> bool {
    match value {
        GoExpression::Boolean(_) => true,
        GoExpression::Binary { operator, .. } => {
            matches!(
                *operator,
                GoBinaryOperator::LogicalAnd
                    | GoBinaryOperator::LogicalOr
                    | GoBinaryOperator::LessThan
                    | GoBinaryOperator::LessThanOrEqual
                    | GoBinaryOperator::GreaterThan
                    | GoBinaryOperator::GreaterThanOrEqual
                    | GoBinaryOperator::Equal
                    | GoBinaryOperator::NotEqual
            )
        }
        GoExpression::Unary { operator: GoUnaryOperator::Not, operand } => is_test(operand),
        _ => false,
    }
}

/// The tests the backend emits for an index: conjuncts `i >= 0` and `i < len(xs)`, at least
/// one of them a length's.
pub(super) fn is_bounds_test(test: &GoExpression) -> bool {
    fn is_length(value: &GoExpression) -> bool {
        match value {
            GoExpression::Call { function, arguments } => {
                matches!(&**function, GoExpression::Identifier(name) if name == "len")
                    && arguments.len() == 1
            }
            GoExpression::Conversion { value, .. } => is_length(value),
            _ => false,
        }
    }
    fn conjuncts<'a>(test: &'a GoExpression, into: &mut Vec<&'a GoExpression>) {
        match test {
            GoExpression::Binary { operator: GoBinaryOperator::LogicalAnd, left, right } => {
                conjuncts(left, into);
                conjuncts(right, into);
            }
            test => into.push(test),
        }
    }
    if !matches!(test, GoExpression::Binary { .. }) {
        return false;
    }
    let mut parts = vec![];
    conjuncts(test, &mut parts);
    let below_length = |conjunct: &GoExpression| matches!(conjunct, GoExpression::Binary { operator: GoBinaryOperator::LessThan, right, .. } if is_length(right));
    let natural = |conjunct: &GoExpression| {
        matches!(conjunct, GoExpression::Binary { operator: GoBinaryOperator::GreaterThanOrEqual, right, .. }
            if matches!(**right, GoExpression::Integer(0)))
    };
    parts.iter().any(|part| below_length(part))
        && parts.iter().all(|part| below_length(part) || natural(part))
}

/// Calls `visit` on the expression and everything in it, function literals' bodies aside.
pub(super) fn each_subexpression(value: &GoExpression, visit: &mut impl FnMut(&GoExpression)) {
    visit(value);
    match value {
        GoExpression::Function { .. } => {}
        GoExpression::Call { function, arguments } => {
            each_subexpression(function, visit);
            arguments.iter().for_each(|argument| each_subexpression(argument, visit));
        }
        GoExpression::Binary { left, right, .. }
        | GoExpression::Index { value: left, index: right } => {
            each_subexpression(left, visit);
            each_subexpression(right, visit);
        }
        GoExpression::Unary { operand: inner, .. }
        | GoExpression::Field { value: inner, .. }
        | GoExpression::Address(inner)
        | GoExpression::Conversion { value: inner, .. }
        | GoExpression::TypeAssertion { value: inner, .. }
        | GoExpression::Spread(inner)
        | GoExpression::Instantiation { function: inner, .. }
        | GoExpression::Attributed { value: inner, .. } => each_subexpression(inner, visit),
        GoExpression::Composite { fields, .. } => {
            fields.iter().for_each(|(_, field)| each_subexpression(field, visit))
        }
        GoExpression::Results(values) => {
            values.iter().for_each(|value| each_subexpression(value, visit))
        }
        _ => {}
    }
}
