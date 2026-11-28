use rustc_hash::FxHashSet;

use crate::naming::{is_vague, lower_first, numbered};
use crate::syntax::{
    GoBinaryOperator, GoBuiltin, GoExpression, GoStatement, GoType, GoUnaryOperator,
};

pub(super) fn unique(base: String, taken: &mut FxHashSet<String>) -> String {
    numbered(&base, |name| !taken.insert(name.to_string()))
}

pub(super) fn call(function: GoExpression, arguments: Vec<GoExpression>) -> GoExpression {
    GoExpression::Call { function: Box::new(function), arguments }
}

pub(super) fn builtin_call(builtin: GoBuiltin, arguments: Vec<GoExpression>) -> GoExpression {
    call(GoExpression::builtin(builtin), arguments)
}

pub(super) fn length(array: GoExpression) -> GoExpression {
    builtin_call(GoBuiltin::Len, vec![array])
}

pub(super) fn identifier_expression(name: &str) -> GoExpression {
    GoExpression::Identifier(name.to_string())
}

/// `value.name`, or the field's own value when `value` is a struct built right there whose other
/// fields cost nothing to leave out: `InvoiceLine{Sku: x.Sku, Cents: q * p}.Cents` is `q * p`.
pub(super) fn field(value: GoExpression, name: &str) -> GoExpression {
    if let GoExpression::Composite { fields, .. } = &value
        && fields.iter().all(|(label, value)| label.is_some() && costs_nothing(value))
        && let Some((_, chosen)) = fields.iter().find(|(label, _)| label.as_deref() == Some(name))
    {
        return chosen.clone();
    }
    GoExpression::Field { value: Box::new(value), name: name.to_string() }
}

/// An expression that can't panic, call anything or allocate where anyone sees it.
fn costs_nothing(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::Binary { operator, left, right } => {
            !operator.may_panic() && costs_nothing(left) && costs_nothing(right)
        }
        GoExpression::Unary { operator, operand } => {
            *operator != GoUnaryOperator::Dereference && costs_nothing(operand)
        }
        GoExpression::Field { value, .. } => is_simple(value),
        GoExpression::Qualified { .. } => true,
        expression => is_simple(expression),
    }
}

pub(super) fn binary(
    operator: GoBinaryOperator,
    left: GoExpression,
    right: GoExpression,
) -> GoExpression {
    GoExpression::Binary { operator, left: Box::new(left), right: Box::new(right) }
}

pub(super) fn negated(operand: GoExpression) -> GoExpression {
    match operand {
        GoExpression::Unary { operator: GoUnaryOperator::Negate, operand } => *operand,
        operand => {
            GoExpression::Unary { operator: GoUnaryOperator::Negate, operand: Box::new(operand) }
        }
    }
}

pub(super) fn unit_value() -> GoExpression {
    GoExpression::Composite { type_: GoType::EmptyStruct, fields: vec![] }
}

pub(super) fn panic_statement(message: &str) -> GoStatement {
    GoStatement::Expression(builtin_call(
        GoBuiltin::Panic,
        vec![GoExpression::String(message.to_string())],
    ))
}

pub(super) fn conjunction(tests: Vec<GoExpression>) -> Option<GoExpression> {
    let mut distinct: Vec<GoExpression> = Vec::with_capacity(tests.len());
    for test in tests {
        if !distinct.contains(&test) {
            distinct.push(test);
        }
    }
    distinct.into_iter().reduce(|left, right| binary(GoBinaryOperator::LogicalAnd, left, right))
}

pub(super) fn is_simple(expression: &GoExpression) -> bool {
    if let GoExpression::Composite { fields, .. } = expression {
        return fields.is_empty();
    }
    matches!(
        expression,
        GoExpression::Identifier(_)
            | GoExpression::Integer(_)
            | GoExpression::Float(_)
            | GoExpression::String(_)
            | GoExpression::Utf16(_)
            | GoExpression::Rune(_)
            | GoExpression::Boolean(_)
    ) || matches!(expression, GoExpression::Field { value, .. } if is_simple(value))
}

pub(super) fn is_effectful_call(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::Call { function, .. } => !function.is_builtin(GoBuiltin::Len),
        GoExpression::Conversion { value, .. } => is_effectful_call(value),
        _ => false,
    }
}

pub(super) fn returning(value: GoExpression, has_result: bool) -> GoStatement {
    if has_result { GoStatement::Return(Some(value)) } else { GoStatement::Expression(value) }
}

pub(super) fn discarded(value: GoExpression) -> GoStatement {
    match value {
        GoExpression::Conversion { value, .. } => discarded(*value),
        value => GoStatement::Expression(value),
    }
}

pub(super) fn scrutinee_name(value: &GoExpression) -> String {
    let named = match value {
        GoExpression::Call { function, .. } => match function.as_ref() {
            GoExpression::Qualified { name, .. } => Some(name),
            _ => None,
        },
        GoExpression::Field { name, .. } => Some(name),
        _ => None,
    };
    match named {
        Some(name) if !is_vague(&lower_first(name)) => lower_first(name),
        _ => "scrutinee".into(),
    }
}

pub(super) fn ends_in_panic(statements: &[GoStatement]) -> bool {
    statements.last().is_some_and(GoStatement::is_panic)
}

pub(super) fn breaks_to(statements: &[GoStatement], label: &str) -> bool {
    statements.iter().any(|statement| match statement {
        GoStatement::BreakTo(target) => target == label,
        GoStatement::If { then, otherwise, .. } => {
            breaks_to(then, label) || breaks_to(otherwise, label)
        }
        GoStatement::Switch { cases, default, .. } => {
            cases.iter().any(|case| breaks_to(&case.body, label))
                || default.as_ref().is_some_and(|default| breaks_to(&default.body, label))
        }
        GoStatement::IfAssert { then, .. } => breaks_to(then, label),
        GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. }
        | GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. } => breaks_to(body, label),
        _ => false,
    })
}

pub(super) fn ends_in_jump(statements: &[GoStatement]) -> bool {
    matches!(statements.last(), Some(GoStatement::Return(_) | GoStatement::Continue))
        || ends_in_panic(statements)
}

/// The type of a `Ref` cell holding values of the given type.
pub(super) fn reference_type(value: GoType) -> GoType {
    GoType::Generic { name: "Ref".into(), arguments: vec![value] }
}
