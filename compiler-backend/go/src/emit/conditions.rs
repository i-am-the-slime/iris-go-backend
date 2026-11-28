use crate::go_traversal;
use crate::syntax::{
    GoBinaryOperator, GoDeclaration, GoExpression, GoStatement, GoType, GoUnaryOperator,
};

pub(super) fn assign_conditions(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position + 1 < block.len() {
                if let Some(define) = defined_condition(&block[position], &block[position + 1]) {
                    block.splice(position..position + 2, [define]);
                    test_in_place(block, position);
                }
                position += 1;
            }
        });
    }
}

/// `result := c; if result {` is `if c {` when nothing else reads `result`.
fn test_in_place(block: &mut Vec<GoStatement>, position: usize) {
    let GoStatement::Define { names, .. } = &block[position] else { return };
    let [name] = names.as_slice() else { return };
    let following = block.get(position + 1);
    let Some(GoStatement::If { condition: GoExpression::Identifier(tested), .. }) = following
    else {
        return;
    };
    if tested != name {
        return;
    }
    let mut rest = block[position + 1..].to_vec();
    if let GoStatement::If { condition, .. } = &mut rest[0] {
        *condition = GoExpression::Boolean(true);
    }
    if super::statements_reference(&mut rest, name) {
        return;
    }
    let GoStatement::Define { mut values, .. } = block.remove(position) else { unreachable!() };
    if let GoStatement::If { condition, .. } = &mut block[position] {
        *condition = values.pop().expect("a condition is defined with one value");
    }
}

fn defined_condition(variable: &GoStatement, chain: &GoStatement) -> Option<GoStatement> {
    let GoStatement::Variable { name, type_: GoType::Bool, value: None } = variable else {
        return None;
    };
    let mut arms = vec![];
    let mut rest = chain;
    let mut value = loop {
        let GoStatement::If { condition, then, otherwise } = rest else { return None };
        if !is_pure(condition) {
            return None;
        }
        let GoExpression::Boolean(literal) = assigned_boolean(name, then)? else { return None };
        arms.push((condition, literal));
        match otherwise.as_slice() {
            [] => break GoExpression::Boolean(false),
            [GoStatement::If { .. }] => rest = &otherwise[0],
            _ => break assigned_boolean(name, otherwise)?,
        }
    };
    for (condition, literal) in arms.into_iter().rev() {
        value = match (literal, value) {
            (true, GoExpression::Boolean(false)) => condition.clone(),
            (false, GoExpression::Boolean(true)) => negated(condition),
            // The test is pure, so a branch that gives what the rest gives can go.
            (true, GoExpression::Boolean(true)) => GoExpression::Boolean(true),
            (false, GoExpression::Boolean(false)) => GoExpression::Boolean(false),
            (true, rest) => chained(GoBinaryOperator::LogicalOr, condition.clone(), rest),
            (false, rest) => chained(GoBinaryOperator::LogicalAnd, negated(condition), rest),
        };
    }
    Some(GoStatement::Define { names: vec![name.clone()], values: vec![value] })
}

fn assigned_boolean(name: &str, block: &[GoStatement]) -> Option<GoExpression> {
    let [GoStatement::Assign { targets, values }] = block else { return None };
    let [GoExpression::Identifier(target)] = targets.as_slice() else { return None };
    let [value] = values.as_slice() else { return None };
    (target == name && is_pure(value)).then(|| value.clone())
}

pub(super) fn is_pure(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Utf16(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_) => true,
        GoExpression::Field { value, .. }
        | GoExpression::Unary { operand: value, .. }
        | GoExpression::Conversion { value, .. } => is_pure(value),
        GoExpression::Binary { left, right, .. } => is_pure(left) && is_pure(right),
        _ => false,
    }
}

pub(super) fn negated(condition: &GoExpression) -> GoExpression {
    match condition {
        GoExpression::Binary { operator: GoBinaryOperator::Equal, left, right } => {
            GoExpression::Binary {
                operator: GoBinaryOperator::NotEqual,
                left: left.clone(),
                right: right.clone(),
            }
        }
        GoExpression::Binary { operator: GoBinaryOperator::NotEqual, left, right } => {
            GoExpression::Binary {
                operator: GoBinaryOperator::Equal,
                left: left.clone(),
                right: right.clone(),
            }
        }
        GoExpression::Unary { operator: GoUnaryOperator::Not, operand } => (**operand).clone(),
        _ => GoExpression::Unary {
            operator: GoUnaryOperator::Not,
            operand: Box::new(condition.clone()),
        },
    }
}

fn chained(operator: GoBinaryOperator, first: GoExpression, rest: GoExpression) -> GoExpression {
    match rest {
        GoExpression::Binary { operator: inner, left, right } if inner == operator => {
            binary(operator, chained(operator, first, *left), *right)
        }
        rest => binary(operator, first, rest),
    }
}

fn binary(operator: GoBinaryOperator, left: GoExpression, right: GoExpression) -> GoExpression {
    GoExpression::Binary { operator, left: Box::new(left), right: Box::new(right) }
}
