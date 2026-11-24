//! Branches of an `if` chain that do the same thing become one.
//!
//! Alternatives with the same right-hand side, `if n < 1 then problem else if n > 100 then problem`,
//! and inlined functions that answer the same for several constructors, `Black -> false; Leaf ->
//! false`, leave chains whose neighbouring branches are the same code. Neighbours join under
//! `||`, `if a { x } else if b { x }` is `if a || b { x }`, and a last test whose branch does
//! what the `else` does is dropped when evaluating it has no effect.

use super::conditions::is_pure;
use crate::go_traversal::{self, Walk, each_block_in_declaration};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

pub(super) fn merge_identical_branches(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if let GoStatement::If { .. } = &block[position]
                    && let Some(merged) = merged(&block[position])
                {
                    let length = merged.len();
                    block.splice(position..=position, merged);
                    position += length;
                } else {
                    position += 1;
                }
            }
        });
    }
}

/// The statements that replace an `if` chain whose branches can be merged.
fn merged(chain: &GoStatement) -> Option<Vec<GoStatement>> {
    let mut arms: Vec<(GoExpression, Vec<GoStatement>)> = vec![];
    let mut rest = chain;
    let otherwise = loop {
        let GoStatement::If { condition, then, otherwise } = rest else { unreachable!() };
        arms.push((condition.clone(), then.clone()));
        match otherwise.as_slice() {
            [next @ GoStatement::If { .. }] => rest = next,
            _ => break otherwise.clone(),
        }
    };
    let count = arms.len();
    let mut joined: Vec<(GoExpression, Vec<GoStatement>)> = vec![];
    for (condition, body) in arms {
        match joined.last_mut() {
            Some((previous, previous_body))
                if same_code(previous_body, &body)
                    && !assigns_boolean(&body)
                    && !compare_same_values(previous, &condition) =>
            {
                let left = std::mem::replace(previous, GoExpression::Boolean(false));
                *previous = match left {
                    GoExpression::Boolean(false) => condition,
                    left => GoExpression::Binary {
                        operator: "||",
                        left: Box::new(left),
                        right: Box::new(condition),
                    },
                };
            }
            _ => joined.push((condition, body)),
        }
    }
    while let Some((condition, body)) = joined.last()
        && is_pure(condition)
        && same_code(body, &otherwise)
    {
        joined.pop();
    }
    if joined.len() == count {
        return None;
    }
    let defines = |statement: &GoStatement| {
        matches!(statement, GoStatement::Define { .. } | GoStatement::Variable { .. })
    };
    if joined.is_empty() && otherwise.iter().any(defines) {
        return None;
    }
    let mut statements = otherwise;
    for (condition, then) in joined.into_iter().rev() {
        statements = vec![GoStatement::If { condition, then, otherwise: statements }];
    }
    Some(statements)
}

/// Whether the branch only sets a boolean, which `assign_conditions` makes one condition of.
fn assigns_boolean(body: &[GoStatement]) -> bool {
    matches!(body, [GoStatement::Assign { values, .. }]
        if matches!(values.as_slice(), [GoExpression::Boolean(_)]))
}

/// Whether both conditions compare the same two values, which says more as one comparison.
fn compare_same_values(left: &GoExpression, right: &GoExpression) -> bool {
    let operands = |condition: &GoExpression| match condition {
        GoExpression::Binary { operator: "<" | "<=" | ">" | ">=" | "==" | "!=", left, right } => {
            Some((left.clone(), right.clone()))
        }
        _ => None,
    };
    match (operands(left), operands(right)) {
        (Some((a, b)), Some((c, d))) => (a == c && b == d) || (a == d && b == c),
        _ => false,
    }
}

/// Whether two blocks are the same code apart from the PureScript lines they are attributed to.
fn same_code(left: &[GoStatement], right: &[GoStatement]) -> bool {
    without_lines(left) == without_lines(right)
}

fn without_lines(statements: &[GoStatement]) -> Vec<GoStatement> {
    struct Strip;
    impl Walk for Strip {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            body.retain(|statement| !matches!(statement, GoStatement::Line(_)));
            body.iter_mut().for_each(|statement| self.statement(statement));
        }

        fn expression(&mut self, value: &mut GoExpression) {
            while let GoExpression::Attributed { value: inner, .. } = value {
                *value = std::mem::replace(inner, GoExpression::Boolean(false));
            }
            go_traversal::expression(self, value);
        }
    }
    let mut statements = statements.to_vec();
    Strip.block(&mut statements);
    statements
}
