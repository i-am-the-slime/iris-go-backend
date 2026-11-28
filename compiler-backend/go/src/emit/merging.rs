//! Branches of an `if` chain that do the same thing become one.
//!
//! Alternatives with the same right-hand side, `if n < 1 then problem else if n > 100 then problem`,
//! and inlined functions that answer the same for several constructors, `Black -> false; Leaf ->
//! false`, leave chains whose neighbouring branches are the same code. Neighbours join under
//! `||`, `if a { x } else if b { x }` is `if a || b { x }`, and a last test whose branch does
//! what the `else` does is dropped when evaluating it has no effect.

use rustc_hash::{FxHashMap, FxHashSet};

use super::conditions::is_pure;
use super::inlining::Rename;
use crate::go_traversal::{self, Walk, each_block_in_declaration};
use crate::syntax::{GoBinaryOperator, GoCase, GoDeclaration, GoExpression, GoStatement};

pub(super) fn merge_identical_branches(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if let GoStatement::Switch { cases, .. } = &mut block[position] {
                    merge_identical_cases(cases);
                }
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

/// Cases of a switch that run the same code, apart from the names of the locals they define,
/// as `Add l r -> leafCount l + leafCount r` and `Pow base exponent -> leafCount base + ...`,
/// become one case listing their values. The cases of a switch exclude each other, so where a
/// case stands does not change what it matches.
fn merge_identical_cases(cases: &mut Vec<GoCase>) {
    let mut merged: Vec<(GoCase, Vec<GoStatement>)> = vec![];
    for case in std::mem::take(cases) {
        let canonical = canonical(&case.body);
        match merged.iter_mut().find(|(_, known)| *known == canonical) {
            Some((first, _)) => first.values.extend(case.values),
            None => merged.push((case, canonical)),
        }
    }
    *cases = merged.into_iter().map(|(case, _)| case).collect();
}

/// The code of a block without its lines, its locals named by the order they are defined in.
fn canonical(body: &[GoStatement]) -> Vec<GoStatement> {
    struct Defined(Vec<String>);
    impl Walk for Defined {
        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Define { names, .. } => self.0.extend(names.iter().cloned()),
                GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                    self.0.push(name.clone())
                }
                GoStatement::Range { index, element, .. } => {
                    self.0.extend(index.iter().cloned());
                    self.0.push(element.clone());
                }
                GoStatement::Counting { variable, .. }
                | GoStatement::CountingDown { variable, .. } => self.0.push(variable.clone()),
                _ => {}
            }
            go_traversal::statement(self, statement);
        }
    }
    let mut statements = without_lines(body);
    let mut defined = Defined(vec![]);
    defined.block(&mut statements);
    let renamed: FxHashMap<String, String> = defined
        .0
        .into_iter()
        .filter(|name| name != "_")
        .enumerate()
        .map(|(position, name)| (name, format!("\0{position}")))
        .collect();
    Rename { renamed: &renamed }.block(&mut statements);
    statements
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
                        operator: GoBinaryOperator::LogicalOr,
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
        GoExpression::Binary {
            operator:
                GoBinaryOperator::LessThan
                | GoBinaryOperator::LessThanOrEqual
                | GoBinaryOperator::GreaterThan
                | GoBinaryOperator::GreaterThanOrEqual
                | GoBinaryOperator::Equal
                | GoBinaryOperator::NotEqual,
            left,
            right,
        } => Some((left.clone(), right.clone())),
        _ => None,
    };
    match (operands(left), operands(right)) {
        (Some((a, b)), Some((c, d))) => (a == c && b == d) || (a == d && b == c),
        _ => false,
    }
}

/// Whether two blocks are the same code apart from the PureScript lines they are attributed to.
pub(super) fn same_code(left: &[GoStatement], right: &[GoStatement]) -> bool {
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

/// Neighbouring `if`s that test the same thing become one: `paired < 1` choosing one slice and
/// then the other is one test choosing both. The first `if` must not change what the test
/// reads, and must not leave the block on either branch; the variables declared between the
/// two move up.
pub(super) fn join_repeated_tests(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let strings = super::known::unchanging_strings(declaration);
        each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if !join_next_test(block, position, &strings) {
                    position += 1;
                }
            }
        });
    }
}

fn join_next_test(
    block: &mut Vec<GoStatement>,
    position: usize,
    strings: &FxHashSet<String>,
) -> bool {
    let GoStatement::If { condition, then, otherwise } = &block[position] else { return false };
    let stable = super::known::reads_only(condition, strings);
    if !stable || [then, otherwise].iter().any(|branch| leaves(branch)) {
        return false;
    }
    let declared = block[position + 1..]
        .iter()
        .take_while(|statement| matches!(statement, GoStatement::Variable { value: None, .. }))
        .count();
    let next = position + 1 + declared;
    let same = matches!(block.get(next), Some(GoStatement::If { condition: repeated, .. })
        if repeated == condition);
    if !same {
        return false;
    }
    let mut read = vec![];
    go_traversal::each_expression_in_statement(
        &mut GoStatement::Expression(condition.clone()),
        |expression| {
            if let GoExpression::Identifier(name) = expression {
                read.push(name.clone());
            }
        },
    );
    let GoStatement::If { then, otherwise, .. } = &mut block[position] else { unreachable!() };
    let changes = then
        .iter_mut()
        .chain(otherwise.iter_mut())
        .any(|statement| read.iter().any(|name| super::aliases::writes(statement, name)));
    if changes {
        return false;
    }
    let GoStatement::If { then: more, otherwise: more_otherwise, .. } = block.remove(next) else {
        unreachable!()
    };
    let GoStatement::If { then, otherwise, .. } = &mut block[position] else { unreachable!() };
    then.extend(more);
    otherwise.extend(more_otherwise);
    let declarations: Vec<GoStatement> = block.drain(position + 1..next).collect();
    block.splice(position..position, declarations);
    true
}

/// Whether a branch ends by leaving the block it is in.
fn leaves(branch: &[GoStatement]) -> bool {
    branch.last().is_some_and(|last| {
        last.is_panic()
            || matches!(
                last,
                GoStatement::Return(_)
                    | GoStatement::Break
                    | GoStatement::Continue
                    | GoStatement::BreakTo(_)
            )
    })
}
