use super::branches;
use crate::go_traversal;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, Name, statements_names};

const COPIED_TESTS: usize = 3;

const TEST_STATEMENTS: usize = 5;

pub(super) fn test_in_each_branch(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let mut tested = false;
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position + 2 < block.len() {
                if test_in_branches(block, position) {
                    tested = true;
                } else {
                    position += 1;
                }
            }
        });
        if tested {
            branches::simplify_branches(std::slice::from_mut(declaration));
        }
    }
}

fn test_in_branches(block: &mut Vec<GoStatement>, position: usize) -> bool {
    let GoStatement::Variable { name, value: None, .. } = &block[position] else { return false };
    let name = name.clone();
    let name = name.as_str();
    let GoStatement::If { condition, .. } = &block[position + 2] else { return false };
    if !mentions(condition, name) || !is_small(&block[position + 2]) {
        return false;
    }
    let tested = matches!(condition, GoExpression::Identifier(tested) if tested == name);
    let mut leaves = 0;
    let assigned = assigns_in_every_leaf(&block[position + 1], name, tested, &mut leaves);
    if !assigned || leaves > COPIED_TESTS {
        return false;
    }
    let mut rest = block[position + 3..].to_vec();
    if references(&mut rest, name) {
        return false;
    }
    let mut chain = vec![block[position + 1].clone()];
    let mut test = vec![block[position + 2].clone()];
    let mut bound = vec![];
    statements_names(&mut chain, &mut |reference| {
        if let Name::Binder(binder) = reference {
            bound.push(binder.clone());
        }
    });
    if bound.iter().any(|binder| references(&mut test, binder)) {
        return false;
    }
    let test = block.remove(position + 2);
    if !tested {
        append_to_leaves(&mut block[position + 1], &test);
        return true;
    }
    let GoStatement::If { then, otherwise, .. } = test else { unreachable!() };
    let mut chain = block[position + 1].clone();
    test_assigned_values(&mut chain, &then, &otherwise);
    let mut tested_chain = vec![chain];
    if references(&mut tested_chain, name) {
        block
            .insert(position + 2, GoStatement::If { condition: identifier(name), then, otherwise });
        return false;
    }
    block.splice(position..position + 2, tested_chain);
    true
}

fn identifier(name: &str) -> GoExpression {
    GoExpression::Identifier(name.to_string())
}

fn test_assigned_values(
    statement: &mut GoStatement,
    then: &[GoStatement],
    otherwise: &[GoStatement],
) {
    let GoStatement::If { then: first, otherwise: second, .. } = statement else { return };
    for branch in [first, second] {
        if let Some(last @ GoStatement::If { .. }) = branch.last_mut() {
            test_assigned_values(last, then, otherwise);
            continue;
        }
        let Some(GoStatement::Assign { mut values, .. }) = branch.pop() else { unreachable!() };
        match values.pop().expect("a tested value is assigned") {
            GoExpression::Boolean(true) => branch.extend(then.iter().cloned()),
            GoExpression::Boolean(false) => branch.extend(otherwise.iter().cloned()),
            condition => branch.push(GoStatement::If {
                condition,
                then: then.to_vec(),
                otherwise: otherwise.to_vec(),
            }),
        }
    }
}

fn assigns_in_every_leaf(
    statement: &GoStatement,
    name: &str,
    tested: bool,
    leaves: &mut usize,
) -> bool {
    let GoStatement::If { then, otherwise, .. } = statement else { return false };
    [then, otherwise].into_iter().all(|branch| match branch.last() {
        Some(last @ GoStatement::If { .. }) => assigns_in_every_leaf(last, name, tested, leaves),
        Some(GoStatement::Assign { targets, values }) if tested => {
            let only =
                matches!(targets.as_slice(), [GoExpression::Identifier(target)] if target == name);
            if values.as_slice() != [GoExpression::Boolean(false)] {
                *leaves += 1;
            }
            only && values.len() == 1
        }
        Some(GoStatement::Assign { targets, .. }) if assigns(targets, name) => {
            *leaves += 1;
            true
        }
        _ => false,
    })
}

fn assigns(targets: &[GoExpression], name: &str) -> bool {
    targets
        .iter()
        .any(|target| matches!(target, GoExpression::Identifier(target) if target == name))
}

fn append_to_leaves(statement: &mut GoStatement, test: &GoStatement) {
    let GoStatement::If { then, otherwise, .. } = statement else { return };
    for branch in [then, otherwise] {
        match branch.last_mut() {
            Some(last @ GoStatement::If { .. }) => append_to_leaves(last, test),
            _ => branch.push(test.clone()),
        }
    }
}

fn is_small(test: &GoStatement) -> bool {
    let mut statements = 0;
    let mut small = true;
    count_statements(std::slice::from_ref(test), &mut statements, &mut small);
    small && statements <= TEST_STATEMENTS
}

fn count_statements(block: &[GoStatement], statements: &mut usize, small: &mut bool) {
    for statement in block {
        *statements += 1;
        match statement {
            GoStatement::If { then, otherwise, .. } => {
                count_statements(then, statements, small);
                count_statements(otherwise, statements, small);
            }
            GoStatement::Assign { .. } | GoStatement::Continue | GoStatement::Line(_) => {}
            _ => *small = false,
        }
    }
}

fn mentions(condition: &GoExpression, name: &str) -> bool {
    let mut tested = vec![GoStatement::Expression(condition.clone())];
    references(&mut tested, name)
}

fn references(statements: &mut [GoStatement], name: &str) -> bool {
    let mut found = false;
    statements_names(statements, &mut |reference| {
        let (Name::Reference(used) | Name::Written(used) | Name::Binder(used)) = reference;
        found |= used == name;
    });
    found
}
