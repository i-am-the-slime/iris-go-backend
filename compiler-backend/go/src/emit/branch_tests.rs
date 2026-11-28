use super::{branches, known, merging};
use crate::go_traversal;
use crate::syntax::{
    GoCase, GoDeclaration, GoDefault, GoExpression, GoStatement, GoType, Name, statements_names,
};

const COPIED_TESTS: usize = 3;

const TEST_STATEMENTS: usize = 5;

const CHOSEN_CASE_STATEMENTS: usize = 48;

pub(super) fn test_in_each_branch(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let mut tested = false;
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position + 2 < block.len() {
                if test_in_branches(block, position) || switch_in_branches(block, position) {
                    tested = true;
                } else {
                    position += 1;
                }
            }
        });
        if tested {
            known::drop_known_tests(std::slice::from_mut(declaration));
            merging::join_repeated_tests(std::slice::from_mut(declaration));
            branches::simplify_branches(std::slice::from_mut(declaration));
            go_traversal::each_block_in_declaration(declaration, define_assigned_variables);
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

fn switch_in_branches(block: &mut Vec<GoStatement>, position: usize) -> bool {
    let GoStatement::Variable { name, value: None, .. } = &block[position] else { return false };
    let name = name.clone();
    let GoStatement::Switch { value: Some(GoExpression::Identifier(switched)), cases, default } =
        &block[position + 2]
    else {
        return false;
    };
    if *switched != name {
        return false;
    }
    let mut leaves = vec![];
    if !assigned_values(&block[position + 1], &name, &mut leaves) {
        return false;
    }
    let opaque = leaves.iter().filter(|value| !is_literal(value)).count();
    if opaque != 1 {
        return false;
    }
    let mut copied = 0;
    for value in leaves.iter().filter(|value| is_literal(value)) {
        let Some(body) = chosen_case(cases, default.as_ref(), value) else { return false };
        let mut statements = 0;
        let mut _small = true;
        count_statements(body, &mut statements, &mut _small);
        copied += statements;
        if leaves_switch(body) {
            return false;
        }
    }
    if copied > CHOSEN_CASE_STATEMENTS {
        return false;
    }
    let mut rest = block[position + 3..].to_vec();
    if references(&mut rest, &name) {
        return false;
    }
    let mut chain = vec![block[position + 1].clone()];
    let mut switch = vec![block[position + 2].clone()];
    let mut bound = vec![];
    statements_names(&mut chain, &mut |reference| {
        if let Name::Binder(binder) = reference {
            bound.push(binder.clone());
        }
    });
    if bound.iter().any(|binder| references(&mut switch, binder)) {
        return false;
    }
    let switch = block.remove(position + 2);
    choose_cases_in_leaves(&mut block[position + 1], &name, &switch);
    true
}

fn assigned_values(statement: &GoStatement, name: &str, values: &mut Vec<GoExpression>) -> bool {
    let GoStatement::If { then, otherwise, .. } = statement else { return false };
    [then, otherwise].into_iter().all(|branch| match branch.last() {
        Some(last @ GoStatement::If { .. }) => assigned_values(last, name, values),
        Some(GoStatement::Assign { targets, values: assigned }) => {
            match (targets.as_slice(), assigned.as_slice()) {
                ([GoExpression::Identifier(target)], [value]) if target == name => {
                    values.push(value.clone());
                    true
                }
                _ => false,
            }
        }
        _ => false,
    })
}

fn is_literal(value: &GoExpression) -> bool {
    matches!(
        value,
        GoExpression::Integer(_)
            | GoExpression::String(_)
            | GoExpression::Rune(_)
            | GoExpression::Boolean(_)
    )
}

fn chosen_case<'s>(
    cases: &'s [GoCase],
    default: Option<&'s GoDefault>,
    value: &GoExpression,
) -> Option<&'s [GoStatement]> {
    let matched = cases.iter().find(|case| case.values.contains(value));
    if let Some(case) = matched {
        return Some(&case.body);
    }
    let literals = cases.iter().flat_map(|case| case.values.iter()).all(is_literal);
    if !literals {
        return None;
    }
    Some(default.map_or(&[][..], |default| &default.body))
}

fn leaves_switch(body: &[GoStatement]) -> bool {
    body.iter().any(|statement| match statement {
        GoStatement::Break | GoStatement::BreakTo(_) | GoStatement::LabeledLoop { .. } => true,
        GoStatement::If { then, otherwise, .. } => leaves_switch(then) || leaves_switch(otherwise),
        GoStatement::IfAssert { then, .. } => leaves_switch(then),
        GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. }
        | GoStatement::Loop(body) => leaves_switch(body),
        GoStatement::Switch { cases, default, .. } => {
            cases.iter().any(|case| leaves_switch(&case.body))
                || default.as_ref().is_some_and(|default| leaves_switch(&default.body))
        }
        _ => false,
    })
}

fn choose_cases_in_leaves(statement: &mut GoStatement, name: &str, switch: &GoStatement) {
    let GoStatement::If { then, otherwise, .. } = statement else { return };
    let GoStatement::Switch { cases, default, .. } = switch else { return };
    for branch in [then, otherwise] {
        if let Some(last @ GoStatement::If { .. }) = branch.last_mut() {
            choose_cases_in_leaves(last, name, switch);
            continue;
        }
        let Some(GoStatement::Assign { values, .. }) = branch.last() else { unreachable!() };
        let value = values[0].clone();
        if !is_literal(&value) {
            branch.push(switch.clone());
            continue;
        }
        let body = chosen_case(cases, default.as_ref(), &value).expect("a literal chooses a case");
        let mut body = body.to_vec();
        if !references(&mut body, name) {
            branch.pop();
        }
        branch.extend(body);
    }
}

fn define_assigned_variables(block: &mut Vec<GoStatement>) {
    let mut position = 0;
    while position + 1 < block.len() {
        let GoStatement::Variable { name, type_, value: None } = &block[position] else {
            position += 1;
            continue;
        };
        let GoStatement::Assign { targets, values } = &block[position + 1] else {
            position += 1;
            continue;
        };
        let assigned = match (targets.as_slice(), values.as_slice()) {
            ([GoExpression::Identifier(target)], [value]) if target == name => value,
            _ => {
                position += 1;
                continue;
            }
        };
        let typed = match assigned {
            GoExpression::Conversion { type_: converted, .. } => converted == type_,
            GoExpression::Slice { .. } => *type_ == GoType::String,
            _ => false,
        };
        if typed {
            let define =
                GoStatement::Define { names: vec![name.clone()], values: vec![assigned.clone()] };
            block.splice(position..position + 2, [define]);
        }
        position += 1;
    }
}
