use crate::go_traversal;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType, Name, statements_names};

const COPIED_BODIES: usize = 2;

pub(super) fn run_bodies_of_chosen_singletons(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position + 2 < block.len() {
                if run_body_in_branches(block, position) {
                    continue;
                }
                position += 1;
            }
        });
    }
}

fn run_body_in_branches(block: &mut Vec<GoStatement>, position: usize) -> bool {
    let GoStatement::Variable { name, type_: GoType::Slice(element_type), value: None } =
        &block[position]
    else {
        return false;
    };
    let element_type = (**element_type).clone();
    let GoStatement::Range { index, element, iterable: GoExpression::Identifier(ranged), body } =
        &block[position + 2]
    else {
        return false;
    };
    if ranged != name || leaves_loop(body) {
        return false;
    }
    let mut singletons = 0;
    if !chooses_literals(&block[position + 1], name, &mut singletons) || singletons > COPIED_BODIES
    {
        return false;
    }
    let mut rest = block[position + 3..].to_vec();
    if references(&mut rest, name) {
        return false;
    }
    let mut unassigned = vec![block[position + 1].clone()];
    strip_assignments(&mut unassigned[0]);
    if references(&mut unassigned, name) {
        return false;
    }
    let (index, element, body) = (index.clone(), element.clone(), body.clone());
    let mut chain = block[position + 1].clone();
    run_in_leaves(&mut chain, name, &|value| {
        let mut ran = vec![];
        if let Some(index) = index.as_ref().filter(|index| *index != "_") {
            ran.push(GoStatement::Define {
                names: vec![index.clone()],
                values: vec![GoExpression::Integer(0)],
            });
        }
        if element != "_" {
            ran.push(GoStatement::Variable {
                name: element.clone(),
                type_: element_type.clone(),
                value: Some(value),
            });
        }
        ran.extend(body.iter().cloned());
        ran
    });
    block.splice(position..position + 3, [chain]);
    true
}

fn leaves_loop(body: &[GoStatement]) -> bool {
    body.iter().any(|statement| match statement {
        GoStatement::Break | GoStatement::Continue | GoStatement::BreakTo(_) => true,
        GoStatement::LabeledLoop { .. } => true,
        GoStatement::If { then, otherwise, .. } => leaves_loop(then) || leaves_loop(otherwise),
        GoStatement::IfAssert { then, .. } => leaves_loop(then),
        GoStatement::Switch { cases, default, .. } => {
            cases.iter().any(|case| leaves_loop(&case.body))
                || default.as_ref().is_some_and(|default| leaves_loop(&default.body))
        }
        GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. }
        | GoStatement::Loop(body) => breaks_to_label(body),
        _ => false,
    })
}

fn breaks_to_label(body: &[GoStatement]) -> bool {
    body.iter().any(|statement| match statement {
        GoStatement::BreakTo(_) | GoStatement::LabeledLoop { .. } => true,
        GoStatement::If { then, otherwise, .. } => {
            breaks_to_label(then) || breaks_to_label(otherwise)
        }
        GoStatement::IfAssert { then, .. } => breaks_to_label(then),
        GoStatement::Switch { cases, default, .. } => {
            cases.iter().any(|case| breaks_to_label(&case.body))
                || default.as_ref().is_some_and(|default| breaks_to_label(&default.body))
        }
        GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. }
        | GoStatement::Loop(body) => breaks_to_label(body),
        _ => false,
    })
}

fn chooses_literals(statement: &GoStatement, name: &str, singletons: &mut usize) -> bool {
    let GoStatement::If { then, otherwise, .. } = statement else { return false };
    [then, otherwise].into_iter().all(|branch| match branch.as_slice() {
        [chain @ GoStatement::If { .. }] => chooses_literals(chain, name, singletons),
        [.., last] => match assigned_literal(last, name) {
            Some(elements) if elements.len() <= 1 => {
                *singletons += elements.len();
                true
            }
            _ => false,
        },
        [] => true,
    })
}

fn assigned_literal<'s>(statement: &'s GoStatement, name: &str) -> Option<Vec<&'s GoExpression>> {
    let GoStatement::Assign { targets, values } = statement else { return None };
    let ([GoExpression::Identifier(target)], [value]) = (targets.as_slice(), values.as_slice())
    else {
        return None;
    };
    if target != name {
        return None;
    }
    match value {
        GoExpression::Composite { fields, .. } if fields.iter().all(|(key, _)| key.is_none()) => {
            Some(fields.iter().map(|(_, value)| value).collect())
        }
        _ => None,
    }
}

fn strip_assignments(statement: &mut GoStatement) {
    let GoStatement::If { then, otherwise, .. } = statement else { return };
    for branch in [then, otherwise] {
        match branch.as_mut_slice() {
            [chain @ GoStatement::If { .. }] => strip_assignments(chain),
            [] => {}
            _ => {
                branch.pop();
            }
        }
    }
}

fn run_in_leaves(
    statement: &mut GoStatement,
    name: &str,
    run: &dyn Fn(GoExpression) -> Vec<GoStatement>,
) {
    let GoStatement::If { then, otherwise, .. } = statement else { return };
    for branch in [then, otherwise] {
        if let [chain @ GoStatement::If { .. }] = branch.as_mut_slice() {
            run_in_leaves(chain, name, run);
            continue;
        }
        let Some(last) = branch.pop() else { continue };
        let elements = assigned_literal(&last, name).expect("a branch assigns a literal");
        if let Some(&element) = elements.first() {
            branch.extend(run(element.clone()));
        }
    }
}

fn references(statements: &mut [GoStatement], name: &str) -> bool {
    let mut found = false;
    statements_names(statements, &mut |reference| {
        let (Name::Reference(used) | Name::Written(used) | Name::Binder(used)) = reference;
        found |= used == name;
    });
    found
}
