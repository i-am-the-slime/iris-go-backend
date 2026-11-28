use super::aliases::{Guarded, writes};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

pub(super) fn join_shared_updates(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let guarded = Guarded::of(declaration);
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if let Some(update) = shared_update(&mut block[position], &guarded) {
                    block.insert(position + 1, update);
                }
                position += 1;
            }
        });
    }
}

fn shared_update(statement: &mut GoStatement, guarded: &Guarded) -> Option<GoStatement> {
    let GoStatement::If { then, otherwise, .. } = statement else { return None };
    let candidates = assigned_names(then.last()?)?;
    for target in candidates {
        if guarded.mentioned_in_literal(&target) {
            continue;
        }
        let Some(joined) = joined_value(then, &target, guarded) else { continue };
        let Some(other) = joined_value(otherwise, &target, guarded) else { continue };
        if !same(&joined, &other) || (is_only_assignment(then) && is_only_assignment(otherwise)) {
            continue;
        }
        drop_assignment(then, &target);
        drop_assignment(otherwise, &target);
        let target = GoExpression::Identifier(target);
        return Some(GoStatement::Assign { targets: vec![target], values: vec![joined] });
    }
    None
}

fn is_only_assignment(branch: &[GoStatement]) -> bool {
    match branch {
        [GoStatement::Assign { targets, .. }] => targets.len() == 1,
        _ => false,
    }
}

fn assigned_names(statement: &GoStatement) -> Option<Vec<String>> {
    let GoStatement::Assign { targets, .. } = statement else { return None };
    targets
        .iter()
        .map(|target| match target {
            GoExpression::Identifier(name) => Some(name.clone()),
            _ => None,
        })
        .collect()
}

fn joined_value(
    branch: &mut [GoStatement],
    target: &str,
    guarded: &Guarded,
) -> Option<GoExpression> {
    let (last, earlier) = branch.split_last_mut()?;
    if earlier.iter_mut().any(|statement| writes(statement, target)) {
        return None;
    }
    let GoStatement::Assign { targets, values } = last else { return None };
    if targets.len() != values.len() {
        return None;
    }
    let names: Vec<&str> = targets
        .iter()
        .map(|target| match target {
            GoExpression::Identifier(name) => Some(name.as_str()),
            _ => None,
        })
        .collect::<Option<_>>()?;
    let position = names.iter().position(|name| *name == target)?;
    let value = &values[position];
    if matches!(value, GoExpression::Identifier(name) if name == target) {
        return None;
    }
    let mut declared = Declared { names: vec![] };
    earlier.iter_mut().for_each(|statement| declared.statement(statement));
    let after = |name: &str| -> Option<String> {
        if name == target {
            return Some(name.to_string());
        }
        let copied = names.iter().zip(values.iter()).find(|(other, value)| {
            **other != target && matches!(value, GoExpression::Identifier(copied) if copied == name)
        });
        if let Some((other, _)) = copied {
            return Some(other.to_string());
        }
        let hidden = names.contains(&name)
            || declared.names.iter().any(|declared| declared == name)
            || guarded.mentioned_in_literal(name);
        (!hidden).then(|| name.to_string())
    };
    renamed(value, &after)
}

fn renamed(value: &GoExpression, after: &impl Fn(&str) -> Option<String>) -> Option<GoExpression> {
    Some(match value {
        GoExpression::Identifier(name) => GoExpression::Identifier(after(name)?),
        GoExpression::Integer(constant) => GoExpression::Integer(*constant),
        GoExpression::Binary { operator, left, right } => GoExpression::Binary {
            operator: *operator,
            left: Box::new(renamed(left, after)?),
            right: Box::new(renamed(right, after)?),
        },
        _ => return None,
    })
}

fn same(left: &GoExpression, right: &GoExpression) -> bool {
    match (left, right) {
        (GoExpression::Identifier(left), GoExpression::Identifier(right)) => left == right,
        (GoExpression::Integer(left), GoExpression::Integer(right)) => left == right,
        (
            GoExpression::Binary { operator, left, right },
            GoExpression::Binary { operator: other, left: other_left, right: other_right },
        ) => operator == other && same(left, other_left) && same(right, other_right),
        _ => false,
    }
}

fn drop_assignment(branch: &mut Vec<GoStatement>, target: &str) {
    let Some(GoStatement::Assign { targets, values }) = branch.last_mut() else { return };
    let Some(position) = targets
        .iter()
        .position(|assigned| matches!(assigned, GoExpression::Identifier(name) if name == target))
    else {
        return;
    };
    targets.remove(position);
    values.remove(position);
    if targets.is_empty() {
        branch.pop();
    }
}

struct Declared {
    names: Vec<String>,
}

impl Walk for Declared {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, .. } => self.names.extend(names.iter().cloned()),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                self.names.push(name.clone())
            }
            GoStatement::Range { index, element, .. } => {
                self.names.extend(index.iter().cloned());
                self.names.push(element.clone());
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.names.push(variable.clone())
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, _: &mut GoExpression) {}
}
