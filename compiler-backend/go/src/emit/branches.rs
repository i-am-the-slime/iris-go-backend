use super::conditions::{is_pure, negated};
use crate::go_traversal::{self, Walk, each_expression_in_statement};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

pub(super) fn simplify_branches(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        go_traversal::declaration(&mut Branches, declaration);
    }
}

struct Branches;

impl Walk for Branches {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        sink_calls_into_branches(body);
        body.iter_mut().for_each(|statement| self.statement(statement));
        let alone = body.iter().filter(|statement| !matches!(statement, GoStatement::Line(_))).count() == 1;
        let statements = std::mem::take(body);
        for statement in statements {
            body.extend(simplified(statement, alone));
        }
    }

    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        if let GoExpression::Unary { operator: "!", operand } = value
            && let GoExpression::Binary { operator: "==" | "!=", .. } = operand.unattributed()
        {
            *value = negated(operand.unattributed());
        }
    }
}

fn sink_calls_into_branches(body: &mut Vec<GoStatement>) {
    let mut index = 0;
    while index < body.len() {
        if let Some((choice, call)) = chosen_then_called(body, index) {
            let GoStatement::Expression(GoExpression::Call { function, arguments }) =
                body.remove(call)
            else {
                unreachable!()
            };
            let method = match *function {
                GoExpression::Field { name, .. } => Some(name),
                _ => None,
            };
            let GoStatement::If { then, otherwise, .. } = &mut body[choice] else {
                unreachable!()
            };
            for branch in [then, otherwise] {
                let last = last_effective(branch).expect("invariant violated: no assignment");
                let GoStatement::Assign { mut values, .. } = branch.remove(last) else {
                    unreachable!()
                };
                let chosen = values.remove(0);
                let function = match &method {
                    Some(method) => {
                        GoExpression::Field { value: Box::new(chosen), name: method.clone() }
                    }
                    None => chosen,
                };
                let called =
                    GoExpression::Call { function: Box::new(function), arguments: arguments.clone() };
                branch.insert(last, GoStatement::Expression(called));
            }
            body.remove(index);
            continue;
        }
        index += 1;
    }
}

fn chosen_then_called(body: &mut [GoStatement], index: usize) -> Option<(usize, usize)> {
    let GoStatement::Variable { name, value: None, .. } = &body[index] else { return None };
    let name = name.clone();
    let choice = next_effective(body, index + 1)?;
    let call = next_effective(body, choice + 1)?;
    let GoStatement::If { then, otherwise, .. } = &body[choice] else { return None };
    if !assigns_last(then, &name) || !assigns_last(otherwise, &name) {
        return None;
    }
    let GoStatement::Expression(GoExpression::Call { function, arguments }) = &body[call] else {
        return None;
    };
    let receiver = match function.as_ref() {
        GoExpression::Field { value, .. } => value.unattributed(),
        function => function,
    };
    let receives = matches!(receiver, GoExpression::Identifier(receiver) if *receiver == name);
    if !receives || !arguments.iter().all(is_pure) {
        return None;
    }
    let uses: usize = body[index + 1..]
        .iter_mut()
        .map(|statement| mentions(statement, &name))
        .sum();
    (uses == 3).then_some((choice, call))
}

fn assigns_last(branch: &[GoStatement], name: &str) -> bool {
    let Some(last) = last_effective(branch) else { return false };
    let GoStatement::Assign { targets, values } = &branch[last] else { return false };
    let [GoExpression::Identifier(target)] = targets.as_slice() else { return false };
    target == name && values.len() == 1
}

fn last_effective(branch: &[GoStatement]) -> Option<usize> {
    branch.iter().rposition(|statement| !matches!(statement, GoStatement::Line(_)))
}

fn next_effective(body: &[GoStatement], from: usize) -> Option<usize> {
    (from..body.len()).find(|&index| !matches!(body[index], GoStatement::Line(_)))
}

fn mentions(statement: &mut GoStatement, name: &str) -> usize {
    let mut count = 0;
    each_expression_in_statement(statement, |expression| {
        if matches!(expression, GoExpression::Identifier(found) if found == name) {
            count += 1;
        }
    });
    count
}

fn simplified(statement: GoStatement, alone: bool) -> Vec<GoStatement> {
    match statement {
        GoStatement::Expression(call) => match called_literal_body(&call, alone) {
            Some(body) => body,
            None => vec![GoStatement::Expression(call)],
        },
        GoStatement::If { condition, then, otherwise } => {
            let then_empty = then.iter().all(|statement| matches!(statement, GoStatement::Line(_)));
            let otherwise_empty =
                otherwise.iter().all(|statement| matches!(statement, GoStatement::Line(_)));
            match (then_empty, otherwise_empty) {
                (true, true) if is_pure(&condition) => vec![],
                (true, false) => vec![GoStatement::If {
                    condition: negated(condition.unattributed()),
                    then: otherwise,
                    otherwise: vec![],
                }],
                (false, true) => vec![GoStatement::If { condition, then, otherwise: vec![] }],
                _ => vec![GoStatement::If { condition, then, otherwise }],
            }
        }
        statement => vec![statement],
    }
}

fn called_literal_body(call: &GoExpression, alone: bool) -> Option<Vec<GoStatement>> {
    let GoExpression::Call { function, arguments } = call.unattributed() else { return None };
    if !arguments.iter().all(is_pure) {
        return None;
    }
    let literal = match function.unattributed() {
        GoExpression::Field { value, name } => {
            let GoExpression::Composite { fields, .. } = value.unattributed() else { return None };
            let only_functions = fields
                .iter()
                .all(|(_, field)| matches!(field.unattributed(), GoExpression::Function { .. }));
            if !only_functions {
                return None;
            }
            let (_, field) = fields.iter().find(|(label, _)| label.as_deref() == Some(name))?;
            field.unattributed()
        }
        function => function,
    };
    let GoExpression::Function { parameters, result: None, body } = literal else { return None };
    let unnamed = parameters.iter().all(|(name, _)| name == "_");
    let declares = body
        .iter()
        .any(|statement| matches!(statement, GoStatement::Define { .. } | GoStatement::Variable { .. }));
    (unnamed && !returns(body) && (alone || !declares)).then(|| body.clone())
}

fn returns(body: &[GoStatement]) -> bool {
    body.iter().any(|statement| match statement {
        GoStatement::Return(_) | GoStatement::Defer(_) => true,
        GoStatement::If { then, otherwise, .. } => returns(then) || returns(otherwise),
        GoStatement::Switch { cases, default, .. } => {
            cases.iter().any(|case| returns(&case.body))
                || default.as_ref().is_some_and(|default| returns(&default.body))
        }
        GoStatement::IfAssert { then: body, .. }
        | GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. }
        | GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. } => returns(body),
        _ => false,
    })
}
