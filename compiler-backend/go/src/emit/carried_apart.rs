use super::conditions::negated;
use super::ownership::Place;
use super::{Emitter, conjunction, field, identifier_expression};
use crate::error::GoResult;
use crate::go_traversal::{self, Walk};
use crate::monomorphic::{Pattern, PatternKind};
use crate::syntax::{GoBinaryOperator, GoExpression, GoStatement};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn carried_apart(
        &mut self,
        looped: GoStatement,
        places: &[&Place],
        absorbing: Option<&Pattern>,
        (accumulator, initial): (&str, &GoExpression),
    ) -> GoResult<Vec<GoStatement>> {
        let ([Place::Constructor { constructor, index: 0, go_field }], Some(absorbing)) =
            (places, absorbing)
        else {
            return Ok(vec![looped]);
        };
        let PatternKind::Constructor { data, constructor: absorbing_constructor, .. } =
            &absorbing.kind
        else {
            return Ok(vec![looped]);
        };
        let layout = self.data_layout(data)?;
        if absorbing_constructor == constructor
            || layout.boxed
            || layout.constructors.len() != 2
            || layout.constructors[*constructor].fields.len() != 1
        {
            return Ok(vec![looped]);
        }
        let mut tests = vec![];
        self.pattern_tests(absorbing, identifier_expression(accumulator), &mut tests, &mut vec![])?;
        let Some(absorbed) = conjunction(tests) else { return Ok(vec![looped]) };
        let scalar = self.temporary("carried");
        let kept = self.construct(data, *constructor, vec![identifier_expression(&scalar)])?;
        let mut apart = Apart {
            accumulator,
            copies: vec![],
            field: go_field,
            scalar: &scalar,
            kept: &kept,
            intact: true,
            in_function: false,
        };
        let mut rewritten = looped.clone();
        apart.statement(&mut rewritten);
        if !apart.intact {
            return Ok(vec![looped]);
        }
        let absorbed_fields = layout.constructors[*absorbing_constructor].fields.len();
        let placeholders = vec![identifier_expression(&scalar); absorbed_fields];
        let absorbing_value = self.construct(data, *absorbing_constructor, placeholders)?;
        let leaving = Leaving {
            accumulator,
            absorbed: &absorbed,
            value: &absorbing_value,
            placeholder: &scalar,
        };
        if let Some(body) = loop_body(&mut rewritten) {
            let starts_kept = kept_argument(&kept, initial, &scalar).is_some();
            leaving.leave_once_absorbed(body, starts_kept);
        }
        let carried = field(identifier_expression(accumulator), go_field);
        let read =
            GoStatement::Define { names: vec![scalar.clone()], values: vec![carried.clone()] };
        let written = GoStatement::Assign {
            targets: vec![carried],
            values: vec![identifier_expression(&scalar)],
        };
        let written = GoStatement::If {
            condition: negated(&absorbed),
            then: vec![written],
            otherwise: vec![],
        };
        Ok(vec![read, rewritten, written])
    }
}

struct Apart<'a> {
    accumulator: &'a str,
    copies: Vec<String>,
    field: &'a str,
    scalar: &'a str,
    kept: &'a GoExpression,
    intact: bool,
    in_function: bool,
}

impl Apart<'_> {
    fn holds_accumulator(&self, name: &str) -> bool {
        name == self.accumulator || self.copies.iter().any(|copy| copy == name)
    }
}

impl Walk for Apart<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values }
                if !self.in_function
                    && matches!((names.as_slice(), values.as_slice()),
                        ([_], [GoExpression::Identifier(copied)]) if self.holds_accumulator(copied)) =>
            {
                self.copies.push(names[0].clone());
            }
            GoStatement::Assign { targets, values }
                if matches!(targets.as_slice(),
                    [GoExpression::Identifier(target)] if target == self.accumulator) =>
            {
                let [value] = values.as_mut_slice() else {
                    self.intact = false;
                    return;
                };
                if self.in_function {
                    self.intact = false;
                    return;
                }
                let Some(mut appended) = kept_argument(self.kept, value, self.scalar) else {
                    return self.expression(value);
                };
                self.expression(&mut appended);
                *statement = GoStatement::Assign {
                    targets: vec![identifier_expression(self.scalar)],
                    values: vec![appended],
                };
            }
            _ => go_traversal::statement(self, statement),
        }
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Field { value: record, name } if matches!(record.as_ref(), GoExpression::Identifier(read) if self.holds_accumulator(read)) => {
                if self.in_function {
                    self.intact = false;
                } else if name == self.field {
                    *value = identifier_expression(self.scalar);
                }
            }
            GoExpression::Identifier(name) if self.holds_accumulator(name) => self.intact = false,
            GoExpression::Function { .. } => {
                let enclosing = std::mem::replace(&mut self.in_function, true);
                go_traversal::expression(self, value);
                self.in_function = enclosing;
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

fn kept_argument(
    kept: &GoExpression,
    value: &GoExpression,
    placeholder: &str,
) -> Option<GoExpression> {
    let is_placeholder = |expression: &GoExpression| matches!(expression, GoExpression::Identifier(name) if name == placeholder);
    let argument = |expected: &[&GoExpression], given: &[&GoExpression]| {
        if expected.len() != given.len() {
            return None;
        }
        let mut argument = None;
        for (expected, given) in expected.iter().zip(given) {
            if is_placeholder(expected) {
                argument = Some((*given).clone());
            } else if expected != given {
                return None;
            }
        }
        argument
    };
    match (kept, value) {
        (_, GoExpression::Attributed { value, .. }) => kept_argument(kept, value, placeholder),
        (
            GoExpression::Call { function: expected, arguments: expected_arguments },
            GoExpression::Call { function: given, arguments: given_arguments },
        ) if expected == given => argument(
            &expected_arguments.iter().collect::<Vec<_>>(),
            &given_arguments.iter().collect::<Vec<_>>(),
        ),
        (
            GoExpression::Composite { type_: expected, fields: expected_fields },
            GoExpression::Composite { type_: given, fields: given_fields },
        ) if expected == given
            && expected_fields.len() == given_fields.len()
            && expected_fields.iter().zip(given_fields).all(|(left, right)| left.0 == right.0) =>
        {
            argument(
                &expected_fields.iter().map(|(_, value)| value).collect::<Vec<_>>(),
                &given_fields.iter().map(|(_, value)| value).collect::<Vec<_>>(),
            )
        }
        (GoExpression::Address(expected), GoExpression::Address(given)) => {
            kept_argument(expected, given, placeholder)
        }
        _ => None,
    }
}

fn loop_body(looped: &mut GoStatement) -> Option<&mut Vec<GoStatement>> {
    match looped {
        GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. }
        | GoStatement::Loop(body) => Some(body),
        _ => None,
    }
}

struct Leaving<'a> {
    accumulator: &'a str,
    absorbed: &'a GoExpression,
    value: &'a GoExpression,
    placeholder: &'a str,
}

impl Leaving<'_> {
    fn leave_once_absorbed(&self, body: &mut Vec<GoStatement>, starts_kept: bool) {
        let Some(check) = body.iter().position(|statement| self.is_check(statement)) else {
            return;
        };
        let copies = copies_of(self.accumulator, &body[check + 1..]);
        let Some(switch) = (check + 1..body.len())
            .find(|&position| self.kept_branch(&body[position], &copies).is_some())
        else {
            return;
        };
        if body[check + 1..switch].iter().any(|statement| self.assigns_accumulator(statement)) {
            return;
        }
        let kept = self.kept_branch(&body[switch], &copies).cloned().unwrap_or_default();
        body.splice(switch..=switch, kept);
        let mut rest = body.split_off(switch);
        if self.break_after_absorbing(&mut rest) && starts_kept {
            body.remove(check);
        }
        body.extend(rest);
    }

    fn is_check(&self, statement: &GoStatement) -> bool {
        matches!(statement, GoStatement::If { condition, then, otherwise }
            if condition == self.absorbed
                && matches!(then.as_slice(), [GoStatement::Break])
                && otherwise.is_empty())
    }

    fn kept_branch<'s>(
        &self,
        statement: &'s GoStatement,
        copies: &[String],
    ) -> Option<&'s Vec<GoStatement>> {
        let GoExpression::Binary {
            operator: GoBinaryOperator::Equal,
            left: tag,
            right: absorbed_tag,
        } = self.absorbed
        else {
            return None;
        };
        let GoStatement::Switch { value: Some(value), cases, default: Some(default) } = statement
        else {
            return None;
        };
        let [case] = cases.as_slice() else { return None };
        let reads_tag = match (value, tag.as_ref()) {
            (
                GoExpression::Field { value: read, name },
                GoExpression::Field { value: accumulator, name: tag_name },
            ) => {
                name == tag_name
                    && (read == accumulator
                        || matches!(read.as_ref(), GoExpression::Identifier(copy) if copies.contains(copy)))
            }
            _ => false,
        };
        if !reads_tag {
            return None;
        }
        match case.values.contains(absorbed_tag) {
            true => Some(&default.body),
            false => Some(&case.body),
        }
    }

    fn assigns_accumulator(&self, statement: &GoStatement) -> bool {
        let mut assigned = Assigned { accumulator: self.accumulator, found: false };
        assigned.statement(&mut statement.clone());
        assigned.found
    }

    fn is_absorbing(&self, value: &GoExpression) -> bool {
        value == self.value || kept_argument(self.value, value, self.placeholder).is_some()
    }

    fn break_after_absorbing(&self, block: &mut Vec<GoStatement>) -> bool {
        let mut position = 0;
        while position < block.len() {
            if self.assigns_accumulator(&block[position])
                && let Some(branches) = switch_as_branches(&block[position])
            {
                block[position] = branches;
            }
            match &mut block[position] {
                GoStatement::Assign { targets, values } if matches!(targets.as_slice(), [GoExpression::Identifier(target)] if target == self.accumulator) =>
                {
                    if !matches!(values.as_slice(), [value] if self.is_absorbing(value)) {
                        return false;
                    }
                    block.insert(position + 1, GoStatement::Break);
                    position += 2;
                    continue;
                }
                GoStatement::If { then, otherwise, .. } => {
                    if !self.break_after_absorbing(then) || !self.break_after_absorbing(otherwise) {
                        return false;
                    }
                }
                statement if self.assigns_accumulator(statement) => return false,
                _ => {}
            }
            position += 1;
        }
        true
    }
}

struct Assigned<'a> {
    accumulator: &'a str,
    found: bool,
}

impl Walk for Assigned<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Assign { targets, .. } = statement
            && targets.iter().any(|target| matches!(target, GoExpression::Identifier(name) if name == self.accumulator))
        {
            self.found = true;
        }
        go_traversal::statement(self, statement);
    }
}

fn copies_of(accumulator: &str, statements: &[GoStatement]) -> Vec<String> {
    let mut copies = vec![];
    for statement in statements {
        if let GoStatement::Define { names, values } = statement
            && let ([copy], [GoExpression::Identifier(copied)]) =
                (names.as_slice(), values.as_slice())
            && (copied == accumulator || copies.contains(copied))
        {
            copies.push(copy.clone());
        }
    }
    copies
}

fn switch_as_branches(statement: &GoStatement) -> Option<GoStatement> {
    let GoStatement::Switch { value: Some(value), cases, default: Some(default) } = statement
    else {
        return None;
    };
    let [case] = cases.as_slice() else { return None };
    if !is_pure_read(value) || case.values.is_empty() {
        return None;
    }
    let tests = case.values.iter().map(|tested| GoExpression::Binary {
        operator: GoBinaryOperator::Equal,
        left: Box::new(value.clone()),
        right: Box::new(tested.clone()),
    });
    let condition = tests
        .reduce(|left, right| GoExpression::Binary {
            operator: GoBinaryOperator::LogicalOr,
            left: Box::new(left),
            right: Box::new(right),
        })
        .expect("a case tests a value");
    let lined = |line: &Option<crate::syntax::SourceLine>, body: &[GoStatement]| {
        line.iter().cloned().map(GoStatement::Line).chain(body.iter().cloned()).collect()
    };
    Some(GoStatement::If {
        condition,
        then: lined(&case.line, &case.body),
        otherwise: lined(&default.line, &default.body),
    })
}

fn is_pure_read(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::Identifier(_) | GoExpression::Qualified { .. } | GoExpression::Integer(_) => {
            true
        }
        GoExpression::Field { value, .. } => is_pure_read(value),
        GoExpression::Index { value, index } => is_pure_read(value) && is_pure_read(index),
        _ => false,
    }
}
