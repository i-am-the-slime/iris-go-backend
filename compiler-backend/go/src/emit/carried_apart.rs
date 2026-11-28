use super::conditions::negated;
use super::ownership::Place;
use super::{Emitter, conjunction, field, identifier_expression};
use crate::error::GoResult;
use crate::go_traversal::{self, Walk};
use crate::monomorphic::{Pattern, PatternKind};
use crate::syntax::{GoExpression, GoStatement};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn carried_apart(
        &mut self,
        looped: GoStatement,
        places: &[&Place],
        absorbing: Option<&Pattern>,
        accumulator: &str,
    ) -> GoResult<Vec<GoStatement>> {
        let ([Place::Constructor { constructor, index: 0, go_field }], Some(absorbing)) =
            (places, absorbing)
        else {
            return Ok(vec![looped]);
        };
        let PatternKind::Constructor { data, constructor: absorbed, .. } = &absorbing.kind else {
            return Ok(vec![looped]);
        };
        let layout = self.data_layout(data)?;
        if absorbed == constructor
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
