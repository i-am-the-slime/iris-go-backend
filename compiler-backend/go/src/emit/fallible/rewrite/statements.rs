use super::{Rewrite, Split};
use crate::emit::fallible::syntax::joined_results;
use crate::emit::fallible::{Conversion, EitherShape, LEFT, failure_test_of, is_no_failure};
use crate::emit::index_arrays::is_line;
use crate::emit::{call, identifier_expression};
use crate::syntax::{GoCase, GoDefault, GoExpression, GoStatement};

impl Rewrite<'_> {
    pub(super) fn block(
        &mut self,
        statements: Vec<GoStatement>,
        own: Option<&str>,
    ) -> Vec<GoStatement> {
        let mut out = Vec::with_capacity(statements.len());
        for statement in statements {
            self.statement(statement, own, &mut out);
        }
        out
    }

    fn statement(&mut self, statement: GoStatement, own: Option<&str>, out: &mut Vec<GoStatement>) {
        match statement {
            GoStatement::Define { names, mut values }
                if names.len() == 1
                    && values.len() == 1
                    && let Some(split) = self.splits.get(&names[0]).cloned() =>
            {
                let source = values.pop().expect("invariant violated: one value");
                self.store(&split, source, true, out);
            }
            GoStatement::Variable { name, value, .. }
                if let Some(split) = self.splits.get(&name).cloned() =>
            {
                match value {
                    Some(source) => self.store(&split, source, true, out),
                    None => {
                        let shape = &self.shapes[&split.shape];
                        out.push(GoStatement::Variable {
                            name: split.value.clone(),
                            type_: shape.right.clone(),
                            value: None,
                        });
                        out.push(GoStatement::Variable {
                            name: split.failure.clone(),
                            type_: shape.failure_type(),
                            value: None,
                        });
                    }
                }
            }
            GoStatement::Assign { targets, mut values }
                if targets.len() == 1
                    && values.len() == 1
                    && let GoExpression::Identifier(target) = targets[0].unattributed()
                    && let Some(split) = self.splits.get(target).cloned() =>
            {
                let source = values.pop().expect("invariant violated: one value");
                self.store(&split, source, false, out);
            }
            GoStatement::Assign { targets, values }
                if targets.len() == values.len()
                    && targets.len() > 1
                    && targets.iter().any(|target| self.split_target(target).is_some()) =>
            {
                let mut stored_targets = Vec::with_capacity(targets.len() + 1);
                let mut stored_values = Vec::with_capacity(values.len() + 1);
                for (target, value) in targets.into_iter().zip(values) {
                    let Some(split) = self.split_target(&target) else {
                        stored_targets.push(self.expression(target));
                        stored_values.push(self.expression(value));
                        continue;
                    };
                    let (value, failure) = self.passed_apart(value, &split.shape);
                    stored_targets.push(identifier_expression(&split.value));
                    stored_targets.push(identifier_expression(&split.failure));
                    stored_values.push(value);
                    stored_values.push(failure);
                }
                out.push(GoStatement::Assign { targets: stored_targets, values: stored_values });
            }
            GoStatement::Return(Some(value)) if let Some(own) = own => {
                let returned = self.returned(value, own);
                out.push(returned);
            }
            GoStatement::Switch { value: Some(scrutinee), cases, default }
                if let Some(split) = self.split_tag(&scrutinee) =>
            {
                self.switch_on_failure(&split, cases, default, own, out);
            }
            GoStatement::Expression(value) => {
                let value = match self.fallible_call(value.clone()) {
                    Some(call) => call,
                    None => self.expression(value),
                };
                out.push(GoStatement::Expression(value));
            }
            GoStatement::Defer(value) => {
                let value = match self.fallible_call(value.clone()) {
                    Some(call) => call,
                    None => self.expression(value),
                };
                out.push(GoStatement::Defer(value));
            }
            GoStatement::Define { names, mut values }
                if let ([local], [_]) = (names.as_slice(), values.as_slice())
                    && let Some(shape) = self.callable.get(local).cloned()
                    && matches!(values[0].unattributed(), GoExpression::Function { .. }) =>
            {
                let literal = values.pop().expect("invariant violated: one value");
                values.push(self.converted_literal(literal, &shape));
                out.push(GoStatement::Define { names, values });
            }
            statement => out.push(self.nested(statement, own)),
        }
    }

    /// The statement with its expressions and blocks rewritten.
    fn nested(&mut self, statement: GoStatement, own: Option<&str>) -> GoStatement {
        match statement {
            GoStatement::Define { names, values } => GoStatement::Define {
                names,
                values: values.into_iter().map(|value| self.expression(value)).collect(),
            },
            GoStatement::Variable { name, type_, value } => GoStatement::Variable {
                name,
                type_,
                value: value.map(|value| self.expression(value)),
            },
            GoStatement::Assign { targets, values } => GoStatement::Assign {
                targets: targets.into_iter().map(|target| self.expression(target)).collect(),
                values: values.into_iter().map(|value| self.expression(value)).collect(),
            },
            GoStatement::Expression(value) => GoStatement::Expression(self.expression(value)),
            GoStatement::Defer(value) => GoStatement::Defer(self.expression(value)),
            GoStatement::Return(value) => {
                GoStatement::Return(value.map(|value| self.expression(value)))
            }
            GoStatement::If { condition, then, otherwise } => GoStatement::If {
                condition: self.expression(condition),
                then: self.block(then, own),
                otherwise: self.block(otherwise, own),
            },
            GoStatement::Switch { value, cases, default } => {
                let value = value.map(|value| self.expression(value));
                let cases = cases.into_iter().map(|case| {
                    let values = case.values.into_iter().map(|value| self.expression(value));
                    let values = values.collect();
                    GoCase { values, body: self.block(case.body, own), line: case.line }
                });
                let cases = cases.collect();
                GoStatement::Switch {
                    value,
                    cases,
                    default: default.map(|default| GoDefault {
                        covers: default.covers,
                        body: self.block(default.body, own),
                        line: default.line,
                    }),
                }
            }
            GoStatement::IfAssert { name, value, type_, then } => GoStatement::IfAssert {
                name,
                value: self.expression(value),
                type_,
                then: self.block(then, own),
            },
            GoStatement::Loop(body) => GoStatement::Loop(self.block(body, own)),
            GoStatement::LabeledLoop { label, body } => {
                GoStatement::LabeledLoop { label, body: self.block(body, own) }
            }
            GoStatement::Range { index, element, iterable, body } => GoStatement::Range {
                index,
                element,
                iterable: self.expression(iterable),
                body: self.block(body, own),
            },
            GoStatement::Counting { variable, start, end, body } => GoStatement::Counting {
                variable,
                start: self.expression(start),
                end: self.expression(end),
                body: self.block(body, own),
            },
            GoStatement::CountingDown { variable, start, body } => GoStatement::CountingDown {
                variable,
                start: self.expression(start),
                body: self.block(body, own),
            },
            statement @ (GoStatement::Continue
            | GoStatement::Break
            | GoStatement::BreakTo(_)
            | GoStatement::Line(_)) => statement,
        }
    }

    /// Stores an `Either` into a split local's two locals.
    fn store(
        &mut self,
        split: &Split,
        source: GoExpression,
        declare: bool,
        out: &mut Vec<GoStatement>,
    ) {
        let shape = &self.shapes[&split.shape];
        let value = identifier_expression(&split.value);
        let failure = identifier_expression(&split.failure);
        if let Some((_, joined_value, joined_failure)) = joined_results(&source) {
            if (&joined_value, &joined_failure) != (&split.value, &split.failure) {
                let values = vec![
                    identifier_expression(&joined_value),
                    identifier_expression(&joined_failure),
                ];
                out.push(match declare {
                    true => GoStatement::Define {
                        names: vec![split.value.clone(), split.failure.clone()],
                        values,
                    },
                    false => GoStatement::Assign { targets: vec![value, failure], values },
                });
            }
            return;
        }
        if let Some(source) = self.fallible_call(source.clone()) {
            out.push(match declare {
                true => GoStatement::Define {
                    names: vec![split.value.clone(), split.failure.clone()],
                    values: vec![source],
                },
                false => {
                    GoStatement::Assign { targets: vec![value, failure], values: vec![source] }
                }
            });
            return;
        }
        let (left, field) = shape
            .construction(&source)
            .expect("invariant violated: a split local holds a call or a construction");
        let side = if left { &shape.left } else { &shape.right };
        let field = match field {
            Some(field) => self.expression(field),
            None => self.zeros.zero(side),
        };
        let (right_type, left_type) = (shape.right.clone(), shape.failure_type());
        match (left, declare) {
            (false, true) => {
                out.push(match crate::emit::operators::is_untyped_constant(field.unattributed()) {
                    true => GoStatement::Variable {
                        name: split.value.clone(),
                        type_: right_type,
                        value: Some(field),
                    },
                    false => GoStatement::Define {
                        names: vec![split.value.clone()],
                        values: vec![field],
                    },
                });
                out.push(GoStatement::Variable {
                    name: split.failure.clone(),
                    type_: left_type,
                    value: None,
                });
            }
            (true, true) => {
                out.push(GoStatement::Variable {
                    name: split.value.clone(),
                    type_: right_type,
                    value: None,
                });
                out.push(GoStatement::Define {
                    names: vec![split.failure.clone()],
                    values: vec![self.failure(field, shape)],
                });
            }
            (false, false) if self.holds_either(split) => {
                out.push(GoStatement::Assign { targets: vec![value], values: vec![field] });
                out.push(GoStatement::Assign {
                    targets: vec![failure],
                    values: vec![shape.no_failure()],
                });
            }
            (false, false) => out.push(GoStatement::Assign {
                targets: vec![value, failure],
                values: vec![field, shape.no_failure()],
            }),
            (true, false) => {
                let stored = self.failure(field, shape);
                if stored != failure {
                    out.push(GoStatement::Assign { targets: vec![failure], values: vec![stored] });
                }
            }
        }
    }

    /// The failure of a `Left` value: the failure it was read from, when it is one, else a new one.
    pub(super) fn failure(&self, value: GoExpression, shape: &EitherShape) -> GoExpression {
        if let GoExpression::Field { value: from, name } = value.unattributed()
            && name == LEFT
            && let GoExpression::Identifier(from) = from.unattributed()
            && self.failure_types.get(from) == Some(&shape.failure)
        {
            return identifier_expression(from);
        }
        shape.failed_with(value)
    }

    /// The `return` of a fallible function, returning its two results.
    fn returned(&mut self, value: GoExpression, own: &str) -> GoStatement {
        let shape = &self.shapes[own];
        if let GoExpression::Identifier(local) = value.unattributed()
            && let Some(split) = self.splits.get(local)
        {
            return GoStatement::Return(Some(GoExpression::Results(vec![
                identifier_expression(&split.value),
                identifier_expression(&split.failure),
            ])));
        }
        if let Some(call) = self.fallible_call(value.clone()) {
            return GoStatement::Return(Some(call));
        }
        let value = match value.unattributed() {
            GoExpression::Identifier(local)
                if let Some(built) = self.constructions.get(local)
                    && shape.construction(built).is_some() =>
            {
                built.clone()
            }
            _ => value,
        };
        if let Some((left, field)) = shape.construction(&value) {
            let side = if left { &shape.left } else { &shape.right };
            let field = match field {
                Some(field) => self.expression(field),
                None => self.zeros.zero(side),
            };
            let results = match left {
                true => vec![self.zeros.zero(&shape.right), self.failure(field, shape)],
                false => vec![field, shape.no_failure()],
            };
            return GoStatement::Return(Some(GoExpression::Results(results)));
        }
        let value = self.expression(value);
        let converter = self.converter(own, Conversion::Results);
        GoStatement::Return(Some(call(identifier_expression(&converter), vec![value])))
    }

    /// A `switch` on a split local's tag, as an `if` on its failure.
    fn switch_on_failure(
        &mut self,
        split: &Split,
        cases: Vec<GoCase>,
        default: Option<GoDefault>,
        own: Option<&str>,
        out: &mut Vec<GoStatement>,
    ) {
        let shape = &self.shapes[&split.shape];
        let mut left = None;
        let mut right = None;
        for case in cases {
            let is_left = case.values.iter().find_map(|value| shape.is_left_tag(value));
            let body = with_line(case.line, case.body);
            match is_left {
                Some(true) => left = Some(body),
                _ => right = Some(body),
            }
        }
        if let Some(default) = default {
            let body = with_line(default.line, default.body);
            if left.is_none() {
                left = Some(body);
            } else {
                right = Some(body);
            }
        }
        let left = self.block(left.unwrap_or_default(), own);
        let right = self.block(right.unwrap_or_default(), own);
        if let Some(moved) = moved_results(&left, &right, split) {
            out.extend(
                left.into_iter().filter(|statement| matches!(statement, GoStatement::Line(_))),
            );
            out.push(moved);
            return;
        }
        let failed = failure_test_of(&split.failure, true);
        if breaks_out(&left) || breaks_out(&right) {
            out.push(GoStatement::Switch {
                value: None,
                cases: vec![GoCase { values: vec![failed], body: left, line: None }],
                default: Some(GoDefault { covers: vec![], body: right, line: None }),
            });
            return;
        }
        out.push(GoStatement::If { condition: failed, then: left, otherwise: right });
    }
}

/// The body after a directive naming the line, when there is one.
fn with_line(line: Option<crate::syntax::SourceLine>, body: Vec<GoStatement>) -> Vec<GoStatement> {
    line.map(GoStatement::Line).into_iter().chain(body).collect()
}

/// `value, err = v, e` for the branches of a `switch` on the split `v, e` that store a `Left`'s
/// failure and a `Right`'s value unchanged: `err = e` and `value, err = v, F{}`.
fn moved_results(left: &[GoStatement], right: &[GoStatement], from: &Split) -> Option<GoStatement> {
    let only = |statements: &[GoStatement]| -> Option<(Vec<GoExpression>, Vec<GoExpression>)> {
        let mut rest = statements.iter().filter(|statement| !is_line(statement));
        let first_two = (rest.next(), rest.next());
        let (Some(GoStatement::Assign { targets, values }), None) = first_two else { return None };
        Some((targets.clone(), values.clone()))
    };
    let (failure_targets, failure_values) = only(left)?;
    let (targets, values) = only(right)?;
    let is = |value: &GoExpression, name: &str| matches!(value.unattributed(), GoExpression::Identifier(found) if found == name);
    let ([failure_target], [failure], [value_target, other_failure_target], [value, nothing]) = (
        failure_targets.as_slice(),
        failure_values.as_slice(),
        targets.as_slice(),
        values.as_slice(),
    ) else {
        return None;
    };
    (is(failure, &from.failure)
        && is(value, &from.value)
        && is_no_failure(nothing)
        && failure_target == other_failure_target)
        .then(|| GoStatement::Assign {
            targets: vec![value_target.clone(), failure_target.clone()],
            values: vec![identifier_expression(&from.value), identifier_expression(&from.failure)],
        })
}

/// Whether a `break` in the statements leaves the `switch` around them.
fn breaks_out(statements: &[GoStatement]) -> bool {
    statements.iter().any(|statement| match statement {
        GoStatement::Break => true,
        GoStatement::If { then, otherwise, .. } => breaks_out(then) || breaks_out(otherwise),
        GoStatement::IfAssert { then, .. } => breaks_out(then),
        _ => false,
    })
}
