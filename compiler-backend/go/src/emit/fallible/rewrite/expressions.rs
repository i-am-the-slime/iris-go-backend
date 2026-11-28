use super::{Rewrite, Split};
use crate::emit::fallible::survey::read_side;
use crate::emit::fallible::{Conversion, LEFT, converter, failure_test_of, nil, values};
use crate::emit::{call, identifier_expression};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoExpression, GoStatement};

impl Rewrite<'_> {
    /// The split local whose tag the scrutinee reads.
    pub(super) fn split_tag(&self, scrutinee: &GoExpression) -> Option<Split> {
        let GoExpression::Field { value, name } = scrutinee.unattributed() else { return None };
        let GoExpression::Identifier(local) = value.unattributed() else { return None };
        (name == "Tag").then(|| self.splits.get(local).cloned()).flatten()
    }

    fn fallible_call_name(&self, function: &GoExpression) -> Option<String> {
        match function.unattributed() {
            GoExpression::Identifier(name) => self.callable.get(name).cloned(),
            _ => None,
        }
    }

    /// The arguments of a call, the function literals it passes to parameters that return two
    /// results returning them.
    fn arguments(
        &mut self,
        function: &GoExpression,
        arguments: Vec<GoExpression>,
    ) -> Vec<GoExpression> {
        let slots = match function.unattributed() {
            GoExpression::Identifier(name) => self.conventions.parameters.get(name),
            _ => None,
        };
        let slots = slots.cloned().unwrap_or_default();
        let split = match function.unattributed() {
            GoExpression::Identifier(name) => self.conventions.split_parameters.get(name),
            _ => None,
        };
        let split = split.cloned().unwrap_or_default();
        let mut out = Vec::with_capacity(arguments.len());
        for (index, argument) in arguments.into_iter().enumerate() {
            match (slots.get(&index), split.get(&index)) {
                (Some(shape), _)
                    if matches!(argument.unattributed(), GoExpression::Function { .. }) =>
                {
                    out.push(self.converted_literal(argument, shape));
                }
                (_, Some(shape)) => {
                    let (value, failure) = self.passed_apart(argument, shape);
                    out.push(value);
                    out.push(failure);
                }
                _ => out.push(self.expression(argument)),
            }
        }
        out
    }

    pub(super) fn split_target(&self, target: &GoExpression) -> Option<Split> {
        match target.unattributed() {
            GoExpression::Identifier(local) => self.splits.get(local).cloned(),
            _ => None,
        }
    }

    /// An `Either` passed to a split parameter, as its value and its failure.
    pub(super) fn passed_apart(
        &mut self,
        argument: GoExpression,
        shape: &str,
    ) -> (GoExpression, GoExpression) {
        let either = &self.shapes[shape];
        if let GoExpression::Identifier(local) = argument.unattributed() {
            if let Some(split) = self.splits.get(local) {
                return (
                    identifier_expression(&split.value),
                    identifier_expression(&split.failure),
                );
            }
            let right = GoExpression::Field {
                value: Box::new(argument.clone()),
                name: either.right_field.clone(),
            };
            let converter = self.converter(shape, Conversion::Failure);
            return (right, call(identifier_expression(&converter), vec![argument]));
        }
        let (left, field) = either
            .construction(&argument)
            .expect("invariant violated: a split parameter is passed a local or a construction");
        let side = if left { &either.left } else { &either.right };
        let field = match field {
            Some(field) => self.expression(field),
            None => self.zeros.zero(side),
        };
        let either = &self.shapes[shape];
        match left {
            true => (self.zeros.zero(&either.right), self.failure(field, either)),
            false => (field, either.no_failure()),
        }
    }

    /// A function literal returning an `Either`, returning its two results instead.
    pub(super) fn converted_literal(&mut self, literal: GoExpression, shape: &str) -> GoExpression {
        match literal {
            GoExpression::Attributed { line, value } => GoExpression::Attributed {
                line,
                value: Box::new(self.converted_literal(*value, shape)),
            },
            GoExpression::Function { parameters, body, .. } => GoExpression::Function {
                parameters,
                result: Some(self.shapes[shape].results()),
                body: self.block(body, Some(shape)),
            },
            value => self.expression(value),
        }
    }

    /// The call of a fallible function the value is, with its arguments rewritten.
    pub(super) fn fallible_call(&mut self, value: GoExpression) -> Option<GoExpression> {
        match value {
            GoExpression::Attributed { line, value } => {
                let value = self.fallible_call(*value)?;
                Some(GoExpression::Attributed { line, value: Box::new(value) })
            }
            GoExpression::Call { function, arguments }
                if self.fallible_call_name(&function).is_some() =>
            {
                let arguments = self.arguments(&function, arguments);
                Some(GoExpression::Call { function, arguments })
            }
            _ => None,
        }
    }

    pub(super) fn converter(&mut self, shape: &str, conversion: Conversion) -> String {
        converter(self.converters, shape, conversion)
    }

    pub(super) fn expression(&mut self, value: GoExpression) -> GoExpression {
        match value {
            GoExpression::Field { value, name } => {
                if let GoExpression::Identifier(local) = value.unattributed()
                    && let Some(split) = self.splits.get(local)
                {
                    let shape = &self.shapes[&split.shape];
                    let side = match read_side(&name) {
                        Some((left, _)) => Some(left),
                        None if shape.shares_field() => None,
                        None if name == shape.right_field => Some(false),
                        None if name == shape.left_field => Some(true),
                        None => None,
                    };
                    if side == Some(false) {
                        return identifier_expression(&split.value);
                    }
                    if side == Some(true) {
                        return GoExpression::Field {
                            value: Box::new(identifier_expression(&split.failure)),
                            name: LEFT.into(),
                        };
                    }
                }
                GoExpression::Field { value: Box::new(self.expression(*value)), name }
            }
            GoExpression::Binary { operator, left, right } if matches!(operator, "==" | "!=") => {
                if let Some(test) = self.failure_test(operator, &left, &right) {
                    return test;
                }
                GoExpression::Binary {
                    operator,
                    left: Box::new(self.expression(*left)),
                    right: Box::new(self.expression(*right)),
                }
            }
            GoExpression::Call { function, mut arguments }
                if let GoExpression::Identifier(head) = function.unattributed()
                    && head.starts_with(values::LITERAL_MARK)
                    && arguments.len() == 1 =>
            {
                let GoExpression::Identifier(head) = function.unattributed() else {
                    unreachable!("invariant violated: a mark")
                };
                let shape = head[values::LITERAL_MARK.len()..].to_string();
                let literal = arguments.pop().expect("invariant violated: one literal");
                self.converted_literal(literal, &shape)
            }
            GoExpression::Call { function, arguments }
                if let Some(shape) = self.fallible_call_name(&function) =>
            {
                let arguments = self.arguments(&function, arguments);
                let converter = self.converter(&shape, Conversion::FromResults);
                call(
                    identifier_expression(&converter),
                    vec![GoExpression::Call { function, arguments }],
                )
            }
            GoExpression::Call { function, arguments }
                if matches!(function.unattributed(), GoExpression::Identifier(_)) =>
            {
                let arguments = self.arguments(&function, arguments);
                GoExpression::Call { function, arguments }
            }
            GoExpression::Function { parameters, result, body } => {
                let body = self.block(body, None);
                GoExpression::Function { parameters, result, body }
            }
            mut value => {
                struct Children<'a, 'r>(&'a mut Rewrite<'r>);
                impl Walk for Children<'_, '_> {
                    fn expression(&mut self, value: &mut GoExpression) {
                        let taken = std::mem::replace(value, nil());
                        *value = self.0.expression(taken);
                    }
                    fn block(&mut self, _: &mut Vec<GoStatement>) {}
                }
                go_traversal::expression(&mut Children(self), &mut value);
                value
            }
        }
    }

    /// `local.Tag == tag` of a split local, as a test of its failure.
    fn failure_test(
        &self,
        operator: &str,
        left: &GoExpression,
        right: &GoExpression,
    ) -> Option<GoExpression> {
        let (field, tag) = match self.split_tag(left) {
            Some(split) => (split, right),
            None => (self.split_tag(right)?, left),
        };
        let shape = &self.shapes[&field.shape];
        let is_left = shape.is_left_tag(tag)?;
        let failed = (operator == "==") == is_left;
        Some(failure_test_of(&field.failure, failed))
    }
}
