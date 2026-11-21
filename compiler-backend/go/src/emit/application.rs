use std::sync::Arc;

use super::{Emitter, call, identifier_expression, uses_local};
use crate::error::GoResult;
use crate::mono::{Expression, ExpressionKind, FunctionId, Local};
use crate::monotype::MonotypeId;
use crate::naming::UNNAMED_VALUE;
use crate::syntax::{GoExpression, GoStatement, GoType};

pub(super) struct Callable {
    pub function: GoExpression,
    pub monotype: MonotypeId,
    pub arity: usize,
    pub names: Vec<String>,
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn arity(&self, monotype: MonotypeId) -> usize {
        if self.monotypes.function_parts(monotype).is_none() {
            return 1;
        }
        self.arities.of(monotype)
    }

    pub(super) fn leading_arrows(
        &self,
        mut monotype: MonotypeId,
        count: usize,
    ) -> (Vec<MonotypeId>, MonotypeId) {
        let mut parameters = Vec::with_capacity(count);
        for _ in 0..count {
            let Some((parameter, result)) = self.monotypes.function_parts(monotype) else { break };
            parameters.push(parameter);
            monotype = result;
        }
        (parameters, monotype)
    }

    /// The name an argument to a parameter takes: the parameter's, else its type's.
    fn argument_base(&mut self, names: &[String], position: usize, monotype: MonotypeId) -> String {
        match names.get(position) {
            Some(name) => self.local_base(name, monotype),
            None => self.value_base(monotype),
        }
    }

    pub(super) fn known_callable(&self, id: FunctionId, monotype: MonotypeId) -> Callable {
        let function = self.program.function(id);
        Callable {
            function: identifier_expression(self.function_reference(id)),
            monotype,
            arity: function.parameters.len(),
            names: function
                .parameters
                .iter()
                .map(|parameter| parameter.name.to_string())
                .collect(),
        }
    }

    pub(super) fn value_callable(&self, function: GoExpression, monotype: MonotypeId) -> Callable {
        Callable { function, monotype, arity: self.arity(monotype), names: vec![] }
    }

    pub(super) fn apply_arguments(
        &mut self,
        mut callable: Callable,
        mut arguments: Vec<GoExpression>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        loop {
            if arguments.len() < callable.arity {
                return self.partial(callable, arguments, out);
            }
            let rest = arguments.split_off(callable.arity);
            let result = self.monotypes.result_after(callable.monotype, callable.arity);
            let called = call(callable.function, arguments);
            if rest.is_empty() {
                return Ok(called);
            }
            arguments = rest;
            callable = self.value_callable(called, result);
        }
    }

    fn partial(
        &mut self,
        callable: Callable,
        supplied: Vec<GoExpression>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let function = self.shared(callable.function, "function", out);
        let mut captured = Vec::with_capacity(supplied.len());
        for (position, value) in supplied.into_iter().enumerate() {
            let value = match value {
                value @ GoExpression::Function { .. } => value,
                value => {
                    let (parameters, _) = self.leading_arrows(callable.monotype, position + 1);
                    let base = match parameters.get(position) {
                        Some(&parameter) => self.argument_base(&callable.names, position, parameter),
                        None => UNNAMED_VALUE.into(),
                    };
                    self.shared(value, &base, out)
                }
            };
            captured.push(value);
        }
        let target = self.monotypes.result_after(callable.monotype, captured.len());
        let callable = Callable { function, ..callable };
        self.closure(callable, captured, target)
    }

    pub(super) fn closure(
        &mut self,
        callable: Callable,
        supplied: Vec<GoExpression>,
        target: MonotypeId,
    ) -> GoResult<GoExpression> {
        let arity = self.arity(target);
        let (parameter_monotypes, result) = self.leading_arrows(target, arity);
        let mut parameters = Vec::with_capacity(arity);
        let mut arguments = supplied;
        for monotype in parameter_monotypes {
            let base = self.argument_base(&callable.names, arguments.len(), monotype);
            let name = self.temporary(&base);
            parameters.push((name.clone(), self.go_type(monotype)?));
            arguments.push(identifier_expression(&name));
        }
        let mut body = vec![];
        let applied = self.apply_arguments(callable, arguments, &mut body)?;
        let returned = self.monotypes.effect_result(result).unwrap_or(result);
        if self.is_unit(returned) {
            body.push(GoStatement::Expression(applied));
        } else {
            body.push(GoStatement::Return(Some(applied)));
        }
        let result = self.go_result(returned)?;
        Ok(GoExpression::Function { parameters, result, body })
    }

    pub(super) fn function_value(
        &mut self,
        id: FunctionId,
        monotype: MonotypeId,
    ) -> GoResult<GoExpression> {
        let function = self.program.function(id);
        let name = self.function_reference(id).to_string();
        if self.lazy_constants.contains(&id) {
            return Ok(call(identifier_expression(&name), vec![]));
        }
        if function.parameters.is_empty() || function.parameters.len() == self.arity(monotype) {
            return Ok(identifier_expression(&name));
        }
        let callable = self.known_callable(id, monotype);
        self.closure(callable, vec![], monotype)
    }

    /// The function a lambda only passes its parameters on to, `\x y -> f x y`, when Go gives
    /// that function the lambda's own type and it is a value already: the lambda is `f` itself,
    /// not a closure that looks `f` up at every call. A coercion that keeps the Go type is no
    /// coercion here.
    pub(super) fn eta_reduced<'e>(
        &mut self,
        monotype: MonotypeId,
        parameters: &[Local],
        body: &'e Expression,
    ) -> GoResult<Option<&'e Expression>> {
        let (parameters, body) = self.merged_lambda(monotype, parameters, body);
        let ExpressionKind::Apply { function, arguments } = &self.same_representation(body)?.kind
        else {
            return Ok(None);
        };
        if parameters.is_empty()
            || parameters.len() != self.arity(monotype)
            || arguments.len() != parameters.len()
        {
            return Ok(None);
        }
        for (argument, parameter) in arguments.iter().zip(&parameters) {
            let argument = self.same_representation(argument)?;
            if !matches!(argument.kind, ExpressionKind::Local(id) if id == parameter.id) {
                return Ok(None);
            }
        }
        let function = self.same_representation(function)?;
        let captures_parameter =
            parameters.iter().any(|parameter| uses_local(function, parameter.id));
        if captures_parameter
            || !self.is_evaluated(function)
            || !self.same_go_type(function.monotype, monotype)?
        {
            return Ok(None);
        }
        Ok(Some(function))
    }

    /// The expression under the coercions that leave its Go type as it is.
    fn same_representation<'e>(
        &mut self,
        mut expression: &'e Expression,
    ) -> GoResult<&'e Expression> {
        while let ExpressionKind::Coerce(inner) = &expression.kind
            && self.same_go_type(inner.monotype, expression.monotype)?
        {
            expression = inner;
        }
        Ok(expression)
    }

    /// Whether reading the expression's value does no work and cannot fail: a local that has its
    /// value, a global that is not computed on first use, or a field of such a record. Reading it
    /// when a closure would have been made is then the same as reading it at every call.
    fn is_evaluated(&self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Local(id) => !self.uninitialized_locals.contains(id),
            ExpressionKind::Function(id) => !self.lazy_constants.contains(id),
            ExpressionKind::Access { record, .. } => self.is_evaluated(record),
            _ => false,
        }
    }

    pub(super) fn lambda(
        &mut self,
        monotype: MonotypeId,
        parameters: &[Local],
        body: &Expression,
    ) -> GoResult<GoExpression> {
        let arity = self.arity(monotype);
        if parameters.len() < arity
            && let ExpressionKind::Lambda { parameters: inner, body: inner_body } = &body.kind
        {
            let mut merged = parameters.to_vec();
            merged.extend(inner.iter().cloned());
            return self.lambda(monotype, &merged, inner_body);
        }
        let taken = parameters.len().min(arity);
        let (taken, rest) = parameters.split_at(taken);
        let mut go_parameters = Vec::with_capacity(arity);
        for parameter in taken {
            let name = if super::uses_local(body, parameter.id) {
                self.bind_local(parameter)
            } else {
                "_".to_string()
            };
            go_parameters.push((name, self.go_type(parameter.monotype)?));
        }
        let saved = self.tail_loop.take();
        let mut statements = vec![];
        let after = self.monotypes.result_after(monotype, taken.len());
        let result_monotype;
        if !rest.is_empty() {
            result_monotype = after;
            let inner = self.lambda(after, rest, body)?;
            statements.push(GoStatement::Return(Some(inner)));
        } else if taken.len() < arity {
            let (extra, result) = self.leading_arrows(after, arity - taken.len());
            let (callable, mut values) = match &body.kind {
                ExpressionKind::Apply { function, arguments } => {
                    self.application(function, arguments, extra.len(), &mut statements)?
                }
                ExpressionKind::Function(_) => self.application(body, &[], 0, &mut statements)?,
                _ => {
                    let function = self.value(body, &mut statements)?;
                    (self.value_callable(function, body.monotype), vec![])
                }
            };
            for monotype in extra {
                let base = self.argument_base(&callable.names, values.len(), monotype);
                let name = self.temporary(&base);
                go_parameters.push((name.clone(), self.go_type(monotype)?));
                values.push(identifier_expression(&name));
            }
            let applied = self.apply_arguments(callable, values, &mut statements)?;
            result_monotype = self.monotypes.effect_result(result).unwrap_or(result);
            if self.is_unit(result_monotype) {
                statements.push(GoStatement::Expression(applied));
            } else {
                statements.push(GoStatement::Return(Some(applied)));
            }
        } else {
            let mode = if self.monotypes.effect_result(body.monotype).is_some() {
                super::Mode::Perform
            } else {
                super::Mode::Value
            };
            result_monotype = self.monotypes.effect_result(body.monotype).unwrap_or(body.monotype);
            self.sink(body, mode, super::Sink::Return, &mut statements)?;
        }
        self.tail_loop = saved;
        if let Some(GoStatement::Return(None)) = statements.last() {
            statements.pop();
        }
        let result = self.go_result(result_monotype)?;
        Ok(GoExpression::Function { parameters: go_parameters, result, body: statements })
    }

    pub(super) fn argument_groups(&self, record: MonotypeId, label: &str) -> Option<Arc<[usize]>> {
        let fields = self.monotypes.uncurried_fields.get(&record)?;
        fields.iter().find(|(field, _)| field == label).map(|(_, groups)| Arc::clone(groups))
    }

    pub(super) fn grouped_value(
        &mut self,
        value: &Expression,
        groups: &[usize],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if let [arity] = groups {
            return self.uncurried_callback(value, *arity, true, out);
        }
        let function = self.value(value, out)?;
        let function = self.shared(function, "function", out);
        self.grouped_from_curried(function, value.monotype, groups)
    }

    fn grouped_from_curried(
        &mut self,
        function: GoExpression,
        monotype: MonotypeId,
        groups: &[usize],
    ) -> GoResult<GoExpression> {
        let Some((&size, rest)) = groups.split_first() else { return Ok(function) };
        let (parameters, after) = self.fresh_parameters(monotype, size)?;
        let mut called = function;
        for (name, _) in &parameters {
            called = call(called, vec![identifier_expression(name)]);
        }
        let (body, result) = if rest.is_empty() {
            self.final_call(called, after)?
        } else {
            let inner = self.grouped_from_curried(called, after, rest)?;
            let inner_type = function_type(&inner);
            (vec![GoStatement::Return(Some(inner))], Some(inner_type))
        };
        Ok(GoExpression::Function { parameters, result, body })
    }

    pub(super) fn curried_from_groups(
        &mut self,
        function: GoExpression,
        monotype: MonotypeId,
        groups: &[usize],
    ) -> GoResult<GoExpression> {
        let total = groups.iter().sum();
        let (parameters, after) = self.fresh_parameters(monotype, total)?;
        let mut called = function;
        let mut at = 0;
        for &size in groups {
            let arguments = parameters[at..at + size].iter();
            called = call(called, arguments.map(|(name, _)| identifier_expression(name)).collect());
            at += size;
        }
        let (mut body, mut result) = self.final_call(called, after)?;
        let mut built = None;
        for parameter in parameters.into_iter().rev() {
            if let Some(inner) = built.take() {
                result = Some(function_type(&inner));
                body = vec![GoStatement::Return(Some(inner))];
            }
            let layer = GoExpression::Function {
                parameters: vec![parameter],
                result: result.clone(),
                body: std::mem::take(&mut body),
            };
            built = Some(layer);
        }
        Ok(built.unwrap_or(GoExpression::Function { parameters: vec![], result, body }))
    }

    fn fresh_parameters(
        &mut self,
        monotype: MonotypeId,
        count: usize,
    ) -> GoResult<(Vec<(String, GoType)>, MonotypeId)> {
        let mut parameters = Vec::with_capacity(count);
        let mut current = monotype;
        for _ in 0..count {
            let (parameter, result) = self
                .monotypes
                .function_parts(current)
                .expect("invariant violated: grouped arguments are the function's parameters");
            let base = self.value_base(parameter);
            let name = self.temporary(&base);
            parameters.push((name, self.go_type(parameter)?));
            current = result;
        }
        Ok((parameters, current))
    }

    fn final_call(
        &mut self,
        called: GoExpression,
        result: MonotypeId,
    ) -> GoResult<(Vec<GoStatement>, Option<GoType>)> {
        let returned = self.monotypes.effect_result(result).unwrap_or(result);
        let statement = match self.is_unit(returned) {
            true => GoStatement::Expression(called),
            false => GoStatement::Return(Some(called)),
        };
        Ok((vec![statement], self.go_result(returned)?))
    }

    pub(super) fn curried_callback(
        &mut self,
        function: GoExpression,
        monotype: MonotypeId,
        arrows: usize,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let curried = (0..arrows).all(|position| {
            let layer = self.monotypes.result_after(monotype, position);
            self.arity(layer) == 1
        });
        if curried {
            return Ok(function);
        }
        let function = self.shared(function, "function", out);
        let callable = self.value_callable(function, monotype);
        self.curried_layer(callable, vec![], monotype, arrows)
    }

    fn curried_layer(
        &mut self,
        callable: Callable,
        mut supplied: Vec<GoExpression>,
        monotype: MonotypeId,
        arrows: usize,
    ) -> GoResult<GoExpression> {
        let (parameter, result) = self
            .monotypes
            .function_parts(monotype)
            .expect("invariant violated: a curried callback has its declared arrows");
        let base = self.value_base(parameter);
        let name = self.temporary(&base);
        let parameter_type = self.go_type(parameter)?;
        supplied.push(identifier_expression(&name));
        let mut body = vec![];
        let result_type = if arrows == 1 {
            let applied = self.apply_arguments(callable, supplied, &mut body)?;
            let returned = self.monotypes.effect_result(result).unwrap_or(result);
            if self.is_unit(returned) {
                body.push(GoStatement::Expression(applied));
            } else {
                body.push(GoStatement::Return(Some(applied)));
            }
            self.go_result(returned)?
        } else {
            let inner = self.curried_layer(callable, supplied, result, arrows - 1)?;
            let GoExpression::Function { parameters, result: inner_result, .. } = &inner else {
                unreachable!("invariant violated: a curried layer is a function")
            };
            let inner_type = GoType::Function {
                parameters: parameters.iter().map(|(_, type_)| type_.clone()).collect(),
                result: inner_result.clone().map(Box::new),
            };
            body.push(GoStatement::Return(Some(inner)));
            Some(inner_type)
        };
        Ok(GoExpression::Function {
            parameters: vec![(name, parameter_type)],
            result: result_type,
            body,
        })
    }
}

fn function_type(function: &GoExpression) -> GoType {
    let GoExpression::Function { parameters, result, .. } = function else {
        unreachable!("invariant violated: a grouped layer is a function")
    };
    GoType::Function {
        parameters: parameters.iter().map(|(_, type_)| type_.clone()).collect(),
        result: result.clone().map(Box::new),
    }
}
