use super::{Emitter, call, identifier, identifier_expression};
use crate::error::GoResult;
use crate::mono::{Expression, ExpressionKind, FunctionId, Local};
use crate::monotype::MonotypeId;
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

    pub(super) fn known_callable(&self, id: FunctionId, monotype: MonotypeId) -> Callable {
        let function = self.program.function(id);
        Callable {
            function: identifier_expression(&self.function_names[id.0 as usize]),
            monotype,
            arity: function.parameters.len(),
            names: function
                .parameters
                .iter()
                .map(|parameter| identifier(&parameter.name))
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
                    let base = callable.names.get(position).map_or("argument", String::as_str);
                    self.shared(value, base, out)
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
            let base = callable.names.get(arguments.len()).map_or("argument", String::as_str);
            let name = self.temporary(base);
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
        let name = self.function_names[id.0 as usize].clone();
        if self.lazy_constants.contains(&id) {
            return Ok(call(identifier_expression(&name), vec![]));
        }
        if function.parameters.is_empty() || function.parameters.len() == self.arity(monotype) {
            return Ok(identifier_expression(&name));
        }
        let callable = self.known_callable(id, monotype);
        self.closure(callable, vec![], monotype)
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
                let base = callable.names.get(values.len()).map_or("argument", String::as_str);
                let name = self.temporary(base);
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
        let name = self.temporary("argument");
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
