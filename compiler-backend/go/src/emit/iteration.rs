use smol_str::SmolStr;

use super::ownership::{Carried, owned_snocs};
use super::{Emitter, Mode, Sink, binary, call, identifier, identifier_expression, uses_local};
use crate::error::GoResult;
use crate::foreign::Iteration;
use crate::mono::{Expression, ExpressionKind, FunctionId, Local};
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement, GoType};

enum Callback<'e> {
    Inline { parameters: Vec<&'e Local>, body: &'e Expression },
    Direct { function: GoExpression, callee: FunctionId, leading: Vec<GoExpression> },
}

enum Found<'e> {
    Inline { parameters: Vec<&'e Local>, body: &'e Expression },
    Direct { function: GoExpression, callee: FunctionId, leading: &'e [Expression] },
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn iteration(
        &mut self,
        iteration: Iteration,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Option<GoExpression>> {
        let (position, arity) = match iteration {
            Iteration::FoldLeft | Iteration::FoldRight | Iteration::MapWithIndex => (0, 2),
            Iteration::Map | Iteration::Filter | Iteration::Any | Iteration::All => (0, 1),
            Iteration::Bind => (1, 1),
            Iteration::FindIndex | Iteration::FindLastIndex => (2, 1),
        };
        let folds_unit = matches!(iteration, Iteration::FoldLeft | Iteration::FoldRight)
            && self.is_unit(monotype);
        if folds_unit {
            return Ok(None);
        }
        if self.effect_after(arguments[position].monotype, arity) {
            return Ok(None);
        }
        let Some(found) = self.callback(&arguments[position], arity) else { return Ok(None) };
        let callback = match found {
            Found::Inline { parameters, body } => Callback::Inline { parameters, body },
            Found::Direct { function, callee, leading } => {
                let mut values = vec![];
                for argument in leading {
                    let value = self.value(argument, out)?;
                    values.push(self.hoist(value, "argument", out));
                }
                Callback::Direct { function, callee, leading: values }
            }
        };
        let value = match iteration {
            Iteration::FoldLeft | Iteration::FoldRight => {
                self.fold(iteration, callback, &arguments[1], &arguments[2], monotype, out)?
            }
            Iteration::Map | Iteration::MapWithIndex => {
                self.map(iteration, callback, &arguments[1], monotype, out)?
            }
            Iteration::Filter => self.filter(callback, &arguments[1], monotype, out)?,
            Iteration::Any | Iteration::All => {
                self.search(iteration, callback, &arguments[1], out)?
            }
            Iteration::Bind => self.bind(callback, &arguments[0], monotype, out)?,
            Iteration::FindIndex | Iteration::FindLastIndex => {
                self.find_index(iteration, callback, &arguments[3], monotype, out)?
            }
        };
        Ok(Some(value))
    }

    fn callback<'e>(&self, function: &'e Expression, arity: usize) -> Option<Found<'e>> {
        let (head, leading): (&Expression, &[Expression]) = match &function.kind {
            ExpressionKind::Apply { function, arguments } => (function, arguments),
            _ => (function, &[]),
        };
        match &head.kind {
            ExpressionKind::Function(id) => {
                let callee = self.program.function(*id);
                let direct = callee.parameters.len() == leading.len() + arity
                    && !self.lazy_constants.contains(id);
                let function = identifier_expression(&self.function_names[id.0 as usize]);
                direct.then_some(Found::Direct { function, callee: *id, leading })
            }
            ExpressionKind::Lambda { .. } if leading.is_empty() => {
                let mut parameters = vec![];
                let mut body = function;
                while parameters.len() < arity {
                    let ExpressionKind::Lambda { parameters: more, body: inner } = &body.kind
                    else {
                        return None;
                    };
                    if parameters.len() + more.len() > arity {
                        return None;
                    }
                    parameters.extend(more.iter());
                    body = inner;
                }
                Some(Found::Inline { parameters, body })
            }
            _ => None,
        }
    }

    fn loop_variable(&mut self, callback: &Callback<'_>, position: usize, base: &str) -> String {
        match callback {
            Callback::Inline { parameters, body } => {
                let parameter = parameters[position];
                if uses_local(body, parameter.id) { self.bind_local(parameter) } else { "_".into() }
            }
            Callback::Direct { .. } => self.temporary(base),
        }
    }

    fn apply_callback(
        &mut self,
        callback: &Callback<'_>,
        arguments: Vec<GoExpression>,
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        match callback {
            Callback::Inline { body, .. } => self.sink(body, Mode::Value, sink, out),
            Callback::Direct { function, leading, .. } => {
                let mut all = leading.clone();
                all.extend(arguments);
                self.deliver(call(function.clone(), all), result, sink, out)
            }
        }
    }

    fn callback_value(
        &mut self,
        callback: &Callback<'_>,
        arguments: Vec<GoExpression>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        match callback {
            Callback::Inline { body, .. } => self.value(body, out),
            Callback::Direct { function, leading, .. } => {
                let mut all = leading.clone();
                all.extend(arguments);
                Ok(call(function.clone(), all))
            }
        }
    }

    fn fold(
        &mut self,
        iteration: Iteration,
        callback: Callback<'_>,
        initial: &Expression,
        array: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let (accumulator_position, element_position) = match iteration {
            Iteration::FoldLeft => (0, 1),
            _ => (1, 0),
        };
        let initial = self.value(initial, out)?;
        let array = self.value(array, out)?;
        let array = self.hoist(array, "array", out);
        let accumulator = self.temporary("accumulator");
        out.push(self.define(accumulator.clone(), initial, monotype)?);
        let callback = self.owning_callback(callback, accumulator_position, &accumulator, out);
        let owned = self.owned_arrays(&callback, accumulator_position, monotype);
        for (field, _) in &owned {
            out.push(self.clip(&accumulator, field.as_ref()));
        }
        let owned_nodes: Vec<*const Expression> = owned
            .iter()
            .flat_map(|(_, nodes)| nodes.iter().map(|node| std::ptr::from_ref(*node)))
            .collect();
        self.owned_snocs.extend(owned_nodes.iter().copied());
        let saved = self.tail_loop.take();
        let parameter = self.loop_variable(&callback, accumulator_position, "accumulated");
        let element = self.loop_variable(&callback, element_position, "element");
        let mut body = vec![];
        if parameter != "_" {
            body.push(GoStatement::Define {
                names: vec![parameter.clone()],
                values: vec![identifier_expression(&accumulator)],
            });
        }
        let mut arguments = vec![identifier_expression(&parameter)];
        arguments.insert(element_position, identifier_expression(&element));
        let outcome = self.apply_callback(
            &callback,
            arguments,
            monotype,
            Sink::Assign(accumulator.clone()),
            &mut body,
        );
        self.tail_loop = saved;
        for node in &owned_nodes {
            self.owned_snocs.remove(node);
        }
        outcome?;
        let statement = match iteration {
            Iteration::FoldLeft => {
                GoStatement::Range { index: None, element, iterable: array, body }
            }
            _ => {
                let index = self.temporary("index");
                if element != "_" {
                    let indexed = GoExpression::Index {
                        value: Box::new(array.clone()),
                        index: Box::new(identifier_expression(&index)),
                    };
                    body.insert(
                        0,
                        GoStatement::Define { names: vec![element], values: vec![indexed] },
                    );
                }
                let last = binary("-", length(array), GoExpression::Integer(1));
                GoStatement::CountingDown { variable: index, start: last, body }
            }
        };
        out.push(statement);
        Ok(identifier_expression(&accumulator))
    }

    fn owning_callback<'e>(
        &mut self,
        callback: Callback<'e>,
        accumulator_position: usize,
        accumulator: &str,
        out: &mut Vec<GoStatement>,
    ) -> Callback<'e> {
        let Callback::Direct { callee, leading, .. } = &callback else { return callback };
        let position = leading.len() + accumulator_position;
        let owned = self.owned_parameter_snocs(self.program.function(*callee), position);
        if owned.is_empty() {
            return callback;
        }
        for (field, _) in &owned {
            out.push(self.clip(accumulator, field.as_ref()));
        }
        let Callback::Direct { callee, leading, .. } = callback else { unreachable!() };
        let function = identifier_expression(&self.owning_variant_name(callee, position));
        Callback::Direct { function, callee, leading }
    }

    fn owned_arrays<'e>(
        &self,
        callback: &Callback<'e>,
        accumulator_position: usize,
        monotype: MonotypeId,
    ) -> Vec<(Option<SmolStr>, Vec<&'e Expression>)> {
        let Callback::Inline { parameters, body } = callback else { return vec![] };
        let accumulator = parameters[accumulator_position].id;
        self.carried_arrays(monotype)
            .into_iter()
            .filter_map(|field| {
                let carried = Carried { accumulator, field: field.as_ref() };
                let nodes = owned_snocs(carried, body)?;
                (!nodes.is_empty()).then_some((field, nodes))
            })
            .collect()
    }

    pub(super) fn carried_arrays(&self, monotype: MonotypeId) -> Vec<Option<SmolStr>> {
        match self.monotypes.get(monotype) {
            Monotype::Array(_) => vec![None],
            Monotype::Record(fields) => fields
                .iter()
                .filter(|field| matches!(self.monotypes.get(field.monotype), Monotype::Array(_)))
                .map(|field| Some(field.label.clone()))
                .collect(),
            _ => vec![],
        }
    }

    pub(super) fn clip(&mut self, accumulator: &str, field: Option<&SmolStr>) -> GoStatement {
        let carried = match field {
            Some(label) => super::field(identifier_expression(accumulator), &identifier(label)),
            None => identifier_expression(accumulator),
        };
        self.imports.insert("slices".into());
        let clip = GoExpression::Qualified { package: "slices".into(), name: "Clip".into() };
        GoStatement::Assign {
            targets: vec![carried.clone()],
            values: vec![call(clip, vec![carried])],
        }
    }

    fn map(
        &mut self,
        iteration: Iteration,
        callback: Callback<'_>,
        array: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let array = self.value(array, out)?;
        let array = self.hoist(array, "array", out);
        let mapped_type = self.go_type(monotype)?;
        let mapped = self.temporary("mapped");
        let allocation = call(
            identifier_expression("make"),
            vec![GoExpression::Type(mapped_type), length(array.clone())],
        );
        out.push(GoStatement::Define { names: vec![mapped.clone()], values: vec![allocation] });
        let saved = self.tail_loop.take();
        let (index, element) = match iteration {
            Iteration::MapWithIndex => {
                let index = self.loop_variable(&callback, 0, "index");
                (index, self.loop_variable(&callback, 1, "element"))
            }
            _ => ("_".to_string(), self.loop_variable(&callback, 0, "element")),
        };
        let slot = if index == "_" { self.temporary("index") } else { self.temporary("slot") };
        let mut body = vec![];
        let mut arguments = vec![identifier_expression(&element)];
        if iteration == Iteration::MapWithIndex && index != "_" {
            body.push(GoStatement::Define {
                names: vec![index.clone()],
                values: vec![GoExpression::Conversion {
                    type_: GoType::Named("int32".into()),
                    value: Box::new(identifier_expression(&slot)),
                }],
            });
            arguments.insert(0, identifier_expression(&index));
        }
        let outcome = self.callback_value(&callback, arguments, &mut body);
        self.tail_loop = saved;
        let value = outcome?;
        body.push(GoStatement::Assign {
            targets: vec![GoExpression::Index {
                value: Box::new(identifier_expression(&mapped)),
                index: Box::new(identifier_expression(&slot)),
            }],
            values: vec![value],
        });
        out.push(GoStatement::Range { index: Some(slot), element, iterable: array, body });
        Ok(identifier_expression(&mapped))
    }

    fn filter(
        &mut self,
        callback: Callback<'_>,
        array: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let array = self.value(array, out)?;
        let array = self.hoist(array, "array", out);
        let kept_type = self.go_type(monotype)?;
        let kept = self.temporary("kept");
        out.push(GoStatement::Define {
            names: vec![kept.clone()],
            values: vec![GoExpression::Composite { type_: kept_type, fields: vec![] }],
        });
        let saved = self.tail_loop.take();
        let element = match &callback {
            Callback::Inline { parameters, .. } => self.bind_local(parameters[0]),
            Callback::Direct { .. } => self.temporary("element"),
        };
        let mut body = vec![];
        let outcome =
            self.callback_value(&callback, vec![identifier_expression(&element)], &mut body);
        self.tail_loop = saved;
        let condition = outcome?;
        let appended = call(
            identifier_expression("append"),
            vec![identifier_expression(&kept), identifier_expression(&element)],
        );
        body.push(GoStatement::If {
            condition,
            then: vec![GoStatement::Assign {
                targets: vec![identifier_expression(&kept)],
                values: vec![appended],
            }],
            otherwise: vec![],
        });
        out.push(GoStatement::Range { index: None, element, iterable: array, body });
        Ok(identifier_expression(&kept))
    }

    fn search(
        &mut self,
        iteration: Iteration,
        callback: Callback<'_>,
        array: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let array = self.value(array, out)?;
        let array = self.hoist(array, "array", out);
        let looking_for = iteration == Iteration::Any;
        let found = self.temporary(if looking_for { "found" } else { "every" });
        out.push(GoStatement::Define {
            names: vec![found.clone()],
            values: vec![GoExpression::Boolean(!looking_for)],
        });
        let saved = self.tail_loop.take();
        let element = self.loop_variable(&callback, 0, "element");
        let mut body = vec![];
        let outcome =
            self.callback_value(&callback, vec![identifier_expression(&element)], &mut body);
        self.tail_loop = saved;
        let condition = outcome?;
        let condition = if looking_for {
            condition
        } else {
            GoExpression::Unary { operator: "!", operand: Box::new(condition) }
        };
        body.push(GoStatement::If {
            condition,
            then: vec![
                GoStatement::Assign {
                    targets: vec![identifier_expression(&found)],
                    values: vec![GoExpression::Boolean(looking_for)],
                },
                GoStatement::Break,
            ],
            otherwise: vec![],
        });
        out.push(GoStatement::Range { index: None, element, iterable: array, body });
        Ok(identifier_expression(&found))
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    fn bind(
        &mut self,
        callback: Callback<'_>,
        array: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let array = self.value(array, out)?;
        let array = self.hoist(array, "array", out);
        let bound_type = self.go_type(monotype)?;
        let bound = self.temporary("bound");
        out.push(GoStatement::Define {
            names: vec![bound.clone()],
            values: vec![GoExpression::Composite { type_: bound_type, fields: vec![] }],
        });
        let saved = self.tail_loop.take();
        let element = self.loop_variable(&callback, 0, "element");
        let mut body = vec![];
        let outcome =
            self.callback_value(&callback, vec![identifier_expression(&element)], &mut body);
        self.tail_loop = saved;
        let produced = outcome?;
        let appended = call(
            identifier_expression("append"),
            vec![identifier_expression(&bound), GoExpression::Spread(Box::new(produced))],
        );
        body.push(GoStatement::Assign {
            targets: vec![identifier_expression(&bound)],
            values: vec![appended],
        });
        out.push(GoStatement::Range { index: None, element, iterable: array, body });
        Ok(identifier_expression(&bound))
    }

    fn find_index(
        &mut self,
        iteration: Iteration,
        callback: Callback<'_>,
        array: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let array = self.value(array, out)?;
        let array = self.hoist(array, "array", out);
        let (data, nothing) = self.constructor_named(monotype, "Nothing")?;
        let (_, just) = self.constructor_named(monotype, "Just")?;
        let found = self.temporary("found");
        let absent = self.construct(&data, nothing, vec![])?;
        out.push(GoStatement::Define { names: vec![found.clone()], values: vec![absent] });
        let saved = self.tail_loop.take();
        let element = self.loop_variable(&callback, 0, "element");
        let index = self.temporary("index");
        let mut body = vec![];
        let ascending = iteration == Iteration::FindIndex;
        if !ascending && element != "_" {
            let indexed = GoExpression::Index {
                value: Box::new(array.clone()),
                index: Box::new(identifier_expression(&index)),
            };
            body.push(GoStatement::Define { names: vec![element.clone()], values: vec![indexed] });
        }
        let outcome =
            self.callback_value(&callback, vec![identifier_expression(&element)], &mut body);
        self.tail_loop = saved;
        let condition = outcome?;
        let position = GoExpression::Conversion {
            type_: GoType::Named("int32".into()),
            value: Box::new(identifier_expression(&index)),
        };
        let present = self.construct(&data, just, vec![position])?;
        body.push(GoStatement::If {
            condition,
            then: vec![
                GoStatement::Assign {
                    targets: vec![identifier_expression(&found)],
                    values: vec![present],
                },
                GoStatement::Break,
            ],
            otherwise: vec![],
        });
        let statement = if ascending {
            GoStatement::Range { index: Some(index), element, iterable: array, body }
        } else {
            let last = binary("-", length(array), GoExpression::Integer(1));
            GoStatement::CountingDown { variable: index, start: last, body }
        };
        out.push(statement);
        Ok(identifier_expression(&found))
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn uncurried_callback(
        &mut self,
        function: &Expression,
        arity: usize,
        perform: bool,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let mut parameter_monotypes = vec![];
        let mut result = function.monotype;
        for _ in 0..arity {
            let (parameter, rest) = self
                .monotypes
                .function_parts(result)
                .expect("invariant violated: an uncurried callback takes its arguments");
            parameter_monotypes.push(parameter);
            result = rest;
        }
        let effect = self.monotypes.effect_result(result);
        let (mode, result) = match effect {
            Some(inner) if perform => (Mode::Perform, inner),
            _ => (Mode::Value, result),
        };
        let delayed = effect.is_some() && !perform;
        let result_type = self.go_result(result)?;
        let saved = self.tail_loop.take();
        let mut parameters = vec![];
        let mut body = vec![];
        let outcome = match self.callback(function, arity) {
            Some(Found::Inline { parameters: locals, body: lambda_body }) => {
                for local in &locals {
                    let name = if uses_local(lambda_body, local.id) {
                        self.bind_local(local)
                    } else {
                        "_".to_string()
                    };
                    parameters.push((name, self.go_type(local.monotype)?));
                }
                self.sink(lambda_body, mode, Sink::Return, &mut body)
            }
            None if !delayed && arity > 1 && self.arity(function.monotype) == arity => {
                let value = self.value(function, out)?;
                self.tail_loop = saved;
                return Ok(value);
            }
            found => {
                let mut arguments = vec![];
                for &monotype in &parameter_monotypes {
                    let name = self.temporary("argument");
                    arguments.push(identifier_expression(&name));
                    parameters.push((name, self.go_type(monotype)?));
                }
                let applied = match found {
                    Some(Found::Direct { function: name, leading, .. })
                        if leading.is_empty() && !delayed =>
                    {
                        self.tail_loop = saved;
                        return Ok(name);
                    }
                    Some(Found::Direct { function: name, leading, .. }) => {
                        let mut values = vec![];
                        for argument in leading {
                            let value = self.value(argument, out)?;
                            values.push(self.hoist(value, "argument", out));
                        }
                        values.extend(arguments);
                        call(name, values)
                    }
                    _ => {
                        let value = self.value(function, out)?;
                        let function_value = self.hoist(value, "function", out);
                        let callable = self.value_callable(function_value, function.monotype);
                        self.apply_arguments(callable, arguments, &mut body)?
                    }
                };
                let applied = if delayed {
                    let inner = effect.unwrap_or(result);
                    let performed = if self.is_unit(inner) {
                        GoStatement::Expression(applied)
                    } else {
                        GoStatement::Return(Some(applied))
                    };
                    let inner = self.go_result(inner)?;
                    GoExpression::Function {
                        parameters: vec![],
                        result: inner,
                        body: vec![performed],
                    }
                } else {
                    applied
                };
                self.deliver(applied, result, Sink::Return, &mut body)
            }
        };
        self.tail_loop = saved;
        outcome?;
        if let Some(GoStatement::Return(None)) = body.last() {
            body.pop();
        }
        Ok(GoExpression::Function { parameters, result: result_type, body })
    }
}

fn length(array: GoExpression) -> GoExpression {
    call(identifier_expression("len"), vec![array])
}
