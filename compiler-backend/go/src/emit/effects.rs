use super::{
    Emitter, Mode, Sink, call, field, field_name, identifier_expression, mutable, reference_type,
    unit_value, uses_local,
};
use crate::error::{GoError, GoResult};
use crate::foreign::{Foreign, GoFunction, GoPackage};
use crate::monomorphic::{Expression, ExpressionKind, Local};
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement, GoType};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn perform_foreign(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        match foreign {
            Foreign::EffectWhile | Foreign::EffectUntil => {
                return self.effect_loop(foreign, arguments, result, sink, out);
            }
            Foreign::EffectFor => return self.effect_for(arguments, result, sink, out),
            Foreign::WithMutex => return self.with_mutex(arguments, result, sink, out),
            Foreign::MutexNew => {
                self.imports.insert("sync".into());
                let mutex = call(
                    identifier_expression("new"),
                    vec![GoExpression::Type(GoType::Named("sync.Mutex".into()))],
                );
                return self.deliver(mutex, result, sink, out);
            }
            Foreign::MakeAff => {
                let performed = self.make_aff(arguments, out)?;
                return self.deliver(performed, result, sink, out);
            }
            Foreign::ForkFiber | Foreign::NewFiber => {
                let action = self.value(&arguments[1], out)?;
                let action = self.unit_valued(action, arguments[1].monotype, out)?;
                let handle = match foreign {
                    Foreign::ForkFiber => {
                        let immediate = self.value(&arguments[0], out)?;
                        let fork = GoFunction { package: GoPackage::Aff, name: "ForkFiber" };
                        call(self.performing(fork), vec![immediate, action])
                    }
                    _ => {
                        let new = GoFunction { package: GoPackage::Aff, name: "NewFiber" };
                        call(self.performing(new), vec![action])
                    }
                };
                if let Sink::Discard = sink {
                    out.push(GoStatement::Expression(handle));
                    return Ok(());
                }
                let handle = self.hoist(handle, "fiber", out);
                let record = self.fiber_record(handle, result, out)?;
                return self.deliver(record, result, sink, out);
            }
            Foreign::NewSupervisedFiber => {
                let action = self.value(&arguments[1], out)?;
                let action = self.unit_valued(action, arguments[1].monotype, out)?;
                let new = GoFunction { package: GoPackage::Aff, name: "NewSupervisedFiber" };
                let handle = self.temporary("fiber");
                let supervisor = self.temporary("supervisor");
                out.push(GoStatement::Define {
                    names: vec![handle.clone(), supervisor.clone()],
                    values: vec![call(self.performing(new), vec![action])],
                });
                let fiber = self.record_field_monotype(result, "fiber");
                let fiber = self.fiber_record(identifier_expression(&handle), fiber, out)?;
                let supervised = GoExpression::Composite {
                    type_: GoType::Named(self.record_name(result)?),
                    fields: vec![
                        (Some(field_name("fiber")), fiber),
                        (Some(field_name("supervisor")), identifier_expression(&supervisor)),
                    ],
                };
                return self.deliver(supervised, result, sink, out);
            }
            Foreign::AssocArray => {
                let array = self.value(&arguments[0], out)?;
                let associated = self.associated_elements(result)?;
                let map = GoFunction { package: GoPackage::Direct, name: "MapWithIndex" };
                let elements = GoExpression::Unary { operator: "*", operand: Box::new(array) };
                let associated = call(self.go_function(map), vec![associated, elements]);
                return self.deliver(associated, result, sink, out);
            }
            // A foreign with arguments performs its effect when called; an effect value
            // without arguments is a function that performs it.
            Foreign::Project { arity, .. } => {
                let called = self.project_call(foreign, arguments, out)?;
                let called = if arity == 0 { call(called, vec![]) } else { called };
                let crossing = self.project_crossing(foreign);
                let performed = self.out_of_convention(called, result, crossing, out)?;
                return self.deliver(performed, result, sink, out);
            }
            Foreign::Perform { function, .. }
                if function.package == GoPackage::Array
                    && mutable::ACCESSES.contains(&function.name) =>
            {
                return self.mutable_access(function.name, arguments, result, sink, out);
            }
            Foreign::Perform { function, boundary, .. } => {
                let values = self.boundary_arguments(arguments, boundary, result, false, out)?;
                self.performs(function);
                let function = self.boundary_function(function, boundary, result)?;
                let mut performed = call(function, values);
                if boundary.thunk {
                    performed = call(performed, vec![]);
                }
                if boundary.record_result {
                    let record = self.record_from_results(performed, result, out)?;
                    return self.deliver(record, result, sink, out);
                }
                return self.deliver(performed, result, sink, out);
            }
            _ => {}
        }
        let mut values = self.values(arguments, out)?;
        match foreign {
            Foreign::ReferenceNew => {
                let value_type = self.go_type(arguments[0].monotype)?;
                self.declare_reference();
                let reference = GoExpression::Address(Box::new(GoExpression::Composite {
                    type_: reference_type(value_type),
                    fields: vec![(Some("Value".into()), values.remove(0))],
                }));
                self.deliver(reference, result, sink, out)
            }
            Foreign::ReferenceRead => {
                let value = field(values.remove(0), "Value");
                self.deliver(value, result, sink, out)
            }
            Foreign::ReferenceWrite => {
                let value = values.remove(0);
                let reference = values.remove(0);
                out.push(GoStatement::Assign {
                    targets: vec![field(reference, "Value")],
                    values: vec![value],
                });
                self.deliver(unit_value(), result, sink, out)
            }
            Foreign::ReferenceModify => {
                let reference = values.remove(1);
                let reference = self.hoist(reference, "reference", out);
                let modified = self.temporary("modified");
                if let ExpressionKind::Lambda { parameters, body } = &arguments[0].kind
                    && let [state] = parameters.as_slice()
                {
                    let name = self.bind_local(state);
                    out.push(GoStatement::Define {
                        names: vec![name],
                        values: vec![field(reference.clone(), "Value")],
                    });
                    self.sink(body, Mode::Value, Sink::Define(modified.clone()), out)?;
                } else {
                    let update = values.remove(0);
                    out.push(GoStatement::Define {
                        names: vec![modified.clone()],
                        values: vec![call(update, vec![field(reference.clone(), "Value")])],
                    });
                }
                out.push(GoStatement::Assign {
                    targets: vec![field(reference, "Value")],
                    values: vec![field(identifier_expression(&modified), &field_name("state"))],
                });
                let value = field(identifier_expression(&modified), &field_name("value"));
                self.deliver(value, result, sink, out)
            }
            Foreign::Throw => {
                out.push(GoStatement::Expression(call(
                    identifier_expression("panic"),
                    vec![values.remove(0)],
                )));
                if let Sink::Define(name) = sink
                    && !self.is_unit(result)
                {
                    let type_ = self.go_type(result)?;
                    out.push(GoStatement::Variable { name, type_, value: None });
                }
                Ok(())
            }
            Foreign::MutableArrayNew => {
                let array_type = self.go_type(result)?;
                let GoType::Pointer(slice) = array_type else {
                    unreachable!("invariant violated: a mutable array is a slice pointer")
                };
                let empty = GoExpression::Composite { type_: *slice, fields: vec![] };
                self.deliver(GoExpression::Address(Box::new(empty)), result, sink, out)
            }
            Foreign::ReferenceWriteThrough => {
                let value = self.hoist(values.remove(0), "written", out);
                let reference = values.remove(0);
                out.push(GoStatement::Assign {
                    targets: vec![field(reference, "Value")],
                    values: vec![value.clone()],
                });
                self.deliver(value, result, sink, out)
            }
            Foreign::EffectPure => self.deliver(values.remove(0), result, sink, out),
            _ => Err(GoError::Unsupported {
                definition: self.current_definition(),
                state: crate::error::UnsupportedState::Construct {
                    construct: "unsaturated effect primitives",
                },
            }),
        }
    }

    /// Notes that the emitted code calls `function` to run an effect.
    fn performs(&mut self, function: GoFunction) {
        self.effects.insert((function.package.name().into(), function.name.into()));
    }

    /// `function`, which the emitted code calls to run an effect.
    pub(super) fn performing(&mut self, function: GoFunction) -> GoExpression {
        self.performs(function);
        self.go_function(function)
    }

    pub(super) fn unit_valued(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if !self.has_unit_result(monotype) {
            return Ok(value);
        }
        let value = match value {
            GoExpression::Function { .. } => value,
            value => self.shared(value, "function", out),
        };
        let (parameter, result) = self.callable_parts(monotype);
        let mut parameters = vec![];
        let mut arguments = vec![];
        if let Some(parameter) = parameter {
            let base = self.value_base(parameter);
            let name = self.temporary(&base);
            parameters.push((name.clone(), self.go_type(parameter)?));
            arguments.push(identifier_expression(&name));
        }
        let mut body = vec![];
        let applied = match parameter {
            Some(_) => {
                let callable = self.value_callable(value, monotype);
                self.apply_arguments(callable, arguments, &mut body)?
            }
            None => call(value, arguments),
        };
        if self.is_unit(result) {
            body.push(GoStatement::Expression(applied));
            body.push(GoStatement::Return(Some(unit_value())));
        } else {
            let adapted = self.unit_valued(applied, result, &mut body)?;
            body.push(GoStatement::Return(Some(adapted)));
        }
        let result = self.unit_valued_type(result)?;
        Ok(GoExpression::Function { parameters, result: Some(result), body })
    }

    fn make_aff(
        &mut self,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let register = &arguments[0];
        let (callback, _) = self
            .monotypes
            .function_parts(register.monotype)
            .expect("invariant violated: makeAff registers a function");
        let (either, _) = self
            .monotypes
            .function_parts(callback)
            .expect("invariant violated: makeAff's callback is a function");
        let is_left = self.projection(either, "Left", None)?;
        let from_left = self.projection(either, "Left", Some(0))?;
        let from_right = self.projection(either, "Right", Some(0))?;
        let register = self.value(register, out)?;
        let function =
            self.performing(GoFunction { package: GoPackage::Aff, name: "MakeAffDirect" });
        Ok(call(function, vec![is_left, from_left, from_right, register]))
    }

    fn fiber_record(
        &mut self,
        handle: GoExpression,
        record: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let join = self.record_field_monotype(record, "join");
        let (callback, _) =
            self.monotypes.function_parts(join).expect("invariant violated: join takes a callback");
        let (either, _) = self
            .monotypes
            .function_parts(callback)
            .expect("invariant violated: join's callback is a function");
        let kill = self.record_field_monotype(record, "kill");
        let killing = self.monotypes.result_after(kill, 1);
        let (kill_callback, _) = self
            .monotypes
            .function_parts(killing)
            .expect("invariant violated: kill takes a callback");
        let (unit_either, _) = self
            .monotypes
            .function_parts(kill_callback)
            .expect("invariant violated: kill's callback is a function");
        let on_complete = self.record_field_monotype(record, "onComplete");
        let (completion, _) = self
            .monotypes
            .function_parts(on_complete)
            .expect("invariant violated: onComplete takes a record");
        let left = self.constructor_function(either, "Left")?;
        let right = self.constructor_function(either, "Right")?;
        let (unit_data, unit_right) = self.constructor_named(unit_either, "Right")?;
        let unit_right = self.construct(&unit_data, unit_right, vec![unit_value()])?;
        let handler = self.record_field_projection(completion, "handler")?;
        let function =
            self.go_function(GoFunction { package: GoPackage::Aff, name: "FiberFields" });
        let fields = call(function, vec![handle, left, right, unit_right, handler]);
        self.record_from_results(fields, record, out)
    }

    fn effect_loop(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let saved = self.tail_loop.take();
        let mut body = vec![];
        let condition = self.temporary("continuing");
        let (test, action) = match foreign {
            Foreign::EffectWhile => (&arguments[0], Some(&arguments[1])),
            _ => (&arguments[0], None),
        };
        self.sink(test, Mode::Perform, Sink::Define(condition.clone()), &mut body)?;
        let condition = identifier_expression(&condition);
        let stop = match foreign {
            Foreign::EffectWhile => {
                GoExpression::Unary { operator: "!", operand: Box::new(condition) }
            }
            _ => condition,
        };
        body.push(GoStatement::If {
            condition: stop,
            then: vec![GoStatement::Break],
            otherwise: vec![],
        });
        if let Some(action) = action {
            self.sink(action, Mode::Perform, Sink::Discard, &mut body)?;
        }
        self.tail_loop = saved;
        out.push(GoStatement::Loop(body));
        self.deliver(unit_value(), result, sink, out)
    }

    /// `withMutex mutex action` holds the lock while the action runs and releases
    /// it even when the action throws. As the last action of a Go function the lock
    /// is released by `defer`; elsewhere the critical section is its own closure.
    fn with_mutex(
        &mut self,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let mutex = self.value(&arguments[0], out)?;
        let mutex = self.hoist(mutex, "mutex", out);
        let lock = call(field(mutex.clone(), "Lock"), vec![]);
        let unlock = call(field(mutex, "Unlock"), vec![]);
        let saved = self.tail_loop.take();
        let outcome = if let Sink::Return = sink {
            out.push(GoStatement::Expression(lock));
            out.push(GoStatement::Defer(unlock));
            self.sink(&arguments[1], Mode::Perform, Sink::Return, out)
        } else {
            let mut body = vec![GoStatement::Expression(lock), GoStatement::Defer(unlock)];
            self.sink(&arguments[1], Mode::Perform, Sink::Return, &mut body).and_then(|()| {
                if let Some(GoStatement::Return(None)) = body.last() {
                    body.pop();
                }
                let result_type = self.go_result(result)?;
                let section =
                    GoExpression::Function { parameters: vec![], result: result_type, body };
                self.deliver(call(section, vec![]), result, sink, out)
            })
        };
        self.tail_loop = saved;
        outcome
    }

    pub(super) fn collect_each(
        &mut self,
        array: &Expression,
        element: &Local,
        body: &Expression,
        collected: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let Monotype::Array(value) = *self.monotypes.get(collected) else {
            unreachable!("invariant violated: an effectful map collects an array")
        };
        let array = self.value(array, out)?;
        let array = self.hoist(array, "array", out);
        let name = self.temporary("collected");
        let length = call(identifier_expression("len"), vec![array.clone()]);
        let allocation = GoExpression::Type(self.go_type(collected)?);
        let allocation = call(identifier_expression("make"), vec![allocation, length]);
        out.push(GoStatement::Define { names: vec![name.clone()], values: vec![allocation] });
        let element_name =
            if uses_local(body, element.id) { self.bind_local(element) } else { "_".to_string() };
        let saved = self.tail_loop.take();
        let mut statements = vec![];
        let index = if self.is_unit(value) {
            self.sink(body, Mode::Perform, Sink::Discard, &mut statements).map(|()| None)
        } else {
            let performed = self.temporary("value");
            let index = self.temporary("index");
            let sink = Sink::Define(performed.clone());
            self.sink(body, Mode::Perform, sink, &mut statements).map(|()| {
                let slot = GoExpression::Index {
                    value: Box::new(identifier_expression(&name)),
                    index: Box::new(identifier_expression(&index)),
                };
                statements.push(GoStatement::Assign {
                    targets: vec![slot],
                    values: vec![identifier_expression(&performed)],
                });
                Some(index)
            })
        };
        self.tail_loop = saved;
        out.push(GoStatement::Range {
            index: index?,
            element: element_name,
            iterable: array,
            body: statements,
        });
        Ok(identifier_expression(&name))
    }

    fn effect_for(
        &mut self,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let start = self.value(&arguments[0], out)?;
        // `index := 0` would be a Go int; the counter is a PureScript Int.
        let start = self.typed_constant(start, arguments[0].monotype)?;
        let end = self.value(&arguments[1], out)?;
        let end = self.hoist(end, "end", out);
        let saved = self.tail_loop.take();
        let mut body = vec![];
        let variable = if let ExpressionKind::Lambda { parameters, body: lambda_body } =
            &arguments[2].kind
            && let [parameter] = parameters.as_slice()
        {
            let variable = self.bind_local(parameter);
            self.sink(lambda_body, Mode::Perform, Sink::Discard, &mut body)?;
            variable
        } else {
            let action = self.value(&arguments[2], out)?;
            let action = self.hoist(action, "action", out);
            let variable = self.temporary("index");
            let performed = call(action, vec![identifier_expression(&variable)]);
            body.push(GoStatement::Expression(performed));
            variable
        };
        self.tail_loop = saved;
        out.push(GoStatement::Counting { variable, start, end, body });
        self.deliver(unit_value(), result, sink, out)
    }
}
