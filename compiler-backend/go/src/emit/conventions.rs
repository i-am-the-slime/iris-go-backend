//! How values cross into and out of foreign code: the conventions of Go packages' functions.

use super::application::Callable;
use super::{Direction, Emitter, binary, call, identifier_expression, returning};
use crate::error::GoResult;
use crate::foreign::{Boundary, GoFunction, GoPackage, Spelled};
use crate::mono::Expression;
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement, GoType};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn convention_type(&mut self, monotype: MonotypeId) -> GoResult<Option<GoType>> {
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Int => Some(GoType::Int),
            Monotype::Array(element) => {
                self.convention_type(element)?.map(|element| GoType::Slice(Box::new(element)))
            }
            // A project's foreign package cannot name the struct generated for a record, so a
            // record crosses as the JavaScript object it is there: a Foreign holding an object
            // table.
            Monotype::Record(_) => Some(GoType::Any),
            Monotype::Nullable(element) => {
                self.convention_type(element)?.map(|element| GoType::Pointer(Box::new(element)))
            }
            Monotype::Effect(result) => self.convention_type(result)?.map(|result| {
                GoType::Function { parameters: vec![], result: Some(Box::new(result)) }
            }),
            Monotype::Function(argument, result) => {
                let effect = self.monotypes.effect_result(result);
                let differs = effect.is_some()
                    || self.arity(monotype) > 1
                    || self.convention_type(argument)?.is_some()
                    || self.convention_type(result)?.is_some();
                if !differs {
                    return Ok(None);
                }
                let argument = self.convention_or_native(argument)?;
                let result = match effect {
                    Some(inner) => {
                        let inner = self.convention_result(inner)?;
                        Some(GoType::Function { parameters: vec![], result: inner.map(Box::new) })
                    }
                    None => self.convention_result(result)?,
                };
                Some(GoType::Function { parameters: vec![argument], result: result.map(Box::new) })
            }
            _ => None,
        })
    }

    pub(super) fn convention_or_native(&mut self, monotype: MonotypeId) -> GoResult<GoType> {
        match self.convention_type(monotype)? {
            Some(type_) => Ok(type_),
            None => self.go_type(monotype),
        }
    }

    pub(super) fn convention_result(&mut self, monotype: MonotypeId) -> GoResult<Option<GoType>> {
        if self.is_unit(monotype) {
            return Ok(None);
        }
        Ok(Some(self.convention_or_native(monotype)?))
    }

    pub(super) fn in_convention(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        self.convert_convention(value, monotype, Direction::ToConvention, out)
    }

    pub(super) fn out_of_convention(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        self.convert_convention(value, monotype, Direction::FromConvention, out)
    }

    pub(super) fn convert_convention(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        direction: Direction,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if self.convention_type(monotype)?.is_none() {
            return Ok(value);
        }
        let (source, target) = match direction {
            Direction::ToConvention => {
                (self.go_type(monotype)?, self.convention_or_native(monotype)?)
            }
            Direction::FromConvention => {
                (self.convention_or_native(monotype)?, self.go_type(monotype)?)
            }
        };
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Int => GoExpression::Conversion { type_: target, value: Box::new(value) },
            Monotype::Array(element) => {
                let GoType::Slice(source_element) = source else { unreachable!() };
                let GoType::Slice(target_element) = target else { unreachable!() };
                let parameter = self.temporary("element");
                let mut body = vec![];
                let converted = self.convert_convention(
                    identifier_expression(&parameter),
                    element,
                    direction,
                    &mut body,
                )?;
                body.push(GoStatement::Return(Some(converted)));
                let function = GoExpression::Function {
                    parameters: vec![(parameter, *source_element)],
                    result: Some(*target_element),
                    body,
                };
                let map = self.go_function(GoFunction { package: GoPackage::Array, name: "Map" });
                call(map, vec![function, value])
            }
            Monotype::Record(_) => {
                let foreign = self.monotypes.intern(Monotype::Opaque);
                match direction {
                    Direction::ToConvention => self.coerce(value, monotype, foreign, out)?,
                    Direction::FromConvention => self.coerce(value, foreign, monotype, out)?,
                }
            }
            Monotype::Nullable(element) => {
                let value = self.shared(value, "nullable", out);
                let converted = self.temporary("converted");
                let mut present = vec![];
                let inner = GoExpression::Unary { operator: "*", operand: Box::new(value.clone()) };
                let inner = self.convert_convention(inner, element, direction, &mut present)?;
                let inner = self.shared(inner, "present", &mut present);
                present.push(GoStatement::Assign {
                    targets: vec![identifier_expression(&converted)],
                    values: vec![GoExpression::Address(Box::new(inner))],
                });
                out.push(GoStatement::Variable { name: converted.clone(), type_: target, value: None });
                out.push(GoStatement::If {
                    condition: binary("!=", value, identifier_expression("nil")),
                    then: present,
                    otherwise: vec![],
                });
                identifier_expression(&converted)
            }
            Monotype::Effect(result) => {
                let value = self.shared(value, "action", out);
                let mut body = vec![];
                let performed =
                    self.convert_convention(call(value, vec![]), result, direction, &mut body)?;
                body.push(GoStatement::Return(Some(performed)));
                let GoType::Function { result: result_type, .. } = target else { unreachable!() };
                GoExpression::Function {
                    parameters: vec![],
                    result: result_type.map(|type_| *type_),
                    body,
                }
            }
            Monotype::Function(..) => {
                let value = self.shared(value, "function", out);
                let callable = self.value_callable(value, monotype);
                let layers = match direction {
                    Direction::ToConvention => callable.arity,
                    Direction::FromConvention => {
                        assert_eq!(
                            callable.arity, 1,
                            "invariant violated: functions received from foreign code stay curried"
                        );
                        1
                    }
                };
                self.convention_layer(callable, vec![], monotype, layers, direction)?
            }
            _ => value,
        })
    }

    pub(super) fn convention_layer(
        &mut self,
        callable: Callable,
        mut supplied: Vec<GoExpression>,
        monotype: MonotypeId,
        layers: usize,
        direction: Direction,
    ) -> GoResult<GoExpression> {
        let target = match direction {
            Direction::ToConvention => self.convention_or_native(monotype)?,
            Direction::FromConvention => self.go_type(monotype)?,
        };
        let GoType::Function { parameters, result: target_result } = target else { unreachable!() };
        let (argument, result) = self
            .monotypes
            .function_parts(monotype)
            .expect("invariant violated: a converted function takes an argument");
        let base = self.value_base(argument);
        let parameter = self.temporary(&base);
        let reverse = match direction {
            Direction::ToConvention => Direction::FromConvention,
            Direction::FromConvention => Direction::ToConvention,
        };
        let mut body = vec![];
        let argument = self.convert_convention(
            identifier_expression(&parameter),
            argument,
            reverse,
            &mut body,
        )?;
        if layers > 1 {
            supplied.push(self.shared(argument, &base, &mut body));
            let inner = self.convention_layer(callable, supplied, result, layers - 1, direction)?;
            body.push(GoStatement::Return(Some(inner)));
            return Ok(GoExpression::Function {
                parameters: vec![(parameter, parameters[0].clone())],
                result: target_result.map(|type_| *type_),
                body,
            });
        }
        supplied.push(argument);
        let applied = self.apply_arguments(callable, supplied, &mut body)?;
        match (self.monotypes.get(result).clone(), direction) {
            (Monotype::Effect(inner), Direction::ToConvention) => {
                let thunk_type = target_result.clone().map(|type_| *type_);
                let Some(GoType::Function { result: inner_type, .. }) = thunk_type else {
                    unreachable!()
                };
                let mut thunk_body = vec![];
                let performed =
                    self.convert_convention(applied, inner, direction, &mut thunk_body)?;
                thunk_body.push(returning(performed, inner_type.is_some()));
                let thunk = GoExpression::Function {
                    parameters: vec![],
                    result: inner_type.clone().map(|type_| *type_),
                    body: thunk_body,
                };
                body.push(GoStatement::Return(Some(thunk)));
            }
            (Monotype::Effect(inner), Direction::FromConvention) => {
                let performed =
                    self.convert_convention(call(applied, vec![]), inner, direction, &mut body)?;
                body.push(returning(performed, target_result.is_some()));
            }
            _ => {
                let converted = self.convert_convention(applied, result, direction, &mut body)?;
                body.push(returning(converted, target_result.is_some()));
            }
        }
        Ok(GoExpression::Function {
            parameters: vec![(parameter, parameters[0].clone())],
            result: target_result.map(|type_| *type_),
            body,
        })
    }

    pub(super) fn boundary_function(
        &mut self,
        function: GoFunction,
        boundary: Boundary,
        result: MonotypeId,
    ) -> GoResult<GoExpression> {
        let function = self.go_function(function);
        if boundary.result_parameter {
            let result = self.go_type(result)?;
            return Ok(GoExpression::Instantiation {
                function: Box::new(function),
                arguments: vec![result],
            });
        }
        if !boundary.instantiate {
            return Ok(function);
        }
        if let Monotype::ForeignData(data) = self.monotypes.get(result).clone() {
            let GoType::Generic { arguments, .. } = self.foreign_data_type(&data)? else {
                unreachable!("invariant violated: an instantiated foreign data type has arguments")
            };
            return Ok(GoExpression::Instantiation { function: Box::new(function), arguments });
        }
        let element = match self.monotypes.get(result).clone() {
            Monotype::Object(element)
            | Monotype::MutableArray(element)
            | Monotype::Nullable(element) => element,
            Monotype::Function(argument, _) => match self.monotypes.get(argument) {
                Monotype::Array(element) => *element,
                _ => unreachable!("invariant violated: an instantiated function takes an array"),
            },
            _ => unreachable!("invariant violated: an instantiated foreign returns a collection"),
        };
        let element = self.go_type(element)?;
        Ok(GoExpression::Instantiation { function: Box::new(function), arguments: vec![element] })
    }

    pub(super) fn go_function(&mut self, function: GoFunction) -> GoExpression {
        self.imports.insert(function.package.path().into());
        GoExpression::Qualified {
            package: function.package.name().into(),
            name: function.name.into(),
        }
    }

    pub(super) fn boundary_arguments(
        &mut self,
        arguments: &[Expression],
        boundary: Boundary,
        result: MonotypeId,
        uniform: bool,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Vec<GoExpression>> {
        let maybe = match boundary.maybe.and_then(|constructors| constructors.witness) {
            Some(witness) => self.mentioned_maybe(arguments[witness].monotype)?.unwrap_or(result),
            None => result,
        };
        let mut values = vec![];
        for (position, argument) in arguments.iter().enumerate() {
            if let Some(utility) = boundary.utility
                && utility.position == position
            {
                for &constructed in utility.constructors {
                    values.push(self.utility_constructor(constructed, arguments, result)?);
                }
                continue;
            }
            let value = match boundary.maybe {
                _ if let Some(destructor) = boundary.maybe_destructor
                    && destructor.position == position =>
                {
                    let mut witness = arguments[destructor.witness].monotype;
                    while let Some((_, result)) = self.monotypes.function_parts(witness) {
                        witness = result;
                    }
                    self.just_value_function(witness)?
                }
                _ if boundary.ignored.contains(&position) => identifier_expression("nil"),
                _ if boundary.int32_parameters.contains(&position) => self.value(argument, out)?,
                _ if boundary.is_just == Some(position) => self.is_just_function(maybe)?,
                Some(constructors) if constructors.just == position => {
                    if constructors.elements {
                        let element = self.array_payload_maybe(maybe)?;
                        values.push(self.just_function(element)?);
                    }
                    self.just_function(maybe)?
                }
                Some(constructors) if constructors.nothing == position => {
                    if constructors.elements {
                        let element = self.array_payload_maybe(maybe)?;
                        values.push(self.nothing_value(element)?);
                    }
                    self.nothing_value(maybe)?
                }
                _ if boundary.record_arguments.contains(&position) => {
                    let record = self.value(argument, out)?;
                    let record = self.hoist(record, "record", out);
                    let Monotype::Record(fields) = self.monotypes.get(argument.monotype).clone()
                    else {
                        unreachable!("invariant violated: a record argument has a record type")
                    };
                    for record_field in fields.iter() {
                        let label = &record_field.label;
                        values.push(self.read_field(record.clone(), argument.monotype, label));
                    }
                    continue;
                }
                _ if boundary.unit_values => {
                    let value = self.value(argument, out)?;
                    self.unit_valued(value, argument.monotype, out)?
                }
                _ if let Some(&(_, arity)) =
                    boundary.uncurried.iter().find(|(callback, _)| *callback == position) =>
                {
                    self.uncurried_callback(argument, arity, boundary.uncurried_perform, out)?
                }
                _ if uniform
                    && let Some(&arrows) = boundary.callback_arities.get(position)
                    && arrows > 0
                    && self.effect_after(argument.monotype, arrows) =>
                {
                    let value = self.value(argument, out)?;
                    let value = self.shared(value, "function", out);
                    self.uniform_function(value, argument.monotype, arrows)?
                }
                _ => {
                    let value = self.value(argument, out)?;
                    let declared = boundary.signature.and_then(|signature| {
                        signature.parameters.get(position).map(Spelled::arrows)
                    });
                    match declared {
                        Some(arrows) if arrows > 0 => {
                            let callback =
                                self.curried_callback(value, argument.monotype, arrows, out)?;
                            if self.is_unit(self.monotypes.result_after(argument.monotype, arrows))
                            {
                                self.unit_valued(callback, argument.monotype, out)?
                            } else {
                                callback
                            }
                        }
                        _ => self.typed_constant(value, argument.monotype)?,
                    }
                }
            };
            values.push(value);
        }
        Ok(values)
    }
}
