//! How values cross into and out of foreign code: the conventions of Go packages' functions.

use super::application::Callable;
use super::{Crossing, Direction, Emitter, binary, call, identifier_expression, returning};
use crate::error::GoResult;
use crate::foreign::{Boundary, GoFunction, Spelled};
use crate::monomorphic::Expression;
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{
    GoBinaryOperator, GoExpression, GoPackage, GoStatement, GoType, GoUnaryOperator,
};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn convention_type(
        &mut self,
        monotype: MonotypeId,
        crossing: Crossing,
    ) -> GoResult<Option<GoType>> {
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Array(element) => self
                .convention_type(element, crossing)?
                .map(|element| GoType::Slice(Box::new(element))),
            // A project's foreign package cannot name the struct generated for a record, so a
            // record crosses as the JavaScript object it is there: a Foreign holding an object
            // table. A record the foreign package's own struct represents crosses as it is.
            Monotype::Record(_) if self.monotypes.foreign_records.contains_key(&monotype) => None,
            Monotype::Record(_) if crossing == Crossing::Native => None,
            Monotype::Record(_) => Some(GoType::Any),
            Monotype::Nullable(element) => self
                .convention_type(element, crossing)?
                .map(|element| GoType::Pointer(Box::new(element))),
            Monotype::Effect(result) => self.convention_type(result, crossing)?.map(|result| {
                GoType::Function { parameters: vec![], result: Some(Box::new(result)) }
            }),
            // A function crosses curried, one argument at a time, and a function whose result is
            // an effect performs it when called: `a -> Effect b` is `func(A) B`, as Iris's own
            // functions are.
            Monotype::Function(argument, result) => {
                let returned = self.monotypes.effect_result(result).unwrap_or(result);
                let differs = self.arity(monotype) > 1
                    || self.convention_type(argument, crossing)?.is_some()
                    || self.convention_type(returned, crossing)?.is_some();
                if !differs {
                    return Ok(None);
                }
                let argument = self.convention_or_native(argument, crossing)?;
                let returned = self.convention_result(returned, crossing)?;
                Some(GoType::Function {
                    parameters: vec![argument],
                    result: returned.map(Box::new),
                })
            }
            _ => None,
        })
    }

    pub(super) fn convention_or_native(
        &mut self,
        monotype: MonotypeId,
        crossing: Crossing,
    ) -> GoResult<GoType> {
        match self.convention_type(monotype, crossing)? {
            Some(type_) => Ok(type_),
            None => self.go_type(monotype),
        }
    }

    pub(super) fn convention_result(
        &mut self,
        monotype: MonotypeId,
        crossing: Crossing,
    ) -> GoResult<Option<GoType>> {
        if self.is_unit(monotype) {
            return Ok(None);
        }
        Ok(Some(self.convention_or_native(monotype, crossing)?))
    }

    pub(super) fn in_convention(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        crossing: Crossing,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        self.convert_convention(value, monotype, Direction::ToConvention, crossing, out)
    }

    pub(super) fn out_of_convention(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        crossing: Crossing,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        self.convert_convention(value, monotype, Direction::FromConvention, crossing, out)
    }

    pub(super) fn convert_convention(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        direction: Direction,
        crossing: Crossing,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if self.convention_type(monotype, crossing)?.is_none() {
            return Ok(value);
        }
        let (source, target) = match direction {
            Direction::ToConvention => {
                (self.go_type(monotype)?, self.convention_or_native(monotype, crossing)?)
            }
            Direction::FromConvention => {
                (self.convention_or_native(monotype, crossing)?, self.go_type(monotype)?)
            }
        };
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Array(element) => {
                let GoType::Slice(source_element) = source else { unreachable!() };
                let GoType::Slice(target_element) = target else { unreachable!() };
                let parameter = self.temporary("element");
                let mut body = vec![];
                let converted = self.convert_convention(
                    identifier_expression(&parameter),
                    element,
                    direction,
                    crossing,
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
            Monotype::Record(_) if crossing == Crossing::BoxedWithoutRows => match direction {
                Direction::ToConvention => {
                    GoExpression::Conversion { type_: target, value: Box::new(value) }
                }
                Direction::FromConvention => {
                    GoExpression::TypeAssertion { value: Box::new(value), type_: target }
                }
            },
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
                let inner = GoExpression::Unary {
                    operator: GoUnaryOperator::Dereference,
                    operand: Box::new(value.clone()),
                };
                let inner =
                    self.convert_convention(inner, element, direction, crossing, &mut present)?;
                let inner = self.shared(inner, "present", &mut present);
                present.push(GoStatement::Assign {
                    targets: vec![identifier_expression(&converted)],
                    values: vec![GoExpression::Address(Box::new(inner))],
                });
                out.push(GoStatement::Variable {
                    name: converted.clone(),
                    type_: target,
                    value: None,
                });
                out.push(GoStatement::If {
                    condition: binary(GoBinaryOperator::NotEqual, value, GoExpression::nil()),
                    then: present,
                    otherwise: vec![],
                });
                identifier_expression(&converted)
            }
            Monotype::Effect(result) => {
                let value = self.shared(value, "action", out);
                let mut body = vec![];
                let performed = self.convert_convention(
                    call(value, vec![]),
                    result,
                    direction,
                    crossing,
                    &mut body,
                )?;
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
                self.convention_layer(callable, vec![], monotype, layers, direction, crossing)?
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
        crossing: Crossing,
    ) -> GoResult<GoExpression> {
        let target = match direction {
            Direction::ToConvention => self.convention_or_native(monotype, crossing)?,
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
            crossing,
            &mut body,
        )?;
        if layers > 1 {
            supplied.push(self.shared(argument, &base, &mut body));
            let inner =
                self.convention_layer(callable, supplied, result, layers - 1, direction, crossing)?;
            body.push(GoStatement::Return(Some(inner)));
            return Ok(GoExpression::Function {
                parameters: vec![(parameter, parameters[0].clone())],
                result: target_result.map(|type_| *type_),
                body,
            });
        }
        supplied.push(argument);
        let applied = self.apply_arguments(callable, supplied, &mut body)?;
        // Applying either side performs an effectful result, so only the value converts.
        let returned = self.monotypes.effect_result(result).unwrap_or(result);
        let value = self.convert_convention(applied, returned, direction, crossing, &mut body)?;
        body.push(returning(value, target_result.is_some()));
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
        self.qualified(function.package, function.name)
    }

    pub(super) fn qualified(&mut self, package: GoPackage, name: &str) -> GoExpression {
        self.import(package);
        GoExpression::qualified(package, name)
    }

    pub(super) fn import(&mut self, package: GoPackage) {
        self.imports.insert(package.path().into());
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
            if boundary.found
                && let Some(constructors) = boundary.maybe
                && (constructors.just == position || constructors.nothing == position)
            {
                continue;
            }
            let uncurried = boundary.uncurried.iter().find(|(callback, _)| *callback == position);
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
                _ if boundary.ignored.contains(&position) => GoExpression::nil(),
                _ if boundary.lazy.contains(&position) => self.lazy_argument(argument, out)?,
                _ if boundary.foreign_arguments.contains(&position) => {
                    let value = self.value(argument, out)?;
                    let opaque = self.monotypes.intern(Monotype::Opaque);
                    self.coerce(value, argument.monotype, opaque, out)?
                }
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
                _ if let Some(&(_, arity)) = uncurried => {
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
                    let declared =
                        boundary.signature.and_then(|signature| signature.parameters.get(position));
                    match declared {
                        Some(Spelled::Scalar) => value,
                        Some(declared) if declared.arrows() > 0 => {
                            let arrows = declared.arrows();
                            let monotype = argument.monotype;
                            let callback = self.curried_callback(value, monotype, arrows, out)?;
                            if self.is_unit(self.monotypes.result_after(monotype, arrows)) {
                                self.unit_valued(callback, monotype, out)?
                            } else {
                                callback
                            }
                        }
                        _ => self.typed_argument(value, argument)?,
                    }
                }
            };
            values.push(value);
        }
        Ok(values)
    }

    /// An argument the Go helper calls for when it needs it, `func() T { return value }`. A pure
    /// argument is built inside, so only the path that uses it pays for it; any other is evaluated
    /// here, in order, and the closure returns its value.
    fn lazy_argument(
        &mut self,
        argument: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let result = self.go_type(argument.monotype)?;
        let mut body = vec![];
        let value = match crate::purity::is_deferrable(argument) {
            true => {
                let saved = self.tail_loop.take();
                let value = self.value(argument, &mut body);
                self.tail_loop = saved;
                value?
            }
            false => {
                let value = self.value(argument, out)?;
                self.shared(value, "argument", out)
            }
        };
        body.push(GoStatement::Return(Some(value)));
        Ok(GoExpression::Function { parameters: vec![], result: Some(result), body })
    }
}
