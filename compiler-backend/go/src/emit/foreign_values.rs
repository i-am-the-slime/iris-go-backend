use super::operators::float_constant;
use super::sorting::Placement;
use super::{
    Emitter, Mode, Sink, binary, call, coerce, field, fusion, identifier_expression, mutable,
    unit_value,
};
use crate::error::{GoError, GoResult};
use crate::foreign::{Boundary, Comparison, Foreign, GoFunction, GoPackage, Operator};
use crate::monomorphic::{Expression, ExpressionKind, Literal};
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoCase, GoExpression, GoStatement, GoType};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn record_field_projection(
        &mut self,
        record: MonotypeId,
        label: &str,
    ) -> GoResult<GoExpression> {
        let Monotype::Record(fields) = self.monotypes.get(record).clone() else {
            unreachable!("invariant violated: a field projection has a record type")
        };
        let field_monotype = fields
            .iter()
            .find(|record_field| record_field.label == label)
            .expect("invariant violated: a projected field exists")
            .monotype;
        let body = self.read_field(identifier_expression("value"), record, label);
        Ok(GoExpression::Function {
            parameters: vec![("value".into(), self.go_type(record)?)],
            result: self.go_result(field_monotype)?,
            body: vec![GoStatement::Return(Some(body))],
        })
    }

    fn unfoldr(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let producer = &arguments[4];
        let produced = self.monotypes.result_after(producer.monotype, 1);
        let (maybe, tuple) = match foreign {
            Foreign::Unfoldr => (produced, self.constructor_field_monotype(produced, "Just", 0)?),
            _ => (self.constructor_field_monotype(produced, "Tuple", 1)?, produced),
        };
        let is_nothing = self.projection(maybe, "Nothing", None)?;
        let from_just = self.projection(maybe, "Just", Some(0))?;
        let first = self.projection(tuple, "Tuple", Some(0))?;
        let second = self.projection(tuple, "Tuple", Some(1))?;
        let producer = self.value(producer, out)?;
        let seed = self.value(&arguments[5], out)?;
        let name = match foreign {
            Foreign::Unfoldr => "Unfoldr",
            _ => "Unfoldr1",
        };
        let function = self.go_function(GoFunction { package: GoPackage::Array, name });
        Ok(call(function, vec![is_nothing, from_just, first, second, producer, seed]))
    }

    pub(super) fn projection(
        &mut self,
        monotype: MonotypeId,
        constructor: &str,
        position: Option<usize>,
    ) -> GoResult<GoExpression> {
        let (data, index) = self.constructor_named(monotype, constructor)?;
        let layout = self.data_layout(&data)?;
        let parameter = identifier_expression("value");
        let (result, body) = match position {
            Some(position) => {
                let (_, field_monotype) = layout.constructors[index].fields[position];
                let read = self.constructor_field(&layout, index, position, parameter);
                (self.go_type(field_monotype)?, read)
            }
            None => {
                let test = self.constructor_test(&layout, index, parameter);
                (GoType::Bool, test.unwrap_or(GoExpression::Boolean(true)))
            }
        };
        Ok(GoExpression::Function {
            parameters: vec![("value".into(), self.go_type(monotype)?)],
            result: Some(result),
            body: vec![GoStatement::Return(Some(body))],
        })
    }

    /// `xs !! i` as a bounds check rather than a call through Just and Nothing closures.
    fn maybe_index(
        &mut self,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let (data, just) = self.constructor_named(monotype, "Just")?;
        let (_, nothing) = self.constructor_named(monotype, "Nothing")?;
        // Go rejects a constant negative index even in a branch that cannot run.
        if let ExpressionKind::Literal(Literal::Int(index)) = arguments[3].kind
            && index < 0
        {
            return self.construct(&data, nothing, vec![]);
        }
        let elements = self.value(&arguments[2], out)?;
        let elements = self.hoist(elements, "elements", out);
        let index = self.value(&arguments[3], out)?;
        if let GoExpression::Integer(constant) = index
            && constant < 0
        {
            return self.construct(&data, nothing, vec![]);
        }
        let index = self.hoist(index, "index", out);
        let element = GoExpression::Index {
            value: Box::new(elements.clone()),
            index: Box::new(index.clone()),
        };
        let found = self.construct(&data, just, vec![element])?;
        let missing = self.construct(&data, nothing, vec![])?;
        let name = self.temporary("element");
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let condition = mutable::in_bounds(&index, elements);
        let target = vec![identifier_expression(&name)];
        out.push(GoStatement::If {
            condition,
            then: vec![GoStatement::Assign { targets: target.clone(), values: vec![found] }],
            otherwise: vec![GoStatement::Assign { targets: target, values: vec![missing] }],
        });
        Ok(identifier_expression(&name))
    }

    /// `updateAt i x xs` as a bounds check around a copy of `xs` with `x` at `i`.
    fn update_at(
        &mut self,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let (data, just) = self.constructor_named(monotype, "Just")?;
        let (_, nothing) = self.constructor_named(monotype, "Nothing")?;
        let index = self.value(&arguments[2], out)?;
        if let GoExpression::Integer(constant) = index
            && constant < 0
        {
            return self.construct(&data, nothing, vec![]);
        }
        let index = self.hoist(index, "index", out);
        let value = self.value(&arguments[3], out)?;
        let value = self.hoist(value, "value", out);
        let elements = self.value(&arguments[4], out)?;
        let elements = self.hoist(elements, "elements", out);
        let name = self.temporary("updateAt");
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let mut within = vec![];
        let updated = self.updated_array(elements.clone(), index.clone(), value, &mut within);
        let found = self.construct(&data, just, vec![updated])?;
        let missing = self.construct(&data, nothing, vec![])?;
        let target = vec![identifier_expression(&name)];
        within.push(GoStatement::Assign { targets: target.clone(), values: vec![found] });
        out.push(GoStatement::If {
            condition: mutable::in_bounds(&index, elements),
            then: within,
            otherwise: vec![GoStatement::Assign { targets: target, values: vec![missing] }],
        });
        Ok(identifier_expression(&name))
    }

    /// A copy of `elements` with `value` at `index`, which is within it.
    fn updated_array(
        &mut self,
        elements: GoExpression,
        index: GoExpression,
        value: GoExpression,
        out: &mut Vec<GoStatement>,
    ) -> GoExpression {
        self.imports.insert("slices".into());
        let clone = GoExpression::Qualified { package: "slices".into(), name: "Clone".into() };
        let name = self.temporary("updated");
        let updated = identifier_expression(&name);
        out.push(GoStatement::Define {
            names: vec![name],
            values: vec![call(clone, vec![elements])],
        });
        let element =
            GoExpression::Index { value: Box::new(updated.clone()), index: Box::new(index) };
        out.push(GoStatement::Assign { targets: vec![element], values: vec![value] });
        updated
    }

    fn updated_in_place(
        &mut self,
        elements: GoExpression,
        index: GoExpression,
        value: GoExpression,
        copied: String,
        out: &mut Vec<GoStatement>,
    ) -> GoExpression {
        let index = self.hoist(index, "index", out);
        let value = self.hoist(value, "value", out);
        self.imports.insert("slices".into());
        let clone = GoExpression::Qualified { package: "slices".into(), name: "Clone".into() };
        let name = self.temporary("updated");
        let updated = identifier_expression(&name);
        out.push(GoStatement::Define { names: vec![name], values: vec![elements] });
        let flag = identifier_expression(&copied);
        out.push(GoStatement::If {
            condition: GoExpression::Unary { operator: "!", operand: Box::new(flag.clone()) },
            then: vec![
                GoStatement::Assign {
                    targets: vec![updated.clone()],
                    values: vec![call(clone, vec![updated.clone()])],
                },
                GoStatement::Assign { targets: vec![flag], values: vec![GoExpression::Boolean(true)] },
            ],
            otherwise: vec![],
        });
        let element =
            GoExpression::Index { value: Box::new(updated.clone()), index: Box::new(index) };
        out.push(GoStatement::Assign { targets: vec![element], values: vec![value] });
        self.copied_flags.insert(copied);
        updated
    }

    pub(super) fn own_updates(
        &mut self,
        body: &Expression,
        owned: &[Vec<*const Expression>],
    ) -> Vec<String> {
        let mut written = rustc_hash::FxHashSet::default();
        crate::monomorphic::traversal::visit(body, &mut |expression| {
            if let ExpressionKind::Foreign { foreign: Foreign::ArrayUpdated, arguments } =
                &expression.kind
            {
                written.insert(std::ptr::from_ref(&arguments[2]));
            }
        });
        let mut flags = vec![];
        for nodes in owned {
            let updates: Vec<_> = nodes.iter().filter(|node| written.contains(*node)).collect();
            if updates.is_empty() {
                continue;
            }
            let flag = self.temporary("copied");
            for node in updates {
                self.owned_updates.insert(*node, flag.clone());
            }
            flags.push(flag);
        }
        flags
    }

    pub(super) fn release_updates(
        &mut self,
        owned: &[Vec<*const Expression>],
        flags: Vec<String>,
    ) -> Vec<GoStatement> {
        for node in owned.iter().flatten() {
            self.owned_updates.remove(node);
        }
        flags
            .into_iter()
            .filter(|flag| self.copied_flags.remove(flag))
            .map(|flag| GoStatement::Define {
                names: vec![flag],
                values: vec![GoExpression::Boolean(false)],
            })
            .collect()
    }

    fn int_from_number(
        &mut self,
        number: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let number = self.value(number, out)?;
        let (data, just) = self.constructor_named(monotype, "Just")?;
        let (_, nothing) = self.constructor_named(monotype, "Nothing")?;
        // Go rejects `int32(c)` for a constant `c` that is not an int32, so a literal is decided here.
        if let Some(constant) = float_constant(&number) {
            let fits = constant.trunc() == constant
                && constant >= f64::from(i32::MIN)
                && constant <= f64::from(i32::MAX);
            if fits {
                return self.construct(&data, just, vec![GoExpression::Integer(constant as i64)]);
            }
            return self.construct(&data, nothing, vec![]);
        }
        let number = self.hoist(number, "number", out);
        let integer = GoExpression::Conversion {
            type_: GoType::Named("int32".into()),
            value: Box::new(number.clone()),
        };
        let found = self.construct(&data, just, vec![integer])?;
        let missing = self.construct(&data, nothing, vec![])?;
        self.imports.insert("math".into());
        let math =
            |name: &str| GoExpression::Qualified { package: "math".into(), name: name.into() };
        let whole = binary("==", call(math("Trunc"), vec![number.clone()]), number.clone());
        let condition = binary(
            "&&",
            whole,
            binary(
                "&&",
                binary(">=", number.clone(), math("MinInt32")),
                binary("<=", number, math("MaxInt32")),
            ),
        );
        let name = self.temporary("integer");
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let target = vec![identifier_expression(&name)];
        out.push(GoStatement::If {
            condition,
            then: vec![GoStatement::Assign { targets: target.clone(), values: vec![found] }],
            otherwise: vec![GoStatement::Assign { targets: target, values: vec![missing] }],
        });
        Ok(identifier_expression(&name))
    }

    pub(super) fn foreign_value(
        &mut self,
        foreign: &'static Foreign,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if foreign.is_effectful() {
            let expression = Expression::new(
                ExpressionKind::Foreign { foreign, arguments: arguments.to_vec() },
                monotype,
            );
            return self.thunk(&expression, out);
        }
        if let Foreign::Range = foreign {
            let range =
                self.go_function(GoFunction { package: GoPackage::Array, name: "RangeInt32" });
            let values = self.values(arguments, out)?;
            return Ok(call(range, values));
        }
        if let Foreign::MaybeIndex = foreign {
            return self.maybe_index(arguments, monotype, out);
        }
        if let Foreign::UpdateAt = foreign {
            return self.update_at(arguments, monotype, out);
        }
        if let Foreign::ArrayUpdated = foreign {
            let index = self.value(&arguments[0], out)?;
            let value = self.value(&arguments[1], out)?;
            let elements = self.value(&arguments[2], out)?;
            if let Some(copied) = self.owned_updates.get(&std::ptr::from_ref(&arguments[2])) {
                let copied = copied.clone();
                return Ok(self.updated_in_place(elements, index, value, copied, out));
            }
            return Ok(self.updated_array(elements, index, value, out));
        }
        if let Foreign::IntFromNumber = foreign {
            return self.int_from_number(&arguments[2], monotype, out);
        }
        if let Foreign::Operator(Operator::StringAppend) = foreign
            && self.owned_snocs.contains(&std::ptr::from_ref(&arguments[0]))
        {
            return self.append_to_buffer(arguments, out);
        }
        if let Some((position, owned)) = crate::foreign::owned_hash_map_write(foreign)
            && self.owned_snocs.contains(&std::ptr::from_ref(&arguments[position]))
        {
            return self.foreign_value(owned, arguments, monotype, out);
        }
        if foreign.calls(crate::foreign::ARRAY_APPEND)
            && self.owned_snocs.contains(&std::ptr::from_ref(&arguments[0]))
            && let ExpressionKind::Array(elements) = &arguments[1].kind
        {
            let mut values = vec![self.value(&arguments[0], out)?];
            for element in elements {
                let value = self.value(element, out)?;
                values.push(self.typed_constant(value, element.monotype)?);
            }
            let appended = call(identifier_expression("append"), values);
            return Ok(call(
                self.go_function(GoFunction { package: GoPackage::Array, name: "Bounded" }),
                vec![appended],
            ));
        }
        if let Some(position) = super::ownership::object_write_position(foreign)
            && self.owned_snocs.contains(&std::ptr::from_ref(&arguments[position]))
        {
            let name = if position == 2 { "InsertOwned" } else { "RemoveOwned" };
            let mut values = vec![];
            for argument in arguments {
                let value = self.value(argument, out)?;
                values.push(self.typed_constant(value, argument.monotype)?);
            }
            let write = GoFunction { package: GoPackage::Object, name };
            return Ok(call(self.go_function(write), values));
        }
        if let Foreign::Snoc = foreign
            && let Some((built, exact)) = self.built_with_spare(&arguments[0], 1, out)?
        {
            // The slice gives an appended constant its type.
            let element = self.value(&arguments[1], out)?;
            let appended = call(identifier_expression("append"), vec![built, element]);
            if exact {
                return Ok(appended);
            }
            let bounded = GoFunction { package: GoPackage::Array, name: "Bounded" };
            return Ok(call(self.go_function(bounded), vec![appended]));
        }
        if let Foreign::Snoc = foreign {
            let array = self.value(&arguments[0], out)?;
            let element = self.value(&arguments[1], out)?;
            let element = self.typed_constant(element, arguments[1].monotype)?;
            if self.owned_snocs.contains(&std::ptr::from_ref(&arguments[0])) {
                let appended = call(identifier_expression("append"), vec![array, element]);
                return Ok(call(
                    self.go_function(GoFunction { package: GoPackage::Array, name: "Bounded" }),
                    vec![appended],
                ));
            }
            let snoc = self.go_function(GoFunction { package: GoPackage::Array, name: "Snoc" });
            let element_type = self.go_type(arguments[1].monotype)?;
            if matches!(element_type, GoType::Any | GoType::Erased(_)) {
                let function = Box::new(snoc);
                let snoc = GoExpression::Instantiation { function, arguments: vec![element_type] };
                return Ok(call(snoc, vec![array, element]));
            }
            return Ok(call(snoc, vec![array, element]));
        }
        if let Foreign::LazyDefer = foreign {
            if let ExpressionKind::Lambda { parameters, body } = &arguments[0].kind
                && let [parameter] = parameters.as_slice()
                && self.is_already_a_value(body)
            {
                self.locals.insert(parameter.id, unit_value());
                let value = self.value(body, out)?;
                let value = self.typed_constant(value, body.monotype)?;
                self.imports.insert(GoPackage::Lazy.path().into());
                let mut evaluated =
                    GoExpression::Qualified { package: "lazy".into(), name: "Evaluated".into() };
                let type_ = self.go_type(body.monotype)?;
                if matches!(type_, GoType::Any | GoType::Erased(_)) {
                    // Go would infer the dynamic type of the value instead.
                    let function = Box::new(evaluated);
                    evaluated = GoExpression::Instantiation { function, arguments: vec![type_] };
                }
                return Ok(call(evaluated, vec![value]));
            }
            return self.lazy_defer(&arguments[0], monotype);
        }
        if let Foreign::LazyForce = foreign {
            if let ExpressionKind::Foreign { foreign: Foreign::LazyDefer, arguments: deferred } =
                &arguments[0].kind
                && let ExpressionKind::Lambda { parameters, body } = &deferred[0].kind
                && let [parameter] = parameters.as_slice()
            {
                self.locals.insert(parameter.id, unit_value());
                return self.value(body, out);
            }
            let lazy = self.value(&arguments[0], out)?;
            return Ok(call(field(lazy, "Force"), vec![]));
        }
        if let Foreign::RunEffect | Foreign::UnsafePerformEffect = foreign {
            if self.is_unit(monotype) {
                self.sink(&arguments[0], Mode::Perform, Sink::Discard, out)?;
                return Ok(unit_value());
            }
            let name = self.temporary("performed");
            self.sink(&arguments[0], Mode::Perform, Sink::Define(name.clone()), out)?;
            return Ok(identifier_expression(&name));
        }
        if let Foreign::RecordGet = foreign {
            let ExpressionKind::Literal(Literal::String(label)) = &arguments[0].kind else {
                return self.record_get_by_label(arguments, monotype, out);
            };
            let record = self.value(&arguments[1], out)?;
            return Ok(self.read_field(record, arguments[1].monotype, label));
        }
        if let Foreign::RecordHas = foreign {
            return Err(GoError::unsupported_construct(
                "a label test on a value whose record type is not closed",
            ));
        }
        if let Foreign::Record(_) = foreign {
            return Err(GoError::unsupported_construct(
                "record builders with labels unknown at compile time",
            ));
        }
        if let Foreign::Json(codec) = *foreign {
            return self.json(codec, arguments, monotype, out);
        }
        if let Foreign::ShowForeignErrors = foreign {
            return self.show_foreign_errors(arguments, out);
        }
        if let Foreign::Crash = foreign {
            let message = self.value(&arguments[0], out)?;
            out.push(GoStatement::Expression(call(identifier_expression("panic"), vec![message])));
            let type_ = self.go_type(monotype)?;
            let name = self.temporary("unreachable");
            out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
            return Ok(identifier_expression(&name));
        }
        if let Foreign::Unfoldr | Foreign::Unfoldr1 = *foreign {
            return self.unfoldr(*foreign, arguments, out);
        }
        if let Foreign::Project { arity, effectful, .. } = *foreign {
            if effectful && arity > 0 {
                return self.project_effect(*foreign, arguments, monotype, out);
            }
            let called = self.project_call(*foreign, arguments, out)?;
            let crossing = self.project_crossing(*foreign);
            return self.out_of_convention(called, monotype, crossing, out);
        }
        if let Foreign::Operator(Operator::ArrayLength) = *foreign
            && self.is_fusible(&arguments[0], fusion::Demand::FORWARD)
        {
            return self.fused_length(&arguments[0], monotype, out);
        }
        if let Foreign::Call { boundary: Boundary { iteration: Some(iteration), .. }, .. } =
            *foreign
            && let Some(iterated) = self.iteration(iteration, arguments, monotype, out)?
        {
            return Ok(iterated);
        }
        if foreign.calls(crate::foreign::ARRAY_FROM_LIST)
            && let Some(listed) = self.array_from_list(&arguments[0], monotype, out)?
        {
            return Ok(listed);
        }
        if foreign.calls(crate::foreign::ARRAY_UNZIP)
            && let Some(unzipped) = self.unzip(&arguments[0], monotype, out)?
        {
            return Ok(unzipped);
        }
        if foreign.calls(crate::foreign::ARRAY_SORT_BY) {
            if let Some(sorted) = self.primitive_sort(arguments, Placement::Copied, out)? {
                return Ok(sorted);
            }
            return self.ordering_sort(arguments, Placement::Copied, out);
        }
        if let Foreign::Call { function, boundary, .. } = *foreign {
            let values = self.boundary_arguments(arguments, boundary, monotype, true, out)?;
            if let Some(standard) = self.standard_call(function, &values, arguments) {
                return Ok(standard);
            }
            let function = self.boundary_function(function, boundary, monotype)?;
            let result = call(function, values);
            if boundary.found
                && let Some(constructors) = boundary.maybe
            {
                return self.found_maybe(result, arguments, constructors, monotype, out);
            }
            if boundary.record_result {
                return self.record_from_results(result, monotype, out);
            }
            return Ok(result);
        }
        if let Foreign::ReferenceEqual = *foreign {
            return self.reference_equal(&arguments[0], &arguments[1], out);
        }
        let mut values = self.values(arguments, out)?;
        Ok(match *foreign {
            Foreign::Operator(Operator::Compare(comparison))
                if !matches!(comparison, Comparison::Equal | Comparison::NotEqual)
                    && matches!(self.monotypes.get(arguments[0].monotype), Monotype::String) =>
            {
                self.string_ordering(comparison, values)
            }
            Foreign::Operator(operator) => self.operator(operator, values),
            Foreign::Int64 { operation, signedness } => {
                self.int64_operation(operation, signedness, values)
            }
            Foreign::Constant(function) => {
                self.imports.insert(function.package.path().into());
                let constant = GoExpression::Qualified {
                    package: function.package.name().into(),
                    name: function.name.into(),
                };
                self.narrow(constant, monotype)
            }
            Foreign::Unit => unit_value(),
            Foreign::UnsafeCoerce => {
                let position = arguments[0].position;
                self.coerce_at(values.remove(0), arguments[0].monotype, monotype, position, out)?
            }
            Foreign::Identity => values.remove(0),
            _ => unreachable!("invariant violated: effectful foreign reached value conversion"),
        })
    }

    /// `unsafeGet label record` with a label known only at run time, over a
    /// record whose fields the specialised type fixes: a switch over the
    /// labels of the fields that can stand at the requested type. A field
    /// whose type has a different shape cannot be the one read, since the
    /// caller uses the result at its own type; `Data.Variant` reads its
    /// handlers this way after asking `unsafeHas`.
    fn record_get_by_label(
        &mut self,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let Monotype::Record(fields) = self.monotypes.get(arguments[1].monotype).clone() else {
            return Err(GoError::unsupported_construct(
                "record access through a run-time label into a value that is not a closed record",
            ));
        };
        let label = self.value(&arguments[0], out)?;
        let record = self.value(&arguments[1], out)?;
        let record = self.shared(record, "record", out);
        let chosen = self.temporary("field");
        let mut cases = Vec::with_capacity(fields.len());
        for record_field in fields.iter() {
            let mut body = vec![];
            let read = self.read_field(record.clone(), arguments[1].monotype, &record_field.label);
            let value = match self.coerce(read, record_field.monotype, monotype, &mut body) {
                Ok(value) => value,
                Err(GoError::Unsupported {
                    state: crate::error::UnsupportedState::Construct { construct },
                    ..
                }) if construct == coerce::UNRELATED_TYPES => continue,
                Err(error) => return Err(error),
            };
            body.push(GoStatement::Assign {
                targets: vec![identifier_expression(&chosen)],
                values: vec![value],
            });
            let label = GoExpression::String(record_field.label.to_string());
            cases.push(GoCase { values: vec![label], body, line: None });
        }
        if cases.is_empty() {
            return Err(GoError::unsupported_construct(
                "record access through a run-time label where no field has the requested type",
            ));
        }
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: chosen.clone(), type_, value: None });
        out.push(GoStatement::Switch { value: Some(label), cases, default: None });
        Ok(identifier_expression(&chosen))
    }
}
