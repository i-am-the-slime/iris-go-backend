use super::buffers::{to_bytes, to_string};
use super::conditions::negated;
use super::foreign_values::updated_arrays;
use super::fusion::{Demand, Need, Order, Pipeline};
use super::ownership::{Carried, Place, owned_snocs};
use super::recycling::Recycled;
use super::{
    Emitter, Mode, Sink, binary, call, conjunction, identifier_expression, unit_value, uses_local,
};
use crate::error::GoResult;
use crate::foreign::{GoFunction, GoPackage, Iteration};
use crate::monomorphic::{
    Expression, ExpressionKind, FunctionId, Guarded, Local, LocalId, Pattern, PatternKind,
};
use crate::monotype::{DataType, Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement, GoType};

pub(super) enum Callback<'e> {
    Inline { parameters: Vec<&'e Local>, body: &'e Expression },
    Direct { function: GoExpression, callee: FunctionId, leading: Vec<GoExpression> },
}

pub(super) enum Found<'e> {
    Inline { parameters: Vec<&'e Local>, body: &'e Expression },
    Direct { function: GoExpression, callee: FunctionId, leading: &'e [Expression] },
}

impl Callback<'_> {
    /// Whether the callback reads its argument at `position`.
    pub(super) fn reads(&self, position: usize) -> bool {
        match self {
            Callback::Inline { parameters, body } => uses_local(body, parameters[position].id),
            Callback::Direct { .. } => true,
        }
    }
}

impl Found<'_> {
    pub(super) fn reads(&self, position: usize) -> bool {
        match self {
            Found::Inline { parameters, body } => uses_local(body, parameters[position].id),
            Found::Direct { .. } => true,
        }
    }
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
        if let Some(vectorised) = self.vectorised(iteration, arguments, monotype, out)? {
            return Ok(Some(vectorised));
        }
        let (position, arity) = match iteration {
            Iteration::FoldLeft | Iteration::FoldRight | Iteration::MapWithIndex => (0, 2),
            Iteration::Map | Iteration::Filter | Iteration::Any | Iteration::All => (0, 1),
            Iteration::Bind => (1, 1),
            Iteration::FindIndex | Iteration::FindLastIndex | Iteration::Find => (2, 1),
            Iteration::ZipWith => return Ok(None),
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
        let callback = self.capture(found, out)?;
        let value = match iteration {
            Iteration::FoldLeft | Iteration::FoldRight => {
                self.fold(iteration, callback, &arguments[1], &arguments[2], monotype, out)?
            }
            Iteration::Map | Iteration::MapWithIndex => {
                let recycled = self.recycled_maps.get(&std::ptr::from_ref(&arguments[0])).cloned();
                self.map(iteration, callback, &arguments[1], monotype, recycled, out)?
            }
            Iteration::Filter => self.filter(callback, &arguments[1], monotype, out)?,
            Iteration::Any | Iteration::All => {
                self.search(iteration, callback, &arguments[1], out)?
            }
            Iteration::Bind => self.bind(callback, &arguments[0], monotype, out)?,
            Iteration::FindIndex | Iteration::FindLastIndex => {
                self.find_index(iteration, callback, &arguments[3], monotype, out)?
            }
            Iteration::Find => self.find_element(callback, &arguments[3], monotype, out)?,
            Iteration::ZipWith => unreachable!("invariant violated: zipWith has no scalar loop"),
        };
        Ok(Some(value))
    }

    pub(super) fn callback<'e>(&self, function: &'e Expression, arity: usize) -> Option<Found<'e>> {
        let (head, leading): (&Expression, &[Expression]) = match &function.kind {
            ExpressionKind::Apply { function, arguments } => (function, arguments),
            _ => (function, &[]),
        };
        match &head.kind {
            ExpressionKind::Function(id) => {
                let callee = self.program.function(*id);
                let direct = callee.parameters.len() == leading.len() + arity
                    && !self.lazy_constants.contains(id);
                let function = identifier_expression(self.function_reference(*id));
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

    pub(super) fn loop_variable(
        &mut self,
        callback: &Callback<'_>,
        position: usize,
        base: &str,
    ) -> String {
        match callback {
            Callback::Inline { parameters, body } => {
                let parameter = parameters[position];
                if uses_local(body, parameter.id) { self.bind_local(parameter) } else { "_".into() }
            }
            Callback::Direct { .. } => self.temporary(base),
        }
    }

    pub(super) fn apply_callback(
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

    pub(super) fn callback_value(
        &mut self,
        callback: &Callback<'_>,
        arguments: Vec<GoExpression>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        match callback {
            Callback::Inline { body, .. } => self.value(body, out),
            Callback::Direct { function, callee, leading } => {
                let mut all = leading.clone();
                all.extend(arguments);
                let applied = call(function.clone(), all);
                if !self.is_unit(self.program.function(*callee).result) {
                    return Ok(applied);
                }
                out.push(GoStatement::Expression(applied));
                Ok(unit_value())
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
        let (accumulator_position, element_position, order) = match iteration {
            Iteration::FoldLeft => (0, 1, Order::Forward),
            _ => (1, 0, Order::Backward),
        };
        let initial = self.value(initial, out)?;
        let absorbing = self.absorbing_pattern(&callback, accumulator_position)?;
        let demand = Demand { order, breaks: absorbing.is_some(), ..Demand::FORWARD };
        let need = Need::Argument { callback: &callback, position: element_position };
        let pipeline = self.pipeline(array, demand, need, out)?;
        let accumulator = self.temporary("accumulator");
        let string_appends = self.owned_string_appends(&callback, accumulator_position, monotype);
        let buffered = !string_appends.is_empty();
        if buffered {
            let names = vec![accumulator.clone()];
            out.push(GoStatement::Define { names, values: vec![to_bytes(initial)] });
        } else {
            out.push(self.define(accumulator.clone(), initial, monotype)?);
        }
        let callback = self.owning_callback(callback, accumulator_position, &accumulator, out);
        let owned = self.owned_arrays(&callback, accumulator_position, monotype);
        for (place, _) in &owned {
            out.push(self.clip(&accumulator, place, monotype));
        }
        let owned_places: Vec<Vec<*const Expression>> = owned
            .iter()
            .map(|(_, nodes)| nodes.iter().map(|node| std::ptr::from_ref(*node)).collect())
            .collect();
        let owned_nodes: Vec<*const Expression> = owned_places
            .iter()
            .flatten()
            .copied()
            .chain(string_appends.into_iter().map(std::ptr::from_ref))
            .collect();
        self.owned_snocs.extend(owned_nodes.iter().copied());
        let flags = match &callback {
            Callback::Inline { body, .. } => self.own_updates(body, &owned_places),
            Callback::Direct { .. } => vec![],
        };
        let saved = self.tail_loop.take();
        let positions = (accumulator_position, element_position);
        let outcome = self.fold_loop(
            &callback,
            pipeline,
            positions,
            (&accumulator, absorbing.as_ref()),
            buffered,
            monotype,
        );
        self.tail_loop = saved;
        for node in &owned_nodes {
            self.owned_snocs.remove(node);
        }
        let flags = self.release_updates(&owned_places, flags);
        out.extend(flags);
        out.push(outcome?);
        if buffered {
            let built = self.temporary("built");
            let value = to_string(identifier_expression(&accumulator));
            out.push(GoStatement::Define { names: vec![built.clone()], values: vec![value] });
            return Ok(identifier_expression(&built));
        }
        Ok(identifier_expression(&accumulator))
    }

    fn fold_loop(
        &mut self,
        callback: &Callback<'_>,
        pipeline: Pipeline<'_>,
        (accumulator_position, element_position): (usize, usize),
        (accumulator, absorbing): (&str, Option<&Pattern>),
        buffered: bool,
        monotype: MonotypeId,
    ) -> GoResult<GoStatement> {
        let parameter = match callback {
            Callback::Inline { parameters, .. } if buffered => {
                let buffer = identifier_expression(accumulator);
                self.locals.insert(parameters[accumulator_position].id, buffer);
                "_".to_string()
            }
            _ => self.loop_variable(callback, accumulator_position, "accumulated"),
        };
        let need = Need::Argument { callback, position: element_position };
        let mut opened = self.open(pipeline, need, None)?;
        if let Some(pattern) = absorbing.filter(|_| !buffered) {
            let mut tests = vec![];
            let path = identifier_expression(accumulator);
            self.pattern_tests(pattern, path, &mut tests, &mut vec![])?;
            if let Some(absorbed) = conjunction(tests) {
                opened.body.body().push(GoStatement::If {
                    condition: absorbed,
                    then: vec![GoStatement::Break],
                    otherwise: vec![],
                });
            }
        }
        if parameter != "_" {
            opened.body.body().push(GoStatement::Define {
                names: vec![parameter.clone()],
                values: vec![identifier_expression(accumulator)],
            });
        }
        let mut arguments = vec![identifier_expression(&parameter)];
        arguments.insert(element_position, opened.element);
        let sink = Sink::Assign(accumulator.to_string());
        self.apply_callback(callback, arguments, monotype, sink, opened.body.body())?;
        Ok(self.close(opened.body))
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
        let function = self.program.function(*callee);
        let monotype = function.parameters[position].monotype;
        let updated = updated_arrays(&function.body);
        for (place, nodes) in &owned {
            let writes = nodes.iter().any(|node| updated.contains(&std::ptr::from_ref(*node)));
            match writes {
                true => out.push(self.copy(accumulator, place)),
                false => out.push(self.clip(accumulator, place, monotype)),
            }
        }
        let Callback::Direct { callee, leading, .. } = callback else { unreachable!() };
        let function = identifier_expression(&self.owning_variant_name(callee, position));
        Callback::Direct { function, callee, leading }
    }

    fn owned_arrays<'e>(
        &mut self,
        callback: &Callback<'e>,
        accumulator_position: usize,
        monotype: MonotypeId,
    ) -> Vec<(Place, Vec<&'e Expression>)> {
        let Callback::Inline { parameters, body } = callback else { return vec![] };
        let accumulator = parameters[accumulator_position].id;
        let body: &'e Expression = body;
        self.carried_places(monotype)
            .into_iter()
            .filter_map(|place| {
                let nodes = owned_snocs(Carried::updating(accumulator, &place), body)?;
                (!nodes.is_empty()).then_some((place, nodes))
            })
            .collect()
    }

    /// The places of an accumulator of this type that hold an array: itself, its record's
    /// fields, or a field of one of its constructors when it is held by value.
    pub(super) fn carried_places(&mut self, monotype: MonotypeId) -> Vec<Place> {
        let is_array = |emitter: &mut Self, monotype: MonotypeId| {
            matches!(emitter.monotypes.get(monotype), Monotype::Array(_) | Monotype::Object(_))
                || emitter.is_native_hash_map(monotype)
        };
        match self.monotypes.get(monotype).clone() {
            Monotype::Array(_) | Monotype::Object(_) => vec![Place::Whole],
            Monotype::ForeignData(_) if self.is_native_hash_map(monotype) => vec![Place::Whole],
            // A rank-N value's instantiations are functions, never arrays.
            Monotype::Record(_) if self.monotypes.is_instantiated_record(monotype) => vec![],
            Monotype::Record(fields) => {
                let mut places = vec![];
                for field in fields.iter() {
                    if is_array(self, field.monotype) {
                        let go_field = self.record_field_name(monotype, &field.label);
                        places.push(Place::Field(field.label.clone(), go_field));
                    }
                }
                places
            }
            Monotype::Data(data) => {
                // Laying a type out declares it where the declarations stand, so only a type
                // the emitted code has already laid out, as the accumulator's, is considered.
                let Some(layout) = self.data_layouts.get(&data).cloned() else { return vec![] };
                if layout.boxed || layout.kind == super::DataKind::Enumeration {
                    return vec![];
                }
                let mut places = vec![];
                for (constructor, constructor_layout) in layout.constructors.iter().enumerate() {
                    for (index, (go_field, field)) in constructor_layout.fields.iter().enumerate() {
                        if is_array(self, *field) {
                            let go_field = go_field.clone();
                            places.push(Place::Constructor { constructor, index, go_field });
                        }
                    }
                }
                places
            }
            _ => vec![],
        }
    }

    fn copy(&mut self, accumulator: &str, place: &Place) -> GoStatement {
        let carried = carried_place(accumulator, place);
        self.imports.insert("slices".into());
        let clone = GoExpression::Qualified { package: "slices".into(), name: "Clone".into() };
        GoStatement::Assign {
            targets: vec![carried.clone()],
            values: vec![call(clone, vec![carried])],
        }
    }

    pub(super) fn clip(
        &mut self,
        accumulator: &str,
        place: &Place,
        monotype: MonotypeId,
    ) -> GoStatement {
        let carried = carried_place(accumulator, place);
        let clip = match self.carried_monotype(monotype, place) {
            Some(carried) if matches!(self.monotypes.get(carried), Monotype::Object(_)) => {
                self.go_function(GoFunction { package: GoPackage::Object, name: "Lend" })
            }
            Some(carried) if self.is_native_hash_map(carried) => {
                self.go_function(crate::foreign::HASH_MAP_LEND)
            }
            _ => {
                self.imports.insert("slices".into());
                GoExpression::Qualified { package: "slices".into(), name: "Clip".into() }
            }
        };
        GoStatement::Assign {
            targets: vec![carried.clone()],
            values: vec![call(clip, vec![carried])],
        }
    }

    fn carried_monotype(&self, monotype: MonotypeId, place: &Place) -> Option<MonotypeId> {
        match (self.monotypes.get(monotype), place) {
            (_, Place::Whole) => Some(monotype),
            (Monotype::Record(fields), Place::Field(label, _)) => {
                fields.iter().find(|field| &field.label == label).map(|field| field.monotype)
            }
            (Monotype::Data(data), Place::Constructor { constructor, index, .. }) => self
                .data_layouts
                .get(data)
                .and_then(|layout| layout.constructors.get(*constructor))
                .and_then(|constructor| constructor.fields.get(*index))
                .map(|(_, field)| *field),
            _ => None,
        }
    }

    fn is_native_hash_map(&mut self, monotype: MonotypeId) -> bool {
        let Monotype::ForeignData(data) = self.monotypes.get(monotype).clone() else {
            return false;
        };
        matches!(crate::monotype::native_hash_map(&mut self.context, &data), Ok(Some(true)))
    }

    fn map(
        &mut self,
        iteration: Iteration,
        callback: Callback<'_>,
        array: &Expression,
        monotype: MonotypeId,
        recycled: Option<Recycled>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let indexed = iteration == Iteration::MapWithIndex;
        let demand = Demand { positions: indexed, ..Demand::FORWARD };
        let need = Need::Argument { callback: &callback, position: usize::from(indexed) };
        let pipeline = self.pipeline(array, demand, need, out)?;
        let mapped_type = self.go_type(monotype)?;
        let mapped = self.temporary("mapped");
        let positional_length = pipeline.known_length();
        let in_place = positional_length.is_some();
        let allocation = match (&recycled, positional_length) {
            (Some(recycled), count) => self.recycled_buffer(recycled, count),
            (None, Some(count)) => {
                call(identifier_expression("make"), vec![GoExpression::Type(mapped_type), count])
            }
            (None, None) => GoExpression::Composite { type_: mapped_type, fields: vec![] },
        };
        out.push(GoStatement::Define { names: vec![mapped.clone()], values: vec![allocation] });
        let saved = self.tail_loop.take();
        let outcome = self.map_loop(indexed, &callback, pipeline, &mapped, in_place);
        self.tail_loop = saved;
        out.push(outcome?);
        if let Some(recycled) = &recycled {
            out.push(Self::rotate(recycled, &mapped));
        }
        Ok(identifier_expression(&mapped))
    }

    fn map_loop(
        &mut self,
        indexed: bool,
        callback: &Callback<'_>,
        pipeline: Pipeline<'_>,
        mapped: &str,
        in_place: bool,
    ) -> GoResult<GoStatement> {
        let index = if indexed { self.loop_variable(callback, 0, "index") } else { "_".into() };
        let slot = in_place.then_some(if index == "_" { "index" } else { "slot" });
        let need = Need::Argument { callback, position: usize::from(indexed) };
        let mut opened = self.open(pipeline, need, slot)?;
        let mut arguments = vec![opened.element];
        if indexed && index != "_" {
            let slot =
                opened.index.as_deref().expect("invariant violated: an indexed map has a slot");
            opened.body.body().push(GoStatement::Define {
                names: vec![index.clone()],
                values: vec![identifier_expression(slot)],
            });
            arguments.insert(0, identifier_expression(&index));
        }
        let value = self.callback_value(callback, arguments, opened.body.body())?;
        let statement = match &opened.index {
            Some(slot) => GoStatement::Assign {
                targets: vec![GoExpression::Index {
                    value: Box::new(identifier_expression(mapped)),
                    index: Box::new(identifier_expression(slot)),
                }],
                values: vec![value],
            },
            None => GoStatement::Assign {
                targets: vec![identifier_expression(mapped)],
                values: vec![call(
                    identifier_expression("append"),
                    vec![identifier_expression(mapped), value],
                )],
            },
        };
        opened.body.body().push(statement);
        Ok(self.close(opened.body))
    }

    fn filter(
        &mut self,
        callback: Callback<'_>,
        array: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let need = Need::Variable { callback: &callback, position: 0 };
        let pipeline = self.pipeline(array, Demand::FORWARD, need, out)?;
        let kept_type = self.go_type(monotype)?;
        let kept = self.temporary("kept");
        out.push(GoStatement::Define {
            names: vec![kept.clone()],
            values: vec![GoExpression::Composite { type_: kept_type, fields: vec![] }],
        });
        let saved = self.tail_loop.take();
        let outcome = self.filter_loop(&callback, pipeline, &kept);
        self.tail_loop = saved;
        out.push(outcome?);
        Ok(identifier_expression(&kept))
    }

    fn filter_loop(
        &mut self,
        callback: &Callback<'_>,
        pipeline: Pipeline<'_>,
        kept: &str,
    ) -> GoResult<GoStatement> {
        let need = Need::Variable { callback, position: 0 };
        let mut opened = self.open(pipeline, need, None)?;
        let element = opened.element.clone();
        let condition = self.callback_value(callback, vec![element.clone()], opened.body.body())?;
        let appended =
            call(identifier_expression("append"), vec![identifier_expression(kept), element]);
        opened.body.body().push(GoStatement::If {
            condition,
            then: vec![GoStatement::Assign {
                targets: vec![identifier_expression(kept)],
                values: vec![appended],
            }],
            otherwise: vec![],
        });
        Ok(self.close(opened.body))
    }

    fn search(
        &mut self,
        iteration: Iteration,
        callback: Callback<'_>,
        array: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let demand = Demand { breaks: true, ..Demand::FORWARD };
        let need = Need::Argument { callback: &callback, position: 0 };
        let pipeline = self.pipeline(array, demand, need, out)?;
        let looking_for = iteration == Iteration::Any;
        let found = self.temporary(if looking_for { "found" } else { "every" });
        out.push(GoStatement::Define {
            names: vec![found.clone()],
            values: vec![GoExpression::Boolean(!looking_for)],
        });
        let saved = self.tail_loop.take();
        let outcome = self.search_loop(looking_for, &callback, pipeline, &found);
        self.tail_loop = saved;
        out.push(outcome?);
        Ok(identifier_expression(&found))
    }

    fn search_loop(
        &mut self,
        looking_for: bool,
        callback: &Callback<'_>,
        pipeline: Pipeline<'_>,
        found: &str,
    ) -> GoResult<GoStatement> {
        let need = Need::Argument { callback, position: 0 };
        let mut opened = self.open(pipeline, need, None)?;
        let condition = self.callback_value(callback, vec![opened.element], opened.body.body())?;
        let condition = if looking_for { condition } else { negated(&condition) };
        opened.body.body().push(GoStatement::If {
            condition,
            then: vec![
                GoStatement::Assign {
                    targets: vec![identifier_expression(found)],
                    values: vec![GoExpression::Boolean(looking_for)],
                },
                GoStatement::Break,
            ],
            otherwise: vec![],
        });
        Ok(self.close(opened.body))
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
        let need = Need::Argument { callback: &callback, position: 0 };
        let pipeline = self.pipeline(array, Demand::FORWARD, need, out)?;
        let bound_type = self.go_type(monotype)?;
        let bound = self.temporary("bound");
        let allocation = match bound_capacity(&callback, &pipeline) {
            Some(capacity) => call(
                identifier_expression("make"),
                vec![GoExpression::Type(bound_type), GoExpression::Integer(0), capacity],
            ),
            None => GoExpression::Composite { type_: bound_type, fields: vec![] },
        };
        out.push(GoStatement::Define { names: vec![bound.clone()], values: vec![allocation] });
        let saved = self.tail_loop.take();
        let outcome = match self.nested_pipeline(&callback) {
            Some(_) => {
                let Monotype::Array(produces) = *self.monotypes.get(monotype) else {
                    unreachable!("invariant violated: concatMap produces an array")
                };
                let pipeline = pipeline.then_bind(callback, produces);
                self.append_loop(pipeline, &bound)
            }
            None => self.bind_loop(&callback, pipeline, &bound),
        };
        self.tail_loop = saved;
        out.push(outcome?);
        Ok(identifier_expression(&bound))
    }

    /// Appends every element a pipeline produces, one at a time.
    fn append_loop(&mut self, pipeline: Pipeline<'_>, appended: &str) -> GoResult<GoStatement> {
        let mut opened = self.open(pipeline, Need::Value, None)?;
        let element = if opened.spread {
            GoExpression::Spread(Box::new(opened.element))
        } else {
            opened.element
        };
        let value =
            call(identifier_expression("append"), vec![identifier_expression(appended), element]);
        opened.body.body().push(GoStatement::Assign {
            targets: vec![identifier_expression(appended)],
            values: vec![value],
        });
        Ok(self.close(opened.body))
    }

    fn bind_loop(
        &mut self,
        callback: &Callback<'_>,
        pipeline: Pipeline<'_>,
        bound: &str,
    ) -> GoResult<GoStatement> {
        let need = Need::Argument { callback, position: 0 };
        let mut opened = self.open(pipeline, need, None)?;
        if let Callback::Inline { body, .. } = callback {
            let appended = Sink::Append(bound.to_string());
            self.sink(body, Mode::Value, appended, opened.body.body())?;
            return Ok(self.close(opened.body));
        }
        let produced = self.callback_value(callback, vec![opened.element], opened.body.body())?;
        let appended = call(
            identifier_expression("append"),
            vec![identifier_expression(bound), GoExpression::Spread(Box::new(produced))],
        );
        opened.body.body().push(GoStatement::Assign {
            targets: vec![identifier_expression(bound)],
            values: vec![appended],
        });
        Ok(self.close(opened.body))
    }

    fn find_index(
        &mut self,
        iteration: Iteration,
        callback: Callback<'_>,
        array: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let order = match iteration {
            Iteration::FindIndex => Order::Forward,
            _ => Order::Backward,
        };
        let demand = Demand { order, positions: true, breaks: true, nested: false };
        let need = Need::Argument { callback: &callback, position: 0 };
        let pipeline = self.pipeline(array, demand, need, out)?;
        let (data, nothing) = self.constructor_named(monotype, "Nothing")?;
        let (_, just) = self.constructor_named(monotype, "Just")?;
        let found = self.temporary("found");
        let absent = self.construct(&data, nothing, vec![])?;
        out.push(GoStatement::Define { names: vec![found.clone()], values: vec![absent] });
        let saved = self.tail_loop.take();
        let outcome = self.find_loop(&callback, pipeline, (&data, just), &found);
        self.tail_loop = saved;
        out.push(outcome?);
        Ok(identifier_expression(&found))
    }

    fn find_element(
        &mut self,
        callback: Callback<'_>,
        array: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let demand = Demand { breaks: true, ..Demand::FORWARD };
        let need = Need::Variable { callback: &callback, position: 0 };
        let pipeline = self.pipeline(array, demand, need, out)?;
        let (data, nothing) = self.constructor_named(monotype, "Nothing")?;
        let (_, just) = self.constructor_named(monotype, "Just")?;
        let found = self.temporary("found");
        let absent = self.construct(&data, nothing, vec![])?;
        out.push(GoStatement::Define { names: vec![found.clone()], values: vec![absent] });
        let saved = self.tail_loop.take();
        let outcome = self.find_element_loop(&callback, pipeline, (&data, just), &found);
        self.tail_loop = saved;
        out.push(outcome?);
        Ok(identifier_expression(&found))
    }

    fn find_element_loop(
        &mut self,
        callback: &Callback<'_>,
        pipeline: Pipeline<'_>,
        (data, just): (&DataType, usize),
        found: &str,
    ) -> GoResult<GoStatement> {
        let need = Need::Variable { callback, position: 0 };
        let mut opened = self.open(pipeline, need, None)?;
        let element = opened.element.clone();
        let condition = self.callback_value(callback, vec![element.clone()], opened.body.body())?;
        let present = self.construct(data, just, vec![element])?;
        opened.body.body().push(GoStatement::If {
            condition,
            then: vec![
                GoStatement::Assign {
                    targets: vec![identifier_expression(found)],
                    values: vec![present],
                },
                GoStatement::Break,
            ],
            otherwise: vec![],
        });
        Ok(self.close(opened.body))
    }

    fn find_loop(
        &mut self,
        callback: &Callback<'_>,
        pipeline: Pipeline<'_>,
        (data, just): (&DataType, usize),
        found: &str,
    ) -> GoResult<GoStatement> {
        let need = Need::Argument { callback, position: 0 };
        let mut opened = self.open(pipeline, need, Some("index"))?;
        let index = opened.index.clone().expect("invariant violated: a search by index has one");
        let condition = self.callback_value(callback, vec![opened.element], opened.body.body())?;
        let present = self.construct(data, just, vec![identifier_expression(&index)])?;
        opened.body.body().push(GoStatement::If {
            condition,
            then: vec![
                GoStatement::Assign {
                    targets: vec![identifier_expression(found)],
                    values: vec![present],
                },
                GoStatement::Break,
            ],
            otherwise: vec![],
        });
        Ok(self.close(opened.body))
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
        let unit_valued = mode == Mode::Value && !delayed && self.is_unit(result);
        let result_type =
            if unit_valued { Some(GoType::EmptyStruct) } else { self.go_result(result)? };
        let result_sink = if unit_valued { Sink::Discard } else { Sink::Return };
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
                self.sink(lambda_body, mode, result_sink, &mut body)
            }
            None if !delayed
                && !unit_valued
                && arity > 1
                && self.arity(function.monotype) == arity =>
            {
                let value = self.value(function, out)?;
                self.tail_loop = saved;
                return Ok(value);
            }
            found => {
                let mut arguments = vec![];
                for &monotype in &parameter_monotypes {
                    let base = self.value_base(monotype);
                    let name = self.temporary(&base);
                    arguments.push(identifier_expression(&name));
                    parameters.push((name, self.go_type(monotype)?));
                }
                let applied = match found {
                    Some(Found::Direct { function: name, leading, .. })
                        if leading.is_empty() && !delayed && !unit_valued =>
                    {
                        self.tail_loop = saved;
                        return Ok(name);
                    }
                    Some(Found::Direct { function: name, leading, .. }) => {
                        let mut values = vec![];
                        for argument in leading {
                            let base = self.value_base(argument.monotype);
                            let value = self.value(argument, out)?;
                            values.push(self.hoist(value, &base, out));
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
                self.deliver(applied, result, result_sink, &mut body)
            }
        };
        self.tail_loop = saved;
        outcome?;
        if unit_valued {
            body.push(GoStatement::Return(Some(unit_value())));
        }
        if let Some(GoStatement::Return(None)) = body.last() {
            body.pop();
        }
        Ok(GoExpression::Function { parameters, result: result_type, body })
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    fn absorbing_pattern(
        &mut self,
        callback: &Callback<'_>,
        accumulator_position: usize,
    ) -> GoResult<Option<Pattern>> {
        let Callback::Inline { parameters, body } = callback else { return Ok(None) };
        let accumulator = parameters[accumulator_position].id;
        let ExpressionKind::Case { scrutinees, alternatives } = &body.kind else {
            return Ok(None);
        };
        let [scrutinee] = scrutinees.as_slice() else { return Ok(None) };
        if !matches!(scrutinee.kind, ExpressionKind::Local(id) if id == accumulator) {
            return Ok(None);
        }
        let mut earlier = vec![];
        let mut covering = true;
        for alternative in alternatives {
            let [pattern] = alternative.patterns.as_slice() else { return Ok(None) };
            let Guarded::Unconditional(result) = &alternative.body else { return Ok(None) };
            let (constructor, fields) = match &pattern.kind {
                PatternKind::Constructor { constructor, arguments, .. } => {
                    (*constructor, arguments)
                }
                PatternKind::Wildcard if covering => {
                    return self.remaining_nullary(result, &earlier, pattern.monotype);
                }
                _ => return Ok(None),
            };
            if earlier.contains(&constructor) {
                return Ok(None);
            }
            if reproduces(result, accumulator, constructor, fields) {
                return Ok(Some(pattern.clone()));
            }
            covering &= fields.iter().all(|field| {
                matches!(field.kind, PatternKind::Wildcard | PatternKind::Variable(_))
            });
            earlier.push(constructor);
        }
        Ok(None)
    }

    fn remaining_nullary(
        &mut self,
        result: &Expression,
        earlier: &[usize],
        monotype: MonotypeId,
    ) -> GoResult<Option<Pattern>> {
        let ExpressionKind::Construct { data, constructor, arguments } = &result.kind else {
            return Ok(None);
        };
        if !arguments.is_empty() || earlier.contains(constructor) {
            return Ok(None);
        }
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&self.current_definition()))?;
        if constructors.len() != earlier.len() + 1 {
            return Ok(None);
        }
        let data = data.clone();
        let kind = PatternKind::Constructor { data, constructor: *constructor, arguments: vec![] };
        Ok(Some(Pattern { kind, monotype }))
    }
}

fn reproduces(
    result: &Expression,
    accumulator: LocalId,
    constructor: usize,
    fields: &[Pattern],
) -> bool {
    match &result.kind {
        ExpressionKind::Local(id) => *id == accumulator,
        ExpressionKind::Construct { constructor: built, arguments, .. } => {
            *built == constructor
                && arguments.len() == fields.len()
                && arguments.iter().zip(fields).all(|(argument, field)| {
                    matches!(
                        (&argument.kind, &field.kind),
                        (ExpressionKind::Local(id), PatternKind::Variable(local)) if *id == local.id
                    )
                })
        }
        _ => false,
    }
}

fn bound_capacity(callback: &Callback<'_>, pipeline: &Pipeline<'_>) -> Option<GoExpression> {
    let Callback::Inline { body, .. } = callback else { return None };
    let most = most_literal_elements(body)?;
    let known = pipeline.known_length()?;
    Some(match (most, known) {
        (most, GoExpression::Integer(count)) => GoExpression::Integer(count * most as i64),
        (1, known) => known,
        (most, known) => binary("*", GoExpression::Integer(most as i64), known),
    })
}

fn most_literal_elements(expression: &Expression) -> Option<usize> {
    match &expression.kind {
        ExpressionKind::Array(elements) => Some(elements.len()),
        ExpressionKind::Fail(_) => Some(0),
        ExpressionKind::Let { body, .. } => most_literal_elements(body),
        ExpressionKind::If { then, otherwise, .. } => {
            Some(most_literal_elements(then)?.max(most_literal_elements(otherwise)?))
        }
        ExpressionKind::Case { alternatives, .. } => {
            alternatives.iter().try_fold(0, |most, alternative| {
                let produced = match &alternative.body {
                    Guarded::Unconditional(body) => most_literal_elements(body)?,
                    Guarded::Guards(branches) => branches.iter().try_fold(0, |most, branch| {
                        Some(most_literal_elements(&branch.body)?.max(most))
                    })?,
                };
                Some(produced.max(most))
            })
        }
        _ => None,
    }
}

fn carried_place(accumulator: &str, place: &Place) -> GoExpression {
    match place {
        Place::Whole => identifier_expression(accumulator),
        Place::Field(_, go_field) => super::field(identifier_expression(accumulator), go_field),
        Place::Constructor { go_field, .. } => {
            super::field(identifier_expression(accumulator), go_field)
        }
    }
}
