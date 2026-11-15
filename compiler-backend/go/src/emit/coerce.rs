use rustc_hash::FxHashSet;

use super::packages::Spelling;
use super::{
    DataKind, Emitter, binary, call, field, identifier_expression, is_simple,
    is_untyped_constant, path_root, unit_value,
};
use crate::erasure::Erasure;
use crate::error::{GoError, GoResult};
use crate::foreign::{GoFunction, GoPackage};
use crate::monotype::{DataType, Monotype, MonotypeId, RecordField};
use crate::syntax::{GoCase, GoDeclaration, GoDefault, GoExpression, GoStatement, GoType};
use crate::walk::each_block;

/// The construct a coercion between types of different shapes reports.
pub(super) const UNRELATED_TYPES: &str = "representation changes between unrelated types";

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn coerce(
        &mut self,
        value: GoExpression,
        from: MonotypeId,
        to: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if from == to || self.same_go_type(from, to)? {
            return Ok(value);
        }
        match (self.monotypes.get(from).clone(), self.monotypes.get(to).clone()) {
            (Monotype::Recursive(data), _) => {
                let unfolded = self.unfold(&data)?;
                self.coerce(value, unfolded, to, out)
            }
            (_, Monotype::Recursive(data)) => {
                let unfolded = self.unfold(&data)?;
                self.coerce(value, from, unfolded, out)
            }
            (Monotype::Record(fields), Monotype::Opaque) => {
                let record = self.shared(value, "original", out);
                let mut entries = Vec::with_capacity(fields.len());
                for record_field in fields.iter() {
                    let field_value = self.read_field(record.clone(), from, &record_field.label);
                    entries.push((
                        record_field.label.to_string(),
                        field_value,
                        record_field.monotype,
                    ));
                }
                self.foreign_record(entries, out)
            }
            (Monotype::Opaque, Monotype::Record(fields)) => {
                let record = self.shared(value, "original", out);
                let read = self
                    .go_function(GoFunction { package: GoPackage::Direct, name: "ForeignField" });
                let mut values = Vec::with_capacity(fields.len());
                for record_field in fields.iter() {
                    let label = GoExpression::String(record_field.label.to_string());
                    let field_value = call(read.clone(), vec![record.clone(), label]);
                    let field_value = self.coerce(field_value, from, record_field.monotype, out)?;
                    values.push((record_field.label.clone(), field_value));
                }
                self.record_value(to, values)
            }
            // A function at its erased polymorphic type becomes a specialized
            // rank-N value: each instantiation is the function used at it.
            (Monotype::Function(..), Monotype::Record(fields)) => {
                if fields.is_empty() {
                    let type_ = GoType::Named(self.record_name(to)?);
                    return Ok(GoExpression::Composite { type_, fields: vec![] });
                }
                let function = self.shared(value, "original", out);
                let mut values = Vec::with_capacity(fields.len());
                for record_field in fields.iter() {
                    let instance =
                        self.coerce(function.clone(), from, record_field.monotype, out)?;
                    values.push((record_field.label.clone(), instance));
                }
                self.record_value(to, values)
            }
            (Monotype::Array(_), Monotype::Opaque) => {
                let foreign_array = self.monotypes.intern(Monotype::Array(to));
                self.coerce(value, from, foreign_array, out)
            }
            (Monotype::Opaque, Monotype::Array(_)) => {
                let foreign_array = self.monotypes.intern(Monotype::Array(from));
                let type_ = self.go_type(foreign_array)?;
                let value = GoExpression::TypeAssertion { value: Box::new(value), type_ };
                self.coerce(value, foreign_array, to, out)
            }
            (_, Monotype::Erased(_) | Monotype::Opaque) => {
                let canonical = self.canonical(from);
                let value = self.coerce(value, from, canonical, out)?;
                if is_untyped_constant(&value) {
                    let type_ = self.go_type(canonical)?;
                    return Ok(GoExpression::Conversion { type_, value: Box::new(value) });
                }
                Ok(value)
            }
            (Monotype::Erased(_) | Monotype::Opaque, _) => {
                let canonical = self.canonical(to);
                let type_ = self.go_type(canonical)?;
                let value = GoExpression::TypeAssertion { value: Box::new(value), type_ };
                self.coerce(value, canonical, to, out)
            }
            (Monotype::Function(..), Monotype::Function(..)) => {
                let function = self.shared(value, "original", out);
                self.coerce_function(function, from, to)
            }
            (Monotype::Lazy(from_result), Monotype::Lazy(to_result)) => {
                let lazy = self.shared(value, "original", out);
                let mut body = vec![];
                let forced = call(field(lazy, "Force"), vec![]);
                self.coerce_returned(forced, from_result, to_result, &mut body)?;
                self.lazy_cell(to_result, body)
            }
            (Monotype::Effect(from_result), Monotype::Effect(to_result)) => {
                let action = self.shared(value, "original", out);
                let mut body = vec![];
                let performed = call(action, vec![]);
                self.coerce_returned(performed, from_result, to_result, &mut body)?;
                let result = self.go_result(to_result)?;
                Ok(GoExpression::Function { parameters: vec![], result, body })
            }
            (Monotype::Array(_), Monotype::Array(_))
            | (Monotype::Nullable(_), Monotype::Nullable(_))
            | (Monotype::Record(_), Monotype::Record(_))
            | (Monotype::Data(_), Monotype::Data(_)) => {
                let converter = self.converter(from, to)?;
                Ok(call(identifier_expression(&converter), vec![value]))
            }
            // JavaScript represents a Char as a string of one code unit, so an `unsafeCoerce`
            // from Char to String (Data.String.NonEmpty.CodeUnits.fromFoldable1) is that string.
            (Monotype::Char, Monotype::String) => {
                let singleton =
                    self.go_function(GoFunction { package: GoPackage::Prim, name: "CharSingleton" });
                Ok(call(singleton, vec![value]))
            }
            // JavaScript turns an array that meets a string (`"" + unsafeCoerce array`) into its
            // elements' strings joined with commas.
            (Monotype::Array(element), Monotype::String) => {
                self.imports.insert("strings".into());
                let join = GoExpression::Qualified { package: "strings".into(), name: "Join".into() };
                let comma = GoExpression::String(",".into());
                if let Monotype::String = self.monotypes.get(element) {
                    return Ok(call(join, vec![value, comma]));
                }
                let parameter = self.temporary("element");
                let mut body = vec![];
                let text = self.coerce(identifier_expression(&parameter), element, to, &mut body)?;
                body.push(GoStatement::Return(Some(text)));
                let render = GoExpression::Function {
                    parameters: vec![(parameter, self.go_type(element)?)],
                    result: Some(GoType::String),
                    body,
                };
                let map = self.go_function(GoFunction { package: GoPackage::Array, name: "Map" });
                Ok(call(join, vec![call(map, vec![render, value]), comma]))
            }
            _ => Err(GoError::unsupported_construct(UNRELATED_TYPES)),
        }
    }

    fn coerce_function(
        &mut self,
        function: GoExpression,
        from: MonotypeId,
        to: MonotypeId,
    ) -> GoResult<GoExpression> {
        let arity = self.arity(to);
        let (to_arguments, to_result) = self.leading_arrows(to, arity);
        let mut parameters = Vec::with_capacity(arity);
        let mut body = vec![];
        let mut callable = self.value_callable(function, from);
        let mut pending = vec![];
        let mut source = from;
        for to_argument in to_arguments {
            if self.monotypes.function_parts(source).is_none() {
                let remaining = self.monotypes.result_after(to, parameters.len());
                let canonical = self.canonical(remaining);
                let type_ = self.go_type(canonical)?;
                let asserted =
                    GoExpression::TypeAssertion { value: Box::new(callable.function), type_ };
                callable = self.value_callable(asserted, canonical);
                source = canonical;
            }
            let (from_argument, from_rest) = self
                .monotypes
                .function_parts(source)
                .expect("invariant violated: a coerced function takes its arguments");
            let parameter = self.temporary("coerced");
            parameters.push((parameter.clone(), self.go_type(to_argument)?));
            let argument = self.coerce(
                identifier_expression(&parameter),
                to_argument,
                from_argument,
                &mut body,
            )?;
            pending.push(argument);
            source = from_rest;
            if pending.len() == callable.arity {
                let invoked = call(callable.function, std::mem::take(&mut pending));
                callable = self.value_callable(invoked, source);
            }
        }
        let invoked = if pending.is_empty() {
            callable.function
        } else {
            self.apply_arguments(callable, pending, &mut body)?
        };
        self.coerce_invocation(invoked, source, to_result, &mut body)?;
        let result = self.invocation_type(to_result)?;
        Ok(GoExpression::Function { parameters, result, body })
    }

    pub(super) fn foreign_record(
        &mut self,
        entries: Vec<(String, GoExpression, MonotypeId)>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let foreign = self.monotypes.intern(Monotype::Opaque);
        let mut keys = Vec::with_capacity(entries.len());
        let mut values = Vec::with_capacity(entries.len());
        for (label, value, monotype) in entries {
            keys.push((None, GoExpression::String(label)));
            values.push((None, self.coerce(value, monotype, foreign, out)?));
        }
        let keys = GoExpression::Composite {
            type_: GoType::Slice(Box::new(GoType::String)),
            fields: keys,
        };
        let values =
            GoExpression::Composite { type_: GoType::Slice(Box::new(GoType::Any)), fields: values };
        let record =
            self.go_function(GoFunction { package: GoPackage::Direct, name: "ForeignRecord" });
        Ok(call(record, vec![keys, values]))
    }

    fn canonical(&mut self, monotype: MonotypeId) -> MonotypeId {
        let erased = self.monotypes.intern(Monotype::Erased(Erasure::Boxing));
        let canonical = match self.monotypes.get(monotype).clone() {
            Monotype::Function(..) => Monotype::Function(erased, erased),
            Monotype::Effect(_) => Monotype::Effect(erased),
            Monotype::Array(_) => Monotype::Array(erased),
            Monotype::MutableArray(_) => Monotype::MutableArray(erased),
            Monotype::Object(_) => Monotype::Object(erased),
            Monotype::Nullable(_) => Monotype::Nullable(erased),
            Monotype::Lazy(_) => Monotype::Lazy(erased),
            Monotype::Record(fields) => {
                let fields = fields
                    .iter()
                    .map(|field| RecordField { label: field.label.clone(), monotype: erased });
                Monotype::Record(fields.collect())
            }
            Monotype::Data(data) => Monotype::Data(self.erase_arguments(&data)),
            Monotype::Recursive(data) => Monotype::Recursive(self.erase_arguments(&data)),
            Monotype::Int
            | Monotype::Number
            | Monotype::Boolean
            | Monotype::Char
            | Monotype::String
            | Monotype::Unit
            | Monotype::Reference(_)
            | Monotype::Error
            | Monotype::Opaque
            | Monotype::Regex
            | Monotype::Mutex
            | Monotype::BigInt
            | Monotype::ForeignData(_)
            | Monotype::Erased(_) => return monotype,
        };
        self.monotypes.intern(canonical)
    }

    fn erase_arguments(&self, data: &DataType) -> DataType {
        let erased = self.context.types.erased(Erasure::Boxing);
        let arguments = data.arguments.iter().map(|_| erased).collect();
        DataType { file_id: data.file_id, item: data.item, arguments }
    }

    pub(super) fn shared(
        &mut self,
        value: GoExpression,
        base: &str,
        out: &mut Vec<GoStatement>,
    ) -> GoExpression {
        let reassigned = path_root(&value).is_some_and(|root| {
            self.tail_loop.as_ref().is_some_and(|tail_loop| tail_loop.parameters.contains(root))
        });
        if is_simple(&value) && !reassigned {
            return value;
        }
        let name = self.temporary(base);
        out.push(GoStatement::Define { names: vec![name.clone()], values: vec![value] });
        identifier_expression(&name)
    }

    fn invocation_type(&mut self, result: MonotypeId) -> GoResult<Option<GoType>> {
        let performed = self.monotypes.effect_result(result).unwrap_or(result);
        self.go_result(performed)
    }

    fn coerce_invocation(
        &mut self,
        invoked: GoExpression,
        from: MonotypeId,
        to: MonotypeId,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        match (self.monotypes.effect_result(from), self.monotypes.effect_result(to)) {
            (Some(from_result), Some(to_result)) => {
                self.coerce_returned(invoked, from_result, to_result, body)
            }
            (None, Some(to_result)) => {
                let action = self.coerce(invoked, from, to, body)?;
                self.coerce_returned(call(action, vec![]), to_result, to_result, body)
            }
            (Some(from_result), None) => {
                let result = self.go_result(from_result)?;
                let mut performed = vec![];
                self.coerce_returned(invoked, from_result, from_result, &mut performed)?;
                let action = GoExpression::Function { parameters: vec![], result, body: performed };
                let effect = self.monotypes.intern(Monotype::Effect(from_result));
                let action = self.coerce(action, effect, to, body)?;
                body.push(GoStatement::Return(Some(action)));
                Ok(())
            }
            (None, None) => self.coerce_returned(invoked, from, to, body),
        }
    }

    fn coerce_returned(
        &mut self,
        invoked: GoExpression,
        from: MonotypeId,
        to: MonotypeId,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        match (self.is_unit(from), self.is_unit(to)) {
            (true, true) => body.push(GoStatement::Expression(invoked)),
            (true, false) => {
                body.push(GoStatement::Expression(invoked));
                let value = self.coerce(unit_value(), from, to, body)?;
                body.push(GoStatement::Return(Some(value)));
            }
            (false, true) => body.push(GoStatement::Expression(invoked)),
            (false, false) => {
                let value = self.coerce(invoked, from, to, body)?;
                body.push(GoStatement::Return(Some(value)));
            }
        }
        Ok(())
    }

    fn converter(&mut self, from: MonotypeId, to: MonotypeId) -> GoResult<String> {
        if let Some(name) = self.converters.get(&(from, to)) {
            return Ok(name.clone());
        }
        let name = self.global_name(Spelling::Base("convert".into()));
        self.converters.insert((from, to), name.clone());
        let parameter_type = self.go_type(from)?;
        let result_type = self.go_type(to)?;
        let value = identifier_expression("value");
        let mut body = vec![];
        match (self.monotypes.get(from).clone(), self.monotypes.get(to).clone()) {
            (Monotype::Array(from_element), Monotype::Array(to_element)) => {
                let empty = GoExpression::Composite { type_: result_type.clone(), fields: vec![] };
                body.push(GoStatement::Define {
                    names: vec!["converted".into()],
                    values: vec![empty],
                });
                let mut each = vec![];
                let element = self.coerce(
                    identifier_expression("element"),
                    from_element,
                    to_element,
                    &mut each,
                )?;
                each.push(GoStatement::Assign {
                    targets: vec![identifier_expression("converted")],
                    values: vec![call(
                        identifier_expression("append"),
                        vec![identifier_expression("converted"), element],
                    )],
                });
                body.push(GoStatement::Range {
                    index: None,
                    element: "element".into(),
                    iterable: value,
                    body: each,
                });
                body.push(GoStatement::Return(Some(identifier_expression("converted"))));
            }
            (Monotype::Nullable(from_element), Monotype::Nullable(to_element)) => {
                let absent = binary("==", value.clone(), identifier_expression("nil"));
                body.push(GoStatement::If {
                    condition: absent,
                    then: vec![GoStatement::Return(Some(identifier_expression("nil")))],
                    otherwise: vec![],
                });
                let present = GoExpression::Unary { operator: "*", operand: Box::new(value) };
                let element = self.coerce(present, from_element, to_element, &mut body)?;
                let type_ = self.go_type(to_element)?;
                body.push(GoStatement::Variable {
                    name: "converted".into(),
                    type_,
                    value: Some(element),
                });
                let converted = GoExpression::Address(Box::new(identifier_expression("converted")));
                body.push(GoStatement::Return(Some(converted)));
            }
            (Monotype::Record(from_fields), Monotype::Record(to_fields)) => {
                // Records of one row differ only in their fields' representations. Rows that
                // differ arise from a rank-N value whose instantiations at one type were never
                // requested before an `unsafeCoerce` to another (Yoga.Om's `expandErr`).
                let mut fields = vec![];
                for to_field in to_fields.iter() {
                    let Some(from_field) =
                        from_fields.iter().find(|from_field| from_field.label == to_field.label)
                    else {
                        return Err(GoError::unsupported_construct("a coercion between records with different fields (a rank-N value coerced to another instantiation)"));
                    };
                    let field_value = self.read_field(value.clone(), from, &to_field.label);
                    let converted = self.coerce(
                        field_value,
                        from_field.monotype,
                        to_field.monotype,
                        &mut body,
                    )?;
                    fields.push((to_field.label.clone(), converted));
                }
                let converted = self.record_value(to, fields)?;
                body.push(GoStatement::Return(Some(converted)));
            }
            (Monotype::Data(from_data), Monotype::Data(to_data)) => {
                let round_trip = self.convert_data(&from_data, &to_data, value, &mut body)?;
                if let Some(mut round_trip) = round_trip {
                    round_trip.converter = self.type_declarations.len();
                    self.round_trips.push(round_trip);
                }
            }
            _ => unreachable!("invariant violated: converter requested for non-composite types"),
        }
        self.type_declarations.push(GoDeclaration::Function {
            name: name.clone(),
            parameters: vec![("value".into(), parameter_type)],
            result: Some(result_type),
            body,
        });
        Ok(name)
    }

    fn convert_data(
        &mut self,
        from: &DataType,
        to: &DataType,
        value: GoExpression,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<Option<RoundTrip>> {
        let from_layout = self.data_layout(from)?;
        let to_layout = self.data_layout(to)?;
        if from_layout.kind == DataKind::Enumeration {
            let type_ = GoType::Named(to_layout.name);
            body.push(GoStatement::Return(Some(GoExpression::Conversion {
                type_,
                value: Box::new(value),
            })));
            return Ok(None);
        }
        // A typed value converted to an erased layout and back is the original.
        let from_remembers = self.remember_origin(from)?;
        let to_remembers = self.remember_origin(to)?;
        if from_remembers {
            let type_ = to_layout.go_type();
            let origin = field(value.clone(), "Origin");
            body.push(GoStatement::IfAssert {
                name: "original".into(),
                value: origin,
                type_,
                then: vec![GoStatement::Return(Some(identifier_expression("original")))],
            });
        }
        let origin = to_remembers.then(|| value.clone());
        let mut cases = vec![];
        for (constructor, (from_constructor, to_constructor)) in
            from_layout.constructors.iter().zip(to_layout.constructors.iter()).enumerate()
        {
            let mut statements = vec![];
            let mut values = vec![];
            for ((from_field, from_monotype), (_, to_monotype)) in
                from_constructor.fields.iter().zip(to_constructor.fields.iter())
            {
                let field_value = field(value.clone(), from_field);
                values.push(self.coerce(
                    field_value,
                    *from_monotype,
                    *to_monotype,
                    &mut statements,
                )?);
            }
            let mut constructed = self.construct(to, constructor, values)?;
            if let Some(origin) = &origin {
                let composite = match &mut constructed {
                    GoExpression::Address(composite) => composite.as_mut(),
                    composite => composite,
                };
                if let GoExpression::Composite { fields, .. } = composite {
                    fields.push((Some("Origin".into()), origin.clone()));
                }
            }
            statements.push(GoStatement::Return(Some(constructed)));
            cases.push(GoCase {
                values: vec![identifier_expression(&from_constructor.tag)],
                body: statements,
            });
        }
        let round_trip = (from_remembers || to_remembers).then(|| RoundTrip {
            converter: 0,
            from: from_layout.name.clone(),
            to: to_layout.name.clone(),
            checks: from_remembers,
            remembers: to_remembers.then_some(to_layout.declaration).flatten(),
        });
        if from_layout.kind == DataKind::Product {
            let [case] = &mut cases[..] else {
                unreachable!("invariant violated: product data has one constructor")
            };
            body.append(&mut case.body);
            return Ok(round_trip);
        }
        let default = GoDefault::covering(&mut cases);
        body.push(GoStatement::Switch {
            value: Some(field(value, "Tag")),
            cases,
            default: Some(default),
        });
        Ok(round_trip)
    }

    pub(super) fn settle_round_trips(&mut self) {
        let round_trips = std::mem::take(&mut self.round_trips);
        let converted: FxHashSet<(&str, &str)> = round_trips
            .iter()
            .map(|round_trip| (round_trip.from.as_str(), round_trip.to.as_str()))
            .collect();
        let mut remembering = FxHashSet::default();
        let mut filled = FxHashSet::default();
        for round_trip in &round_trips {
            remembering.extend(round_trip.remembers);
            if converted.contains(&(round_trip.to.as_str(), round_trip.from.as_str())) {
                filled.extend(round_trip.remembers);
                continue;
            }
            let GoDeclaration::Function { body, .. } =
                &mut self.type_declarations[round_trip.converter]
            else {
                unreachable!("invariant violated: a round trip names its converter")
            };
            if round_trip.checks {
                body.remove(0);
            }
            if round_trip.remembers.is_some() {
                forget_origins(body);
            }
        }
        for position in remembering.difference(&filled) {
            if let GoDeclaration::Type { type_: GoType::Struct(fields), .. } =
                &mut self.type_declarations[*position]
            {
                fields.retain(|(name, _)| name != "Origin");
            }
        }
    }
}

pub(super) struct RoundTrip {
    converter: usize,
    from: String,
    to: String,
    checks: bool,
    remembers: Option<usize>,
}

fn forget_origins(body: &mut Vec<GoStatement>) {
    each_block(body, |block| {
        for statement in block {
            if let GoStatement::Return(Some(returned)) = statement {
                let composite = match returned {
                    GoExpression::Address(composite) => composite.as_mut(),
                    composite => composite,
                };
                if let GoExpression::Composite { fields, .. } = composite {
                    fields.retain(|(name, _)| name.as_deref() != Some("Origin"));
                }
            }
        }
    })
}
