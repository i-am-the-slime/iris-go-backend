use rustc_hash::FxHashSet;

use super::packages::Spelling;
use super::{
    DataKind, Emitter, binary, call, field, identifier_expression, is_simple, is_untyped_constant,
    length, path_root, unit_value,
};
use crate::erasure::Erasure;
use crate::error::{GoError, GoResult, RepresentationChange};
use crate::foreign::{GoFunction, GoPackage};
use crate::go_traversal::each_block;
use crate::monomorphic::{Expression, ExpressionKind};
use crate::monotype::{DataType, Failure, Monotype, MonotypeId, RecordField};
use crate::syntax::{GoCase, GoDeclaration, GoDefault, GoExpression, GoStatement, GoType};
use smol_str::SmolStr;

/// The construct a coercion between types of different shapes reports.
pub(super) const UNRELATED_TYPES: &str = "representation changes between unrelated types";

/// Where the arguments of a coerced call come from: the application, or the parameters of the
/// closure the call is the body of.
enum Arguments<'p> {
    Given(std::vec::IntoIter<GoExpression>),
    Parameters(&'p mut Vec<(String, GoType)>),
}

const TYPED_EXISTENTIAL: &str = "a typed Data.Exists rebuilt from another representation";

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
        match (self.monotypes.get(from), self.monotypes.get(to)) {
            (Monotype::Opaque, Monotype::Erased(_)) => self.array_boxes.foreign_values_enter = true,
            (Monotype::Erased(_), Monotype::Opaque) => self.array_boxes.erased_values_leave = true,
            _ => {}
        }
        if from == to || self.same_go_type(from, to)? {
            return Ok(value);
        }
        match (self.monotypes.get(from).clone(), self.monotypes.get(to).clone()) {
            (Monotype::Recursive(data), _) if !self.is_uninhabited(&data)? => {
                let unfolded = self.unfold(&data)?;
                self.coerce(value, unfolded, to, out)
            }
            (_, Monotype::Recursive(data)) if !self.is_uninhabited(&data)? => {
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
            (Monotype::Array(_), Monotype::Erased(_)) => self.box_array(value, from, true),
            (Monotype::Erased(_), Monotype::Array(_)) => self.box_array(value, to, false),
            (Monotype::Array(_), Monotype::Opaque) => {
                let type_ = self.go_type(from)?;
                self.array_boxes.cross(from, type_, true);
                let foreign_array = self.monotypes.intern(Monotype::Array(to));
                self.coerce(value, from, foreign_array, out)
            }
            (Monotype::Opaque, Monotype::Array(_)) => {
                let type_ = self.go_type(to)?;
                self.array_boxes.cross(to, type_, true);
                let foreign_array = self.monotypes.intern(Monotype::Array(from));
                let type_ = self.go_type(foreign_array)?;
                let value = GoExpression::TypeAssertion { value: Box::new(value), type_ };
                self.coerce(value, foreign_array, to, out)
            }
            (Monotype::Data(data), Monotype::Record(_))
            | (Monotype::Record(_), Monotype::Data(data))
                if self.monotypes.variant_row(&data).is_some() =>
            {
                let converter = self.converter(from, to)?;
                Ok(call(identifier_expression(&converter), vec![value]))
            }
            (Monotype::Data(data), Monotype::Erased(_) | Monotype::Opaque)
                if self.monotypes.exists_family(&data).is_some() =>
            {
                self.erase_existential(value, from, &data, to)
            }
            (_, Monotype::Data(data)) | (Monotype::Data(data), _)
                if self.monotypes.exists_family(&data).is_some() =>
            {
                Err(GoError::unsupported_construct(TYPED_EXISTENTIAL))
            }
            (_, Monotype::Erased(_) | Monotype::Opaque) => {
                let canonical = self.canonical(from)?;
                self.note_foreign_data(canonical);
                let value = self.coerce(value, from, canonical, out)?;
                if is_untyped_constant(&value) {
                    let type_ = self.go_type(canonical)?;
                    return Ok(GoExpression::Conversion { type_, value: Box::new(value) });
                }
                Ok(value)
            }
            (Monotype::Erased(_) | Monotype::Opaque, _) => {
                let canonical = self.canonical(to)?;
                let type_ = self.go_type(canonical)?;
                let value = GoExpression::TypeAssertion { value: Box::new(value), type_ };
                self.coerce(value, canonical, to, out)
            }
            (Monotype::Function(..), Monotype::Function(..)) => {
                if let GoExpression::Function { .. } = value
                    && let Some(composed) = self.compose_coercion(value.clone(), from, to)?
                {
                    return Ok(composed);
                }
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
                let singleton = self
                    .go_function(GoFunction { package: GoPackage::Prim, name: "CharSingleton" });
                Ok(call(singleton, vec![value]))
            }
            // JavaScript turns an array that meets a string (`"" + unsafeCoerce array`) into its
            // elements' strings joined with commas.
            (Monotype::Array(element), Monotype::String) => {
                self.imports.insert("strings".into());
                let join =
                    GoExpression::Qualified { package: "strings".into(), name: "Join".into() };
                let comma = GoExpression::String(",".into());
                if let Monotype::String = self.monotypes.get(element) {
                    return Ok(call(join, vec![value, comma]));
                }
                let parameter = self.temporary("element");
                let mut body = vec![];
                let text =
                    self.coerce(identifier_expression(&parameter), element, to, &mut body)?;
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
        let mut parameters = Vec::with_capacity(arity);
        let mut body = vec![];
        let closure = Arguments::Parameters(&mut parameters);
        let (invoked, source) = self.coerced_call(function, from, to, closure, &mut body)?;
        let to_result = self.monotypes.result_after(to, parameters.len());
        self.coerce_invocation(invoked, source, to_result, &mut body)?;
        let result = self.invocation_type(to_result)?;
        Ok(GoExpression::Function { parameters, result, body })
    }

    /// A function literal coerced to another function type as one literal, which calls nothing
    /// that the coerced literal did: its body is the literal's, with its own parameters coerced.
    /// `None` where the literal does not reduce into the call, which then calls it by name.
    fn compose_coercion(
        &mut self,
        literal: GoExpression,
        from: MonotypeId,
        to: MonotypeId,
    ) -> GoResult<Option<GoExpression>> {
        let mut composed = self.coerce_function(literal, from, to)?;
        super::immediate::reduce_immediate_calls_in(&mut composed);
        Ok((!super::immediate::calls_a_literal(&composed)).then_some(composed))
    }

    /// Whether `(coerce f) x …`, `f` at `from` seen as `to`, can call `f` where it is applied,
    /// with its arguments and its result coerced, instead of making a closure that is called
    /// once. It can when it takes every argument the closure would and its call returns a value;
    /// a call that performs an effect or returns nothing stays in a closure's body.
    pub(super) fn applies_through_coercion(
        &mut self,
        from: MonotypeId,
        to: MonotypeId,
        supplied: usize,
    ) -> GoResult<bool> {
        let functions = matches!(self.monotypes.get(from), Monotype::Function(..))
            && matches!(self.monotypes.get(to), Monotype::Function(..));
        if !functions || from == to || self.same_go_type(from, to)? {
            return Ok(false);
        }
        let arity = self.arity(to);
        if supplied < arity {
            return Ok(false);
        }
        let (to_arguments, returned) = self.leading_arrows(to, arity);
        let mut source = from;
        for (position, to_argument) in to_arguments.into_iter().enumerate() {
            if self.monotypes.function_parts(source).is_none() {
                source = self.canonical(self.monotypes.result_after(to, position))?;
            }
            let Some((from_argument, rest)) = self.monotypes.function_parts(source) else {
                return Ok(false);
            };
            if self.crosses_interface(to_argument, from_argument)? {
                return Ok(false);
            }
            source = rest;
        }
        let returns_value =
            |monotype| self.monotypes.effect_result(monotype).is_none() && !self.is_unit(monotype);
        Ok(returns_value(source)
            && returns_value(returned)
            && !self.crosses_interface(source, returned)?)
    }

    /// Whether a coercion moves a value into or out of an interface. Only a parameter or a
    /// result of the interface type boxes it in Go, and a value at an erased type may still have
    /// its own, so the closure's signature has to stay.
    fn crosses_interface(&mut self, from: MonotypeId, to: MonotypeId) -> GoResult<bool> {
        let interface = |type_: GoType| matches!(type_, GoType::Any | GoType::Erased(_));
        Ok(interface(self.go_type(to)?) != interface(self.go_type(from)?))
    }

    pub(super) fn coerced_into_interface(&mut self, expression: &Expression) -> GoResult<bool> {
        let ExpressionKind::Coerce(inner) = &expression.kind else { return Ok(false) };
        match self.monotypes.get(expression.monotype) {
            Monotype::Opaque | Monotype::Erased(_) => {}
            _ => return Ok(false),
        }
        match self.monotypes.get(inner.monotype) {
            Monotype::Record(_) => Ok(false),
            Monotype::Opaque | Monotype::Erased(_) => self.coerced_into_interface(inner),
            _ => self.crosses_interface(inner.monotype, expression.monotype),
        }
    }

    /// `(coerce f) x …` where [`Self::applies_through_coercion`] says it can be: `f` called with
    /// the arguments coerced to its own parameters, its result coerced to `to`'s.
    pub(super) fn coerce_applied(
        &mut self,
        function: GoExpression,
        from: MonotypeId,
        to: MonotypeId,
        mut arguments: Vec<GoExpression>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let function = match function {
            literal @ GoExpression::Function { .. } => self.shared(literal, "original", out),
            function => function,
        };
        let rest = arguments.split_off(self.arity(to));
        let given = Arguments::Given(arguments.into_iter());
        let (invoked, source) = self.coerced_call(function, from, to, given, out)?;
        let returned = self.monotypes.result_after(to, self.arity(to));
        if !rest.is_empty() && self.applies_through_coercion(source, returned, rest.len())? {
            return self.coerce_applied(invoked, source, returned, rest, out);
        }
        let result = self.coerce(invoked, source, returned, out)?;
        if rest.is_empty() {
            return Ok(result);
        }
        let callable = self.value_callable(result, returned);
        self.apply_arguments(callable, rest, out)
    }

    /// A function at `from` called as `to` with `to`'s first arguments: the call, and the type
    /// of what it returns. The arguments are given, or become parameters of the closure that
    /// `body` belongs to.
    fn coerced_call(
        &mut self,
        function: GoExpression,
        from: MonotypeId,
        to: MonotypeId,
        mut arguments: Arguments<'_>,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<(GoExpression, MonotypeId)> {
        let arity = self.arity(to);
        let (to_arguments, _) = self.leading_arrows(to, arity);
        let mut callable = self.value_callable(function, from);
        let mut pending = vec![];
        let mut source = from;
        for (position, to_argument) in to_arguments.into_iter().enumerate() {
            if self.monotypes.function_parts(source).is_none() {
                let remaining = self.monotypes.result_after(to, position);
                let canonical = self.canonical(remaining)?;
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
            let argument = match &mut arguments {
                Arguments::Given(given) => given.next().expect("a coerced call has its arguments"),
                Arguments::Parameters(parameters) => {
                    let parameter = self.temporary("coerced");
                    parameters.push((parameter.clone(), self.go_type(to_argument)?));
                    identifier_expression(&parameter)
                }
            };
            let argument = self.coerce(argument, to_argument, from_argument, body)?;
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
            self.apply_arguments(callable, pending, body)?
        };
        Ok((invoked, source))
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

    /// Whether a recursive newtype unfolds through newtypes alone back to
    /// itself, as `Data.Void` does. Unfolding it never reaches another
    /// representation, so a coercion stops at its named empty struct.
    fn is_uninhabited(&mut self, data: &DataType) -> GoResult<bool> {
        let unfolded = self.unfold(data)?;
        self.unfolds_only_to_newtypes(data, unfolded)
    }

    pub(super) fn canonical(&mut self, monotype: MonotypeId) -> GoResult<MonotypeId> {
        let erased = self.monotypes.intern(Monotype::Erased(Erasure::Boxing));
        let canonical = match self.monotypes.get(monotype).clone() {
            Monotype::Function(..) => Monotype::Function(erased, erased),
            Monotype::Effect(_) => Monotype::Effect(erased),
            Monotype::Array(_) => Monotype::Array(erased),
            Monotype::MutableArray(_) => Monotype::MutableArray(erased),
            Monotype::Object(_) => Monotype::Object(erased),
            Monotype::Nullable(_) => Monotype::Nullable(erased),
            Monotype::Lazy(_) => Monotype::Lazy(erased),
            Monotype::ConsList(_) => Monotype::ConsList(erased),
            Monotype::Record(fields) => {
                let fields = fields
                    .iter()
                    .map(|field| RecordField { label: field.label.clone(), monotype: erased });
                Monotype::Record(fields.collect())
            }
            Monotype::Data(data) if self.monotypes.variant_row(&data).is_some() => {
                return Ok(monotype);
            }
            Monotype::Data(data) => Monotype::Data(self.erase_arguments(&data)?),
            Monotype::Recursive(data) => Monotype::Recursive(self.erase_arguments(&data)?),
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
            | Monotype::Int64
            | Monotype::UInt64
            | Monotype::ForeignData(_)
            | Monotype::Erased(_) => return Ok(monotype),
        };
        Ok(self.monotypes.intern(canonical))
    }

    fn erase_arguments(&mut self, data: &DataType) -> GoResult<DataType> {
        let erased = self.context.types.erased(Erasure::Boxing);
        let arguments = data.arguments.iter().map(|_| erased).collect();
        let erased =
            self.monotypes.data_type(&mut self.context, data.file_id, data.item, arguments)?;
        Ok(erased)
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
                self.convert_elements(value, from_element, to_element, &result_type, &mut body)?;
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
                        return Err(GoError::unsupported_construct(
                            "a coercion between records with different fields (a rank-N value coerced to another instantiation)",
                        ));
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
            (Monotype::Data(from_data), Monotype::Record(_))
                if self.monotypes.variant_row(&from_data).is_some() =>
            {
                self.variant_to_representation(&from_data, to, value, &mut body)?;
            }
            (Monotype::Record(_), Monotype::Data(to_data))
                if self.monotypes.variant_row(&to_data).is_some() =>
            {
                self.representation_to_variant(from, &to_data, value, &mut body)?;
            }
            (Monotype::Data(from_data), Monotype::Data(to_data))
                if self.monotypes.variant_row(&from_data).is_some()
                    && self.monotypes.variant_row(&to_data).is_some() =>
            {
                self.convert_variant(&from_data, &to_data, value, &mut body)?;
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

    /// The statements that return an array's elements converted, into a new
    /// array of the result type.
    pub(super) fn convert_elements(
        &mut self,
        array: GoExpression,
        from_element: MonotypeId,
        to_element: MonotypeId,
        result_type: &GoType,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let allocation = call(
            identifier_expression("make"),
            vec![GoExpression::Type(result_type.clone()), length(array.clone())],
        );
        let names = vec!["converted".into()];
        body.push(GoStatement::Define { names, values: vec![allocation] });
        let mut each = vec![];
        let element = identifier_expression("element");
        let element = self.coerce(element, from_element, to_element, &mut each)?;
        let slot = GoExpression::Index {
            value: Box::new(identifier_expression("converted")),
            index: Box::new(identifier_expression("index")),
        };
        each.push(GoStatement::Assign { targets: vec![slot], values: vec![element] });
        body.push(GoStatement::Range {
            index: Some("index".into()),
            element: "element".into(),
            iterable: array,
            body: each,
        });
        body.push(GoStatement::Return(Some(identifier_expression("converted"))));
        Ok(())
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
            let type_ = self.layout_type(&to_layout)?;
            let origin = field(value.clone(), "Origin");
            body.push(GoStatement::IfAssert {
                name: "original".into(),
                value: origin,
                type_,
                then: vec![GoStatement::Return(Some(identifier_expression("original")))],
            });
        }
        let origin = to_remembers.then(|| value.clone());
        let mut arms = vec![];
        for (constructor, (from_constructor, to_constructor)) in
            from_layout.constructors.iter().zip(to_layout.constructors.iter()).enumerate()
        {
            let mut statements = vec![];
            let mut values = vec![];
            for (position, ((_, from_monotype), (_, to_monotype))) in
                from_constructor.fields.iter().zip(to_constructor.fields.iter()).enumerate()
            {
                let field_value =
                    self.constructor_field(&from_layout, constructor, position, value.clone());
                values.push(self.coerce(
                    field_value,
                    *from_monotype,
                    *to_monotype,
                    &mut statements,
                )?);
            }
            let constructed = match &origin {
                Some(origin) => {
                    let mut composite = self.composite(&to_layout, constructor, values);
                    if let GoExpression::Composite { fields, .. } = &mut composite {
                        fields.push((Some("Origin".into()), origin.clone()));
                    }
                    if to_layout.boxed {
                        GoExpression::Address(Box::new(composite))
                    } else {
                        composite
                    }
                }
                None => self.construct(to, constructor, values)?,
            };
            statements.push(GoStatement::Return(Some(constructed)));
            let test = self.constructor_test(&from_layout, constructor, value.clone());
            arms.push((test, statements));
        }
        let round_trip = (from_remembers || to_remembers).then(|| RoundTrip {
            converter: 0,
            from: from_layout.name.clone(),
            to: to_layout.name.clone(),
            checks: from_remembers,
            remembers: to_remembers.then_some(to_layout.declaration).flatten(),
        });
        let switches_on_tag = from_layout.kind == DataKind::Tagged
            && from_layout.maybe.as_ref().is_none_or(|maybe| maybe.is_struct());
        if !switches_on_tag {
            let last = arms.len() - 1;
            for (position, (test, mut statements)) in arms.into_iter().enumerate() {
                match test {
                    Some(condition) if position < last => {
                        body.push(GoStatement::If {
                            condition,
                            then: statements,
                            otherwise: vec![],
                        });
                    }
                    _ => body.append(&mut statements),
                }
            }
            return Ok(round_trip);
        }
        let mut cases: Vec<GoCase> = arms
            .into_iter()
            .zip(&from_layout.constructors)
            .map(|((_, statements), from_constructor)| GoCase {
                values: vec![identifier_expression(&from_constructor.tag)],
                body: statements,
                line: None,
            })
            .collect();
        let default = GoDefault::covering(&mut cases);
        body.push(GoStatement::Switch {
            value: Some(field(value, "Tag")),
            cases,
            default: Some(default),
        });
        Ok(round_trip)
    }

    fn variant_to_representation(
        &mut self,
        from: &DataType,
        representation: MonotypeId,
        value: GoExpression,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let layout = self.data_layout(from)?;
        let constructors = self
            .monotypes
            .constructors(&mut self.context, from)
            .map_err(Failure::in_code_generation)?;
        let payload = self.record_field_monotype(representation, "value");
        let last = constructors.len().saturating_sub(1);
        for (index, constructor) in constructors.iter().enumerate() {
            let mut statements = vec![];
            let read = self.constructor_field(&layout, index, 0, value.clone());
            let boxed = self.coerce(read, constructor.fields[0], payload, &mut statements)?;
            let label = GoExpression::String(constructor.name.to_string());
            let fields =
                vec![(SmolStr::new_static("type"), label), (SmolStr::new_static("value"), boxed)];
            let built = self.record_value(representation, fields)?;
            statements.push(GoStatement::Return(Some(built)));
            match self.constructor_test(&layout, index, value.clone()) {
                Some(condition) if index < last => {
                    body.push(GoStatement::If { condition, then: statements, otherwise: vec![] });
                }
                _ => body.append(&mut statements),
            }
        }
        if constructors.is_empty() {
            body.push(super::panic_statement(NO_SUCH_LABEL));
        }
        Ok(())
    }

    fn representation_to_variant(
        &mut self,
        representation: MonotypeId,
        to: &DataType,
        value: GoExpression,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let constructors = self
            .monotypes
            .constructors(&mut self.context, to)
            .map_err(Failure::in_code_generation)?;
        let payload = self.record_field_monotype(representation, "value");
        let mut cases = vec![];
        for (index, constructor) in constructors.iter().enumerate() {
            let mut statements = vec![];
            let read = self.read_field(value.clone(), representation, "value");
            let unboxed = self.coerce(read, payload, constructor.fields[0], &mut statements)?;
            let built = self.construct(to, index, vec![unboxed])?;
            statements.push(GoStatement::Return(Some(built)));
            let label = GoExpression::String(constructor.name.to_string());
            cases.push(GoCase { values: vec![label], body: statements, line: None });
        }
        if cases.is_empty() {
            body.push(super::panic_statement(NO_SUCH_LABEL));
            return Ok(());
        }
        let panics = vec![super::panic_statement(NO_SUCH_LABEL)];
        let default = GoDefault { covers: vec![], body: panics, line: None };
        let tag = self.read_field(value, representation, "type");
        body.push(GoStatement::Switch { value: Some(tag), cases, default: Some(default) });
        Ok(())
    }

    fn convert_variant(
        &mut self,
        from: &DataType,
        to: &DataType,
        value: GoExpression,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let layout = self.data_layout(from)?;
        let from_constructors = self
            .monotypes
            .constructors(&mut self.context, from)
            .map_err(Failure::in_code_generation)?;
        let to_constructors = self
            .monotypes
            .constructors(&mut self.context, to)
            .map_err(Failure::in_code_generation)?;
        let mut arms = vec![];
        for (index, constructor) in from_constructors.iter().enumerate() {
            let Some(target) =
                to_constructors.iter().position(|candidate| candidate.name == constructor.name)
            else {
                continue;
            };
            let mut statements = vec![];
            let read = self.constructor_field(&layout, index, 0, value.clone());
            let field = self.coerce(
                read,
                constructor.fields[0],
                to_constructors[target].fields[0],
                &mut statements,
            )?;
            let built = self.construct(to, target, vec![field])?;
            statements.push(GoStatement::Return(Some(built)));
            arms.push((self.constructor_test(&layout, index, value.clone()), statements));
        }
        let covers_every_label = !arms.is_empty() && arms.len() == from_constructors.len();
        let last = arms.len().saturating_sub(1);
        for (position, (test, mut statements)) in arms.into_iter().enumerate() {
            match test {
                Some(condition) if position < last || !covers_every_label => {
                    body.push(GoStatement::If { condition, then: statements, otherwise: vec![] });
                }
                _ => body.append(&mut statements),
            }
        }
        if !covers_every_label {
            body.push(super::panic_statement(NO_SUCH_LABEL));
        }
        Ok(())
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
                fields.retain(|field| field.name != "Origin");
            }
        }
    }
}

const NO_SUCH_LABEL: &str = "Data.Variant: a label the target row lacks";

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

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// A coercion the program wrote. One Go cannot make is reported at the `unsafeCoerce` that
    /// asked for it, with both types.
    pub(super) fn coerce_at(
        &mut self,
        value: GoExpression,
        from: MonotypeId,
        to: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        match self.coerce(value, from, to, out) {
            Err(GoError::Unsupported {
                state: crate::error::UnsupportedState::Construct { construct },
                ..
            }) if construct == UNRELATED_TYPES => Err(self.representation_change(from, to)?),
            result => result,
        }
    }

    fn representation_change(&mut self, from: MonotypeId, to: MonotypeId) -> GoResult<GoError> {
        let site = self.monotypes.coercion_sites.get(&(from, to)).cloned();
        let location = match &site {
            Some(site) => self.location(site.file_id, site.offset)?,
            None => String::new(),
        };
        let definition = match site {
            Some(site) => site.definition,
            None => self.current_definition(),
        };
        Ok(GoError::RepresentationChange(Box::new(RepresentationChange {
            location,
            definition,
            from: self.purescript_type(from)?,
            from_go: self.go_type(from)?.render(),
            to: self.purescript_type(to)?,
            to_go: self.go_type(to)?.render(),
        })))
    }
}
