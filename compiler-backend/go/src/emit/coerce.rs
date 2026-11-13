use super::{
    DataKind, Emitter, binary, call, field, identifier, identifier_expression, is_simple,
    is_untyped_constant, panic_statement, unique, unit_value,
};
use crate::error::{GoError, GoResult};
use crate::foreign::{GoFunction, GoPackage};
use crate::monotype::{DataType, Monotype, MonotypeId, RecordField};
use crate::syntax::{GoCase, GoDeclaration, GoExpression, GoStatement, GoType};

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
        if from == to || self.go_type(from)? == self.go_type(to)? {
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
                let record = self.shared(value, out);
                let mut entries = Vec::with_capacity(fields.len());
                for record_field in fields.iter() {
                    let field_value = field(record.clone(), &identifier(&record_field.label));
                    entries.push((
                        record_field.label.to_string(),
                        field_value,
                        record_field.monotype,
                    ));
                }
                self.foreign_record(entries, out)
            }
            (Monotype::Opaque, Monotype::Record(fields)) => {
                let record = self.shared(value, out);
                let read = self
                    .go_function(GoFunction { package: GoPackage::Direct, name: "ForeignField" });
                let mut values = Vec::with_capacity(fields.len());
                for record_field in fields.iter() {
                    let label = GoExpression::String(record_field.label.to_string());
                    let field_value = call(read.clone(), vec![record.clone(), label]);
                    let field_value = self.coerce(field_value, from, record_field.monotype, out)?;
                    values.push((Some(identifier(&record_field.label)), field_value));
                }
                let type_ = GoType::Named(self.record_name(to)?);
                Ok(GoExpression::Composite { type_, fields: values })
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
            (_, Monotype::Erased | Monotype::Opaque) => {
                let canonical = self.canonical(from);
                let value = self.coerce(value, from, canonical, out)?;
                if is_untyped_constant(&value) {
                    let type_ = self.go_type(canonical)?;
                    return Ok(GoExpression::Conversion { type_, value: Box::new(value) });
                }
                Ok(value)
            }
            (Monotype::Erased | Monotype::Opaque, _) => {
                let canonical = self.canonical(to);
                let type_ = self.go_type(canonical)?;
                let value = GoExpression::TypeAssertion { value: Box::new(value), type_ };
                self.coerce(value, canonical, to, out)
            }
            (
                Monotype::Function(from_argument, from_result),
                Monotype::Function(to_argument, to_result),
            ) => {
                let function = self.shared(value, out);
                let parameter = self.temporary("coerced");
                let parameter_type = self.go_type(to_argument)?;
                let mut body = vec![];
                let argument = self.coerce(
                    identifier_expression(&parameter),
                    to_argument,
                    from_argument,
                    &mut body,
                )?;
                let invoked = call(function, vec![argument]);
                self.coerce_invocation(invoked, from_result, to_result, &mut body)?;
                let result = self.invocation_type(to_result)?;
                Ok(GoExpression::Function {
                    parameters: vec![(parameter, parameter_type)],
                    result,
                    body,
                })
            }
            (Monotype::Effect(from_result), Monotype::Effect(to_result)) => {
                let action = self.shared(value, out);
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
            _ => Err(GoError::Unsupported {
                definition: "code generation".into(),
                state: crate::error::UnsupportedState::Construct {
                    construct: "representation changes between unrelated types",
                },
            }),
        }
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
        let erased = self.monotypes.intern(Monotype::Erased);
        let canonical = match self.monotypes.get(monotype).clone() {
            Monotype::Function(..) => Monotype::Function(erased, erased),
            Monotype::Effect(_) => Monotype::Effect(erased),
            Monotype::Array(_) => Monotype::Array(erased),
            Monotype::MutableArray(_) => Monotype::MutableArray(erased),
            Monotype::Object(_) => Monotype::Object(erased),
            Monotype::Nullable(_) => Monotype::Nullable(erased),
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
            | Monotype::Erased => return monotype,
        };
        self.monotypes.intern(canonical)
    }

    fn erase_arguments(&self, data: &DataType) -> DataType {
        let erased = self.context.types.erased();
        let arguments = data.arguments.iter().map(|_| erased).collect();
        DataType { file_id: data.file_id, item: data.item, arguments }
    }

    fn shared(&mut self, value: GoExpression, out: &mut Vec<GoStatement>) -> GoExpression {
        if is_simple(&value) {
            return value;
        }
        let name = self.temporary("original");
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
        let name = unique("convert".to_string(), &mut self.global_names);
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
                let mut fields = vec![];
                for (from_field, to_field) in from_fields.iter().zip(to_fields.iter()) {
                    let label = identifier(&to_field.label);
                    let field_value = field(value.clone(), &label);
                    let converted = self.coerce(
                        field_value,
                        from_field.monotype,
                        to_field.monotype,
                        &mut body,
                    )?;
                    fields.push((Some(label), converted));
                }
                body.push(GoStatement::Return(Some(GoExpression::Composite {
                    type_: result_type.clone(),
                    fields,
                })));
            }
            (Monotype::Data(from_data), Monotype::Data(to_data)) => {
                self.convert_data(&from_data, &to_data, value, &mut body)?;
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
    ) -> GoResult<()> {
        let from_layout = self.data_layout(from)?;
        let to_layout = self.data_layout(to)?;
        if from_layout.kind == DataKind::Enumeration {
            let type_ = GoType::Named(to_layout.name);
            body.push(GoStatement::Return(Some(GoExpression::Conversion {
                type_,
                value: Box::new(value),
            })));
            return Ok(());
        }
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
            let constructed = self.construct(to, constructor, values)?;
            statements.push(GoStatement::Return(Some(constructed)));
            cases.push(GoCase {
                values: vec![identifier_expression(&from_constructor.tag)],
                body: statements,
            });
        }
        if from_layout.kind == DataKind::Product {
            let [case] = &mut cases[..] else {
                unreachable!("invariant violated: product data has one constructor")
            };
            body.append(&mut case.body);
            return Ok(());
        }
        body.push(GoStatement::Switch { value: Some(field(value, "Tag")), cases, default: None });
        body.push(panic_statement("Failed pattern match"));
        Ok(())
    }
}
