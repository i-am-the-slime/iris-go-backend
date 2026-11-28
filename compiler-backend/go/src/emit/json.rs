//! Yoga.JSON's readJSON (and so readJSON_) and writeJSON at a type whose codec the specializer found to
//! be Yoga.JSON's own instances throughout (`specialize::json`).
//!
//! Each type gets a decoder that reads the text straight into the program's Go value with
//! go-support's `foreignvalue.Decoder`, and an encoder that writes the value straight out
//! with its `foreignvalue.Encoder`, as JSON.stringify writes what Yoga.JSON's `writeImpl`
//! builds: a record's members in the order Yoga.JSON's builder inserts them (its labels
//! backwards), a Nothing member left out and a Nothing element written as null.
//!
//! A decoder is only a fast path. Text that it does not take, whatever the reason, is read
//! again by Yoga.JSON's own definition, which reports Yoga.JSON's errors in Yoga.JSON's
//! order: a decoder never has to build an error.

use smol_str::SmolStr;

use super::maybe::constructor_field;
use super::names::{NamePart, PendingSpelling};
use super::{Emitter, Mode, Sink, binary, builtin_call, call, identifier_expression};
use crate::error::GoResult;
use crate::foreign::JsonCodec;
use crate::monomorphic::{Expression, Local, LocalId, Pattern, PatternKind};
use crate::monotype::{Monotype, MonotypeId};
use crate::naming::{capitalise, identifier, lower_camel};
use crate::syntax::{
    GoBinaryOperator, GoBuiltin, GoCase, GoDeclaration, GoDefault, GoExpression, GoPackage,
    GoStatement, GoType, GoUnaryOperator,
};

/// The decoder's or the encoder's parameter.
const DECODER: &str = "d";
const ENCODER: &str = "e";
const VALUE: &str = "value";

/// The names a decoder's or an encoder's body may not give its locals: its parameters and
/// the packages it calls.
const RESERVED: &[&str] =
    &[DECODER, ENCODER, VALUE, "foreignvalue", "nullable", "object", "slices"];

impl<'p, Q> Emitter<'p, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn json(
        &mut self,
        codec: JsonCodec,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        self.import(GoPackage::ForeignValue);
        match codec {
            JsonCodec::Read => {
                let name = self.temporary("read");
                let sink = Sink::Define(name.clone());
                self.json_read(&arguments[0], &arguments[1], monotype, sink, out)?;
                Ok(identifier_expression(&name))
            }
            JsonCodec::Write => {
                let value = self.value(&arguments[0], out)?;
                let encoder = self.json_encoder(arguments[0].monotype)?;
                let encode = foreign_value("Encode");
                Ok(call(encode, vec![identifier_expression(&encoder), value]))
            }
        }
    }

    /// `decoded, ok := foreignvalue.Decode(text, DecodeJSON…)`, the decoded value as the
    /// result's success when it is ok, and else Yoga.JSON's own `slow` reading of the text,
    /// both delivered to the sink. A reader's body returns the decoded value early, so that
    /// the slow path reads as what follows when the text does not decode.
    pub(super) fn json_read(
        &mut self,
        slow: &Expression,
        text: &Expression,
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        self.import(GoPackage::ForeignValue);
        let text = self.value(text, out)?;
        let text = self.hoist(text, "text", out);
        let success = match self.monotypes.get(result).clone() {
            Monotype::Data(data) if self.maybe_payload(&data)?.is_some() => "Just",
            _ => "Right",
        };
        let decoded_monotype = self.constructor_field_monotype(result, success, 0)?;
        let decoder = self.json_decoder(decoded_monotype)?;
        let decoded = self.temporary("decoded");
        let ok = self.temporary("ok");
        out.push(GoStatement::Define {
            names: vec![decoded.clone(), ok.clone()],
            values: vec![call(
                foreign_value("Decode"),
                vec![text, identifier_expression(&decoder)],
            )],
        });
        let (data, constructor) = self.constructor_named(result, success)?;
        let decoded_value = identifier_expression(&decoded);
        let succeeded = self.construct(&data, constructor, vec![decoded_value])?;
        let sink = match sink {
            Sink::Define(name) => {
                let type_ = self.go_type(result)?;
                out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
                Sink::Assign(name)
            }
            sink => sink,
        };
        let mut then = vec![];
        self.deliver(succeeded, result, sink.clone(), &mut then)?;
        let mut otherwise = vec![];
        self.sink(slow, Mode::Value, sink.clone(), &mut otherwise)?;
        let condition = identifier_expression(&ok);
        if matches!(sink, Sink::Return) {
            out.push(GoStatement::If { condition, then, otherwise: vec![] });
            out.extend(otherwise);
        } else {
            out.push(GoStatement::If { condition, then, otherwise });
        }
        Ok(())
    }

    /// `show` of the errors a Yoga.JSON read fails with: a call of
    /// `func ShowNonEmptyListForeignError(errors) string`, declared on first use, which shows
    /// each error by Foreign's `show` and the list around them with `foreignvalue.ShowErrors`.
    pub(super) fn show_foreign_errors(
        &mut self,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let [show, errors] = arguments else {
            unreachable!("invariant violated: showing errors takes a show and the errors")
        };
        let mut computed = vec![];
        let show = self.value(show, &mut computed)?;
        let global = computed.is_empty()
            && matches!(show, GoExpression::Identifier(_) | GoExpression::Qualified { .. });
        if !global {
            out.extend(computed);
            let value = self.value(errors, out)?;
            let shown = self.temporary("shown");
            let cell = self.temporary("cell");
            let names = ShownErrors { shown, cell };
            return self.shown_errors(show, value, errors.monotype, &names, out);
        }
        let name = match self.foreign_error_shows.get(&errors.monotype) {
            Some(name) => name.clone(),
            None => {
                let name = self.json_global("Show", errors.monotype)?;
                self.foreign_error_shows.insert(errors.monotype, name.clone());
                let names = ShownErrors { shown: "shown".into(), cell: "cell".into() };
                let mut body = vec![];
                let parameter = identifier_expression("errors");
                let shown =
                    self.shown_errors(show, parameter, errors.monotype, &names, &mut body)?;
                body.push(GoStatement::Return(Some(shown)));
                let type_ = self.go_type(errors.monotype)?;
                self.type_declarations.push(GoDeclaration::Function {
                    name: name.clone(),
                    parameters: vec![("errors".into(), type_)],
                    result: Some(GoType::String),
                    body,
                });
                name
            }
        };
        let value = self.value(errors, out)?;
        Ok(call(identifier_expression(&name), vec![value]))
    }

    /// `shown := []string{show(first)}`, each error of the rest appended in a walk over its
    /// cells, and the list of them shown.
    fn shown_errors(
        &mut self,
        show: GoExpression,
        errors: GoExpression,
        monotype: MonotypeId,
        names: &ShownErrors,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let unsupported = || {
            crate::error::GoError::unsupported_construct(
                "showing errors that are not a NonEmpty of a List",
            )
        };
        let Monotype::Data(data) = self.monotypes.get(monotype).clone() else {
            return Err(unsupported());
        };
        let constructors = self
            .monotypes
            .constructors(&mut self.context, &data)
            .map_err(|failure| failure.at(&self.current_definition()))?;
        let [non_empty] = &constructors[..] else { return Err(unsupported()) };
        let [first, rest] = non_empty.fields[..] else { return Err(unsupported()) };
        let Monotype::Data(list) = self.monotypes.get(rest).clone() else {
            return Err(unsupported());
        };
        let [first, rest] = self.constructor_bindings(&data, 0, [first, rest], errors)?.1;
        let cells = self
            .monotypes
            .constructors(&mut self.context, &list)
            .map_err(|failure| failure.at(&self.current_definition()))?;
        let Some(cons) = cells.iter().position(|constructor| constructor.name == "Cons") else {
            return Err(unsupported());
        };
        let [head, tail] = cells[cons].fields[..] else { return Err(unsupported()) };
        out.push(GoStatement::Define {
            names: vec![names.shown.clone()],
            values: vec![GoExpression::Composite {
                type_: GoType::Slice(Box::new(GoType::String)),
                fields: vec![(None, call(show.clone(), vec![first]))],
            }],
        });
        out.push(GoStatement::Define { names: vec![names.cell.clone()], values: vec![rest] });
        let cell = identifier_expression(&names.cell);
        let (tests, [head, tail]) = self.constructor_bindings(&list, cons, [head, tail], cell)?;
        let is_cons = super::conjunction(tests).ok_or_else(unsupported)?;
        out.push(GoStatement::Loop(vec![
            GoStatement::If {
                condition: super::conditions::negated(&is_cons),
                then: vec![GoStatement::Break],
                otherwise: vec![],
            },
            append(&names.shown, call(show, vec![head])),
            assign(&names.cell, tail),
        ]));
        self.import(GoPackage::ForeignValue);
        Ok(call(foreign_value("ShowErrors"), vec![identifier_expression(&names.shown)]))
    }

    /// The tests that a value is built by the constructor, and its two fields.
    fn constructor_bindings(
        &mut self,
        data: &crate::monotype::DataType,
        constructor: usize,
        fields: [MonotypeId; 2],
        value: GoExpression,
    ) -> GoResult<(Vec<GoExpression>, [GoExpression; 2])> {
        let patterns = fields.map(|monotype| Pattern {
            kind: PatternKind::Variable(Local { id: LocalId(0), name: "field".into(), monotype }),
            monotype,
        });
        let monotype = self.monotypes.intern(Monotype::Data(data.clone()));
        let kind = PatternKind::Constructor {
            data: data.clone(),
            constructor,
            arguments: patterns.into(),
        };
        let mut tests = vec![];
        let mut bindings = vec![];
        self.pattern_tests(&Pattern { kind, monotype }, value, &mut tests, &mut bindings)?;
        let [(_, first), (_, second)] = <[_; 2]>::try_from(bindings)
            .unwrap_or_else(|_| unreachable!("invariant violated: a pattern of two fields"));
        Ok((tests, [first, second]))
    }

    /// The name of `func ReadJSON…(d *foreignvalue.Decoder) T`, declared on first use.
    fn json_decoder(&mut self, monotype: MonotypeId) -> GoResult<String> {
        if let Some(name) = self.json_decoders.get(&monotype) {
            return Ok(name.clone());
        }
        let name = self.json_global("DecodeJSON", monotype)?;
        self.json_decoders.insert(monotype, name.clone());
        let mut locals = Locals::default();
        let mut body = vec![];
        let value = self.json_decode_body(monotype, &mut locals, &mut body)?;
        body.push(GoStatement::Return(Some(value)));
        let decoder = GoType::Pointer(Box::new(GoType::Named("foreignvalue.Decoder".into())));
        let result = self.go_type(monotype)?;
        self.type_declarations.push(GoDeclaration::Function {
            name: name.clone(),
            parameters: vec![(DECODER.into(), decoder)],
            result: Some(result),
            body,
        });
        Ok(name)
    }

    /// Statements that read one value of the type, and the value.
    fn json_decode_body(
        &mut self,
        monotype: MonotypeId,
        locals: &mut Locals,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        match self.monotypes.get(monotype).clone() {
            Monotype::Record(fields) => {
                let mut names = Vec::with_capacity(fields.len());
                let mut cases = Vec::with_capacity(fields.len());
                let mut seen = vec![];
                for field in fields.iter() {
                    let name = locals.fresh(&lower_camel(&field.label));
                    let mut body = vec![];
                    self.json_decode_into(field.monotype, &name, locals, &mut body)?;
                    match self.json_absent(field.monotype)? {
                        Some(absent) => out.push(GoStatement::Define {
                            names: vec![name.clone()],
                            values: vec![absent],
                        }),
                        None => {
                            let type_ = self.go_type(field.monotype)?;
                            out.push(GoStatement::Variable {
                                name: name.clone(),
                                type_,
                                value: None,
                            });
                            let has = locals
                                .fresh(&format!("has{}", capitalise(&lower_camel(&field.label))));
                            out.push(GoStatement::Define {
                                names: vec![has.clone()],
                                values: vec![GoExpression::Boolean(false)],
                            });
                            body.push(assign(&has, GoExpression::Boolean(true)));
                            seen.push(has);
                        }
                    }
                    cases.push(GoCase {
                        values: vec![GoExpression::String(field.label.to_string())],
                        body,
                        line: None,
                    });
                    names.push((field.label.clone(), identifier_expression(&name)));
                }
                let key = method(DECODER, "Key", vec![]);
                let skip = GoDefault {
                    covers: vec![],
                    body: vec![discard(method(DECODER, "Skip", vec![]))],
                    line: None,
                };
                let switch = GoStatement::Switch { value: Some(key), cases, default: Some(skip) };
                out.push(members(DECODER, "Object", "MoreMembers", vec![switch]));
                let missing = seen
                    .iter()
                    .map(|has| not(identifier_expression(has)))
                    .reduce(|left, right| binary(GoBinaryOperator::LogicalOr, left, right));
                if let Some(missing) = missing {
                    out.push(GoStatement::If {
                        condition: missing,
                        then: vec![discard(method(DECODER, "Fail", vec![]))],
                        otherwise: vec![],
                    });
                }
                self.record_value(monotype, names)
            }
            Monotype::Array(element) => {
                let items = locals.fresh("items");
                let element_type = self.go_type(element)?;
                out.push(GoStatement::Define {
                    names: vec![items.clone()],
                    values: vec![GoExpression::Composite {
                        type_: GoType::Slice(Box::new(element_type)),
                        fields: vec![],
                    }],
                });
                let mut body = vec![];
                let value = self.json_decode(element, locals, &mut body)?;
                body.push(append(&items, value));
                out.push(members(DECODER, "Array", "MoreElements", body));
                let clip = self.qualified(GoPackage::Slices, "Clip");
                Ok(call(clip, vec![identifier_expression(&items)]))
            }
            Monotype::Object(element) => {
                let keys = locals.fresh("keys");
                let values = locals.fresh("values");
                out.push(GoStatement::Variable {
                    name: keys.clone(),
                    type_: GoType::Slice(Box::new(GoType::String)),
                    value: None,
                });
                let element_type = self.go_type(element)?;
                out.push(GoStatement::Variable {
                    name: values.clone(),
                    type_: GoType::Slice(Box::new(element_type)),
                    value: None,
                });
                let mut body = vec![append(&keys, method(DECODER, "Key", vec![]))];
                let value = self.json_decode(element, locals, &mut body)?;
                body.push(append(&values, value));
                out.push(members(DECODER, "Object", "MoreMembers", body));
                self.import(GoPackage::Object);
                let from_entries = GoExpression::qualified(GoPackage::Object, "FromEntries");
                Ok(call(
                    from_entries,
                    vec![identifier_expression(&keys), identifier_expression(&values)],
                ))
            }
            _ => self.json_decode(monotype, locals, out),
        }
    }

    /// One value of the type read in place: a scalar by the decoder's method, an optional
    /// value by its test for null, and anything else by its own decoder.
    fn json_decode(
        &mut self,
        monotype: MonotypeId,
        locals: &mut Locals,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let scalar = |name: &str| Ok(method(DECODER, name, vec![]));
        match self.monotypes.get(monotype).clone() {
            Monotype::Int => scalar("Int"),
            Monotype::Number => scalar("Number"),
            Monotype::String => scalar("String"),
            Monotype::Boolean => scalar("Boolean"),
            Monotype::Nullable(_) => self.json_decode_optional(monotype, locals, out),
            Monotype::Data(data) if self.maybe_payload(&data)?.is_some() => {
                self.json_decode_optional(monotype, locals, out)
            }
            _ => {
                let decoder = self.json_decoder(monotype)?;
                Ok(call(identifier_expression(&decoder), vec![identifier_expression(DECODER)]))
            }
        }
    }

    fn json_decode_optional(
        &mut self,
        monotype: MonotypeId,
        locals: &mut Locals,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let name = locals.fresh("optional");
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        self.json_decode_into(monotype, &name, locals, out)?;
        Ok(identifier_expression(&name))
    }

    /// Reads one value of the type into the local `target`: a Maybe or a Nullable by its test
    /// for null, with no local of its own.
    fn json_decode_into(
        &mut self,
        monotype: MonotypeId,
        target: &str,
        locals: &mut Locals,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let mut otherwise = vec![];
        let (null, value) = match self.monotypes.get(monotype).clone() {
            Monotype::Nullable(payload) => {
                let null = GoExpression::nil();
                let value = self.json_decode(payload, locals, &mut otherwise)?;
                self.import(GoPackage::Nullable);
                let not_null = GoExpression::qualified(GoPackage::Nullable, "NotNull");
                (null, call(not_null, vec![value]))
            }
            Monotype::Data(data) if let Some(payload) = self.maybe_payload(&data)? => {
                let nothing = self.nothing_value(monotype)?;
                let value = self.json_decode(payload, locals, &mut otherwise)?;
                let (data, just) = self.constructor_named(monotype, "Just")?;
                (nothing, self.construct(&data, just, vec![value])?)
            }
            _ => {
                let value = self.json_decode(monotype, locals, out)?;
                out.push(assign(target, value));
                return Ok(());
            }
        };
        otherwise.push(assign(target, value));
        out.push(GoStatement::If {
            condition: method(DECODER, "Null", vec![]),
            then: vec![assign(target, null)],
            otherwise,
        });
        Ok(())
    }

    /// The value of a record field that the text leaves out, for a type that reads undefined:
    /// a Maybe's Nothing. Foreign's `readNull` takes only null, not undefined, for a Nullable.
    fn json_absent(&mut self, monotype: MonotypeId) -> GoResult<Option<GoExpression>> {
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Data(data) if self.maybe_payload(&data)?.is_some() => {
                Some(self.nothing_value(monotype)?)
            }
            _ => None,
        })
    }

    /// The name of `func WriteJSON…(e *foreignvalue.Encoder, value T)`, declared on first use.
    fn json_encoder(&mut self, monotype: MonotypeId) -> GoResult<String> {
        if let Some(name) = self.json_encoders.get(&monotype) {
            return Ok(name.clone());
        }
        let name = self.json_global("EncodeJSON", monotype)?;
        self.json_encoders.insert(monotype, name.clone());
        let mut locals = Locals::default();
        let mut body = vec![];
        self.json_encode_body(monotype, identifier_expression(VALUE), &mut locals, &mut body)?;
        let encoder = GoType::Pointer(Box::new(GoType::Named("foreignvalue.Encoder".into())));
        let value = self.go_type(monotype)?;
        self.type_declarations.push(GoDeclaration::Function {
            name: name.clone(),
            parameters: vec![(ENCODER.into(), encoder), (VALUE.into(), value)],
            result: None,
            body,
        });
        Ok(name)
    }

    fn json_encode_body(
        &mut self,
        monotype: MonotypeId,
        value: GoExpression,
        locals: &mut Locals,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        match self.monotypes.get(monotype).clone() {
            Monotype::Record(fields) => {
                raw(out, "{");
                // Whether a member is written already, as far as the code knows.
                let mut written = Some(false);
                for field in fields.iter().rev() {
                    let key = format!("{}:", json_string(&field.label));
                    let member = self.read_field(value.clone(), monotype, &field.label);
                    let mut body = vec![];
                    let maybe = match self.monotypes.get(field.monotype).clone() {
                        Monotype::Data(data) => self.maybe_payload(&data)?,
                        _ => None,
                    };
                    let (payload, test) = match maybe {
                        Some(payload) => {
                            let (data, just) = self.constructor_named(field.monotype, "Just")?;
                            let layout = self.data_layout(&data)?;
                            let name = locals.fresh(&lower_camel(&field.label));
                            out.push(GoStatement::Define {
                                names: vec![name.clone()],
                                values: vec![member.clone()],
                            });
                            let member = identifier_expression(&name);
                            let test = self
                                .constructor_test(&layout, just, member.clone())
                                .expect("invariant violated: Just is one of two constructors");
                            let inner = constructor_field(&layout, just, 0, member);
                            (payload, Some((inner, test)))
                        }
                        None => (field.monotype, None),
                    };
                    let target = if test.is_some() { &mut body } else { &mut *out };
                    match written {
                        Some(false) => raw(target, &key),
                        Some(true) => raw(target, &format!(",{key}")),
                        None => target.push(discard(method(
                            ENCODER,
                            "Member",
                            vec![GoExpression::String(key.clone())],
                        ))),
                    }
                    match test {
                        Some((inner, test)) => {
                            self.json_encode(payload, inner, locals, &mut body)?;
                            out.push(GoStatement::If {
                                condition: test,
                                then: body,
                                otherwise: vec![],
                            });
                            if written == Some(false) {
                                written = None;
                            }
                        }
                        None => {
                            self.json_encode(payload, member, locals, out)?;
                            written = Some(true);
                        }
                    }
                }
                raw(out, "}");
            }
            Monotype::Array(element) => {
                raw(out, "[");
                let index = locals.fresh("index");
                let item = locals.fresh("item");
                let mut body = vec![GoStatement::If {
                    condition: binary(
                        GoBinaryOperator::GreaterThan,
                        identifier_expression(&index),
                        GoExpression::Integer(0),
                    ),
                    then: vec![raw_statement(",")],
                    otherwise: vec![],
                }];
                self.json_encode(element, identifier_expression(&item), locals, &mut body)?;
                out.push(GoStatement::Range {
                    index: Some(index),
                    element: item,
                    iterable: value,
                    body,
                });
                raw(out, "]");
            }
            Monotype::Object(element) => {
                raw(out, "{");
                let key = locals.fresh("key");
                let member = locals.fresh("member");
                let mut body = vec![];
                let write_key = discard(method(ENCODER, "Key", vec![identifier_expression(&key)]));
                let mut written = vec![write_key];
                let maybe = match self.monotypes.get(element).clone() {
                    Monotype::Data(data) => self.maybe_payload(&data)?,
                    _ => None,
                };
                match maybe {
                    Some(payload) => {
                        let (data, just) = self.constructor_named(element, "Just")?;
                        let layout = self.data_layout(&data)?;
                        let member = identifier_expression(&member);
                        let test = self
                            .constructor_test(&layout, just, member.clone())
                            .expect("invariant violated: Just is one of two constructors");
                        let inner = constructor_field(&layout, just, 0, member);
                        self.json_encode(payload, inner, locals, &mut written)?;
                        body.push(GoStatement::If {
                            condition: test,
                            then: written,
                            otherwise: vec![],
                        });
                    }
                    None => {
                        self.json_encode(
                            element,
                            identifier_expression(&member),
                            locals,
                            &mut written,
                        )?;
                        body.extend(written);
                    }
                }
                self.import(GoPackage::Object);
                let entries = GoExpression::qualified(GoPackage::Object, "Entries");
                out.push(GoStatement::Range {
                    index: Some(key),
                    element: member,
                    iterable: call(entries, vec![value]),
                    body,
                });
                raw(out, "}");
            }
            Monotype::Data(data) if self.monotypes.variant_row(&data).is_some() => {
                self.json_encode_variant(&data, value, locals, out)?
            }
            _ => self.json_encode(monotype, value, locals, out)?,
        }
        Ok(())
    }

    /// A variant as Yoga.JSON writes it, an object of its one label: `{"label":payload}`, by a
    /// switch over its tag.
    fn json_encode_variant(
        &mut self,
        data: &crate::monotype::DataType,
        value: GoExpression,
        locals: &mut Locals,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&self.current_definition()))?;
        let layout = self.data_layout(data)?;
        let mut cases = vec![];
        for (index, constructor) in constructors.iter().enumerate() {
            let [payload] = constructor.fields[..] else {
                return Err(crate::error::GoError::unsupported_construct(
                    "a variant label without one payload",
                ));
            };
            let mut body = vec![];
            raw(&mut body, &format!("{{{}:", json_string(&constructor.name)));
            let field = constructor_field(&layout, index, 0, value.clone());
            self.json_encode(payload, field, locals, &mut body)?;
            raw(&mut body, "}");
            cases.push((index, body));
        }
        if let [(_, body)] = cases.as_mut_slice() {
            out.append(body);
            return Ok(());
        }
        let cases = cases.into_iter().map(|(index, body)| GoCase {
            values: vec![identifier_expression(&layout.constructors[index].tag)],
            body,
            line: None,
        });
        let cases = cases.collect();
        let tag = super::field(value, "Tag");
        out.push(GoStatement::Switch { value: Some(tag), cases, default: None });
        Ok(())
    }

    /// Writes one value in place: a scalar by the encoder's method, an optional value as null
    /// when it is absent, and anything else by its own encoder.
    fn json_encode(
        &mut self,
        monotype: MonotypeId,
        value: GoExpression,
        locals: &mut Locals,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let scalar = match self.monotypes.get(monotype) {
            Monotype::Int => Some("Int"),
            Monotype::Number => Some("Number"),
            Monotype::String => Some("String"),
            Monotype::Boolean => Some("Boolean"),
            _ => None,
        };
        if let Some(name) = scalar {
            out.push(discard(method(ENCODER, name, vec![value])));
            return Ok(());
        }
        match self.monotypes.get(monotype).clone() {
            Monotype::Nullable(payload) => {
                let name = held(value, locals, out);
                let mut present = vec![];
                let dereferenced = GoExpression::Unary {
                    operator: GoUnaryOperator::Dereference,
                    operand: Box::new(identifier_expression(&name)),
                };
                self.json_encode(payload, dereferenced, locals, &mut present)?;
                out.push(GoStatement::If {
                    condition: binary(
                        GoBinaryOperator::Equal,
                        identifier_expression(&name),
                        GoExpression::nil(),
                    ),
                    then: vec![raw_statement("null")],
                    otherwise: present,
                });
            }
            Monotype::Data(data) if let Some(payload) = self.maybe_payload(&data)? => {
                let name = held(value, locals, out);
                let (data, just) = self.constructor_named(monotype, "Just")?;
                let layout = self.data_layout(&data)?;
                let optional = identifier_expression(&name);
                let test = self
                    .constructor_test(&layout, just, optional.clone())
                    .expect("invariant violated: Just is one of two constructors");
                let inner = constructor_field(&layout, just, 0, optional);
                let mut present = vec![];
                self.json_encode(payload, inner, locals, &mut present)?;
                out.push(GoStatement::If {
                    condition: test,
                    then: present,
                    otherwise: vec![raw_statement("null")],
                });
            }
            _ => {
                let encoder = self.json_encoder(monotype)?;
                out.push(discard(call(
                    identifier_expression(&encoder),
                    vec![identifier_expression(ENCODER), value],
                )));
            }
        }
        Ok(())
    }

    /// A global named after the codec and the type it reads or writes, its records by the
    /// names packaging gives them.
    pub(super) fn json_global(&mut self, prefix: &str, monotype: MonotypeId) -> GoResult<String> {
        let mut full = prefix.to_string();
        let mut parts = vec![NamePart::Text(prefix.into())];
        self.json_name_parts(monotype, &mut full, &mut parts)?;
        Ok(self.pending_global(identifier(&full), PendingSpelling::Parts(parts)))
    }

    pub(super) fn json_name_parts(
        &mut self,
        monotype: MonotypeId,
        full: &mut String,
        parts: &mut Vec<NamePart>,
    ) -> GoResult<()> {
        let text = |text: &str, full: &mut String, parts: &mut Vec<NamePart>| {
            full.push_str(text);
            parts.push(NamePart::Text(text.into()));
        };
        match self.monotypes.get(monotype).clone() {
            Monotype::Int => text("Int", full, parts),
            Monotype::Number => text("Number", full, parts),
            Monotype::String => text("String", full, parts),
            Monotype::Boolean => text("Boolean", full, parts),
            Monotype::Array(element) => {
                text("Array", full, parts);
                self.json_name_parts(element, full, parts)?;
            }
            Monotype::Object(element) => {
                text("Object", full, parts);
                self.json_name_parts(element, full, parts)?;
            }
            Monotype::Nullable(element) => {
                text("Nullable", full, parts);
                self.json_name_parts(element, full, parts)?;
            }
            Monotype::Data(data) if let Some(payload) = self.maybe_payload(&data)? => {
                text("Maybe", full, parts);
                self.json_name_parts(payload, full, parts)?;
            }
            Monotype::Record(fields) => {
                let labels = fields.iter().map(|field| capitalise(&lower_camel(&field.label)));
                let labels: String = labels.collect();
                full.push_str(&labels);
                parts.push(NamePart::Record { monotype, labels });
            }
            Monotype::Char => text("Char", full, parts),
            Monotype::Unit => text("Unit", full, parts),
            Monotype::Int64 => text("Int64", full, parts),
            Monotype::UInt64 => text("UInt64", full, parts),
            Monotype::BigInt => text("BigInt", full, parts),
            Monotype::Data(data) => {
                let layout = self.data_layout(&data)?;
                text(&capitalise(&layout.name), full, parts);
            }
            _ => text("Value", full, parts),
        }
        Ok(())
    }
}

/// The locals that showing errors writes: the errors shown so far and the cell of the rest.
struct ShownErrors {
    shown: String,
    cell: String,
}

/// The locals of one decoder or encoder.
#[derive(Default)]
struct Locals {
    taken: rustc_hash::FxHashSet<String>,
}

impl Locals {
    fn fresh(&mut self, base: &str) -> String {
        let base = match identifier(base) {
            base if base.is_empty() => "field".to_string(),
            base => base,
        };
        let mut name = base.clone();
        let mut number = 1;
        while RESERVED.contains(&name.as_str()) || !self.taken.insert(name.clone()) {
            number += 1;
            name = format!("{base}{number}");
        }
        name
    }
}

fn foreign_value(name: &str) -> GoExpression {
    GoExpression::qualified(GoPackage::ForeignValue, name)
}

fn method(receiver: &str, name: &str, arguments: Vec<GoExpression>) -> GoExpression {
    call(super::field(identifier_expression(receiver), name), arguments)
}

fn discard(expression: GoExpression) -> GoStatement {
    GoStatement::Expression(expression)
}

fn assign(name: &str, value: GoExpression) -> GoStatement {
    GoStatement::Assign { targets: vec![identifier_expression(name)], values: vec![value] }
}

fn append(name: &str, value: GoExpression) -> GoStatement {
    let appended = builtin_call(GoBuiltin::Append, vec![identifier_expression(name), value]);
    assign(name, appended)
}

/// `if d.open() { for { body; if !d.more() { break } } }`: the members of an object or the
/// elements of an array.
fn members(decoder: &str, open: &str, more: &str, mut body: Vec<GoStatement>) -> GoStatement {
    body.push(GoStatement::If {
        condition: not(method(decoder, more, vec![])),
        then: vec![GoStatement::Break],
        otherwise: vec![],
    });
    GoStatement::If {
        condition: method(decoder, open, vec![]),
        then: vec![GoStatement::Loop(body)],
        otherwise: vec![],
    }
}

fn raw_statement(text: &str) -> GoStatement {
    discard(method(ENCODER, "Raw", vec![GoExpression::String(text.into())]))
}

/// Writes text that is already JSON, joined to the text the statement before writes.
fn raw(out: &mut Vec<GoStatement>, text: &str) {
    let last = out.last_mut();
    if let Some(GoStatement::Expression(GoExpression::Call { function, arguments })) = last
        && let GoExpression::Field { value, name } = function.as_ref()
        && name == "Raw"
        && matches!(value.as_ref(), GoExpression::Identifier(receiver) if receiver == ENCODER)
        && let [GoExpression::String(written)] = arguments.as_mut_slice()
    {
        written.push_str(text);
        return;
    }
    out.push(raw_statement(text));
}

/// A label quoted as JSON.stringify quotes it.
fn json_string(text: &SmolStr) -> String {
    let mut quoted = String::with_capacity(text.len() + 2);
    quoted.push('"');
    for character in text.chars() {
        match character {
            '"' => quoted.push_str("\\\""),
            '\\' => quoted.push_str("\\\\"),
            '\u{8}' => quoted.push_str("\\b"),
            '\u{c}' => quoted.push_str("\\f"),
            '\n' => quoted.push_str("\\n"),
            '\r' => quoted.push_str("\\r"),
            '\t' => quoted.push_str("\\t"),
            character if (character as u32) < 0x20 => {
                quoted.push_str(&format!("\\u{:04x}", character as u32))
            }
            character => quoted.push(character),
        }
    }
    quoted.push('"');
    quoted
}

fn not(operand: GoExpression) -> GoExpression {
    GoExpression::Unary { operator: GoUnaryOperator::Not, operand: Box::new(operand) }
}

/// The name of a local holding the value, defined unless the value is a local already.
fn held(value: GoExpression, locals: &mut Locals, out: &mut Vec<GoStatement>) -> String {
    if let GoExpression::Identifier(name) = value {
        return name;
    }
    let name = locals.fresh("optional");
    out.push(GoStatement::Define { names: vec![name.clone()], values: vec![value] });
    name
}
