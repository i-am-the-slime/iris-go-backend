use std::sync::Arc;

use checking::TypeId;
use checking::core::{RowField, RowType, Type};
use files::FileId;
use indexing::TermItemId;
use smol_str::SmolStr;

use super::{Scope, Specializer};
use crate::dictionary::Dictionary;
use crate::error::GoResult;
use crate::monomorphic::{
    Alternative, Expression, ExpressionKind, Guarded, Literal, Local, Pattern, PatternKind,
};
use crate::monotype::{DataType, Monotype, MonotypeId};
use crate::primitives::Primitive;
use crate::scheme::ConstrainedScheme;
use crate::types::Substitution;

const IMPOSSIBLE: &str = "Data.Variant: pattern match failure";
const PENDING: &str = "continuation instantiation discovered in this pass";
const UNHANDLED: &str = "Data.Variant: a label without a handler";

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn variant_primitive(
        &mut self,
        scope: &Scope,
        primitive: Primitive,
        types: &[TypeId],
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        match primitive {
            Primitive::Inject => self.inject(scope, types, monotype),
            Primitive::On => self.on(scope, types, monotype),
            Primitive::Default => Ok(self.default_case(monotype)),
            Primitive::Case => Ok(self.impossible_case(monotype)),
            Primitive::Expand => self.expand(scope, monotype),
            Primitive::Match => self.match_record(scope, monotype),
            Primitive::OnMatch => self.on_match(scope, monotype),
            Primitive::MakeExists
            | Primitive::RunExists
            | Primitive::Unvariant
            | Primitive::ReifyType
            | Primitive::Provide
            | Primitive::Defer
            | Primitive::DeferApply
            | Primitive::DeferLazy
            | Primitive::DeferLazyApply
            | Primitive::ToSigned
            | Primitive::ToUnsigned
            | Primitive::ReadJson
            | Primitive::WriteJson
            | Primitive::GenericShow => Ok(None),
        }
    }

    fn inject(
        &mut self,
        scope: &Scope,
        types: &[TypeId],
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        let Some(([proxy, payload], result)) = self.arrows::<2>(monotype) else { return Ok(None) };
        let Some(data) = self.variant_data(result) else { return Ok(None) };
        let Some(label) = types.iter().find_map(|&symbol| self.symbol(symbol)) else {
            return Ok(None);
        };
        let Some(index) = self.label_index(scope, &data, &label)? else { return Ok(None) };
        let proxy = self.fresh_local(SmolStr::new_static("proxy"), proxy);
        let value = self.fresh_local(self.monotypes.value_name(payload), payload);
        let constructed = self.inject_at(scope, &data, index, value.expression(), result)?;
        Ok(Some(self.lambda(vec![proxy, value], constructed)))
    }

    fn on(
        &mut self,
        scope: &Scope,
        types: &[TypeId],
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        let Some(([proxy, handler, fallback, variant], result)) = self.arrows::<4>(monotype) else {
            return Ok(None);
        };
        let Some(data) = self.variant_data(variant) else { return Ok(None) };
        let Some((remaining, _)) = self.monotypes.function_parts(fallback) else { return Ok(None) };
        let Some(remaining_data) = self.variant_data(remaining) else { return Ok(None) };
        let Some(label) = types.iter().find_map(|&symbol| self.symbol(symbol)) else {
            return Ok(None);
        };
        let proxy = self.fresh_local(SmolStr::new_static("proxy"), proxy);
        let handler = self.fresh_local(SmolStr::new_static("handler"), handler);
        let fallback = self.fresh_local(SmolStr::new_static("fallback"), fallback);
        let value = self.fresh_local(self.monotypes.value_name(variant), variant);
        let alternatives = self.alternatives(scope, &data, variant, |this, name, hidden| {
            if name == label {
                return this.apply_handler(handler.expression(), hidden, result);
            }
            let reinjected = this.reinject(scope, &remaining_data, remaining, name, hidden)?;
            let kind = ExpressionKind::Apply {
                function: Box::new(fallback.expression()),
                arguments: vec![reinjected],
            };
            Ok(Expression::new(kind, result))
        })?;
        let body = case_expression(value.expression(), alternatives, result);
        Ok(Some(self.lambda(vec![proxy, handler, fallback, value], body)))
    }

    fn default_case(&mut self, monotype: MonotypeId) -> Option<Expression> {
        let ([answer, variant], _) = self.arrows::<2>(monotype)?;
        let answer = self.fresh_local(self.monotypes.value_name(answer), answer);
        let value = self.fresh_local(self.monotypes.value_name(variant), variant);
        let body = answer.expression();
        Some(self.lambda(vec![answer, value], body))
    }

    fn impossible_case(&mut self, monotype: MonotypeId) -> Option<Expression> {
        let ([variant], result) = self.arrows::<1>(monotype)?;
        let value = self.fresh_local(self.monotypes.value_name(variant), variant);
        let body = Expression::new(ExpressionKind::Fail(SmolStr::new_static(IMPOSSIBLE)), result);
        Some(self.lambda(vec![value], body))
    }

    fn expand(&mut self, scope: &Scope, monotype: MonotypeId) -> GoResult<Option<Expression>> {
        let Some(([variant], result)) = self.arrows::<1>(monotype) else { return Ok(None) };
        let Some(data) = self.variant_data(variant) else { return Ok(None) };
        let Some(wider) = self.variant_data(result) else { return Ok(None) };
        let value = self.fresh_local(self.monotypes.value_name(variant), variant);
        let alternatives = self.alternatives(scope, &data, variant, |this, name, hidden| {
            this.reinject(scope, &wider, result, name, hidden)
        })?;
        let body = case_expression(value.expression(), alternatives, result);
        Ok(Some(self.lambda(vec![value], body)))
    }

    fn match_record(
        &mut self,
        scope: &Scope,
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        let Some(([handlers, variant], result)) = self.arrows::<2>(monotype) else {
            return Ok(None);
        };
        let Some(data) = self.variant_data(variant) else { return Ok(None) };
        let Monotype::Record(_) = self.monotypes.get(handlers) else { return Ok(None) };
        let handlers = self.fresh_local(SmolStr::new_static("handlers"), handlers);
        let value = self.fresh_local(self.monotypes.value_name(variant), variant);
        let alternatives = self.alternatives(scope, &data, variant, |this, name, hidden| {
            let Some(handler) = this.handler(&handlers, &name) else {
                let failure = ExpressionKind::Fail(SmolStr::new_static(UNHANDLED));
                return Ok(Expression::new(failure, result));
            };
            this.apply_handler(handler, hidden, result)
        })?;
        let body = case_expression(value.expression(), alternatives, result);
        Ok(Some(self.lambda(vec![handlers, value], body)))
    }

    fn on_match(&mut self, scope: &Scope, monotype: MonotypeId) -> GoResult<Option<Expression>> {
        let Some(([handlers, fallback, variant], result)) = self.arrows::<3>(monotype) else {
            return Ok(None);
        };
        let Some(data) = self.variant_data(variant) else { return Ok(None) };
        let Monotype::Record(_) = self.monotypes.get(handlers) else { return Ok(None) };
        let Some((remaining, _)) = self.monotypes.function_parts(fallback) else { return Ok(None) };
        let Some(remaining_data) = self.variant_data(remaining) else { return Ok(None) };
        let handlers = self.fresh_local(SmolStr::new_static("handlers"), handlers);
        let fallback = self.fresh_local(SmolStr::new_static("fallback"), fallback);
        let value = self.fresh_local(self.monotypes.value_name(variant), variant);
        let alternatives = self.alternatives(scope, &data, variant, |this, name, hidden| {
            if let Some(handler) = this.handler(&handlers, &name) {
                return this.apply_handler(handler, hidden, result);
            }
            let reinjected = this.reinject(scope, &remaining_data, remaining, name, hidden)?;
            let kind = ExpressionKind::Apply {
                function: Box::new(fallback.expression()),
                arguments: vec![reinjected],
            };
            Ok(Expression::new(kind, result))
        })?;
        let body = case_expression(value.expression(), alternatives, result);
        Ok(Some(self.lambda(vec![handlers, fallback, value], body)))
    }

    /// `unvariant v` as one branch per label of the Variant, each the Unvariant
    /// that runs the continuation's instantiation at that label on the payload.
    pub(super) fn unvariant(
        &mut self,
        scope: &Scope,
        declaration: (FileId, TermItemId),
        instantiations: &Substitution,
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        let Some(([variant], unvariant)) = self.arrows::<1>(monotype) else { return Ok(None) };
        let Some(continuation) = self.unvariant_continuation(declaration, instantiations)? else {
            return Ok(None);
        };
        let Some(data) = self.variant_data(variant) else {
            let Some(labels) = self.unvariant_row_labels(declaration, instantiations)? else {
                return Ok(None);
            };
            return self.unvariant_representation(scope, &continuation, &labels, monotype);
        };
        let labels = self.constructor_labels(scope, &data)?;
        let Some(continuations) = self.label_continuations(scope, &continuation, &labels)? else {
            return Ok(Some(self.pending_unvariant(monotype)));
        };
        let value = self.fresh_local(self.monotypes.value_name(variant), variant);
        let alternatives = self.alternatives(scope, &data, variant, |this, name, hidden| {
            let label = continuations.iter().find(|(label, _)| *label == name);
            match label {
                Some((_, field)) => Ok(this.run_continuation(unvariant, field, &hidden)),
                None => Ok(Expression::new(
                    ExpressionKind::Fail(SmolStr::new_static(IMPOSSIBLE)),
                    unvariant,
                )),
            }
        })?;
        let body = case_expression(value.expression(), alternatives, unvariant);
        Ok(Some(self.lambda(vec![value], body)))
    }

    /// `unvariant v` of a Variant whose row was erased, as a narrowed one is: its `VariantRep`
    /// still holds the label, so each label of the row the specialization knows is a branch on it.
    fn unvariant_representation(
        &mut self,
        scope: &Scope,
        continuation: &ConstrainedScheme,
        labels: &[SmolStr],
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        let Some(([variant], unvariant)) = self.arrows::<1>(monotype) else { return Ok(None) };
        let Monotype::Record(fields) = self.monotypes.get(variant).clone() else { return Ok(None) };
        let field = |label: &str| fields.iter().find(|field| field.label == label).cloned();
        let (Some(tag), Some(payload)) = (field("type"), field("value")) else { return Ok(None) };
        let Some(continuations) = self.label_continuations(scope, continuation, labels)? else {
            return Ok(Some(self.pending_unvariant(monotype)));
        };
        let value = self.fresh_local(self.monotypes.value_name(variant), variant);
        let mut alternatives = Vec::with_capacity(continuations.len() + 1);
        for (label, field) in &continuations {
            let hidden_name = self.monotypes.value_name(payload.monotype);
            let hidden = self.fresh_local(hidden_name, payload.monotype);
            let body = self.run_continuation(unvariant, field, &hidden);
            let tag = Pattern {
                kind: PatternKind::Literal(Literal::String(label.to_string())),
                monotype: tag.monotype,
            };
            let variable = PatternKind::Variable(hidden);
            let payload = Pattern { kind: variable, monotype: payload.monotype };
            let kind = PatternKind::Record(vec![
                (SmolStr::new_static("type"), tag),
                (SmolStr::new_static("value"), payload),
            ]);
            alternatives.push(Alternative {
                patterns: vec![Pattern { kind, monotype: variant }],
                body: Guarded::Unconditional(body),
                position: None,
            });
        }
        let scrutinee = value.expression();
        alternatives.push(Alternative::match_failure(std::slice::from_ref(&scrutinee), unvariant));
        let body = case_expression(scrutinee, alternatives, unvariant);
        Ok(Some(self.lambda(vec![value], body)))
    }

    fn pending_unvariant(&mut self, monotype: MonotypeId) -> Expression {
        self.note_pending();
        Expression::new(ExpressionKind::Fail(SmolStr::new_static(PENDING)), monotype)
    }

    fn constructor_labels(&mut self, scope: &Scope, data: &DataType) -> GoResult<Vec<SmolStr>> {
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&scope.definition))?;
        Ok(constructors.iter().map(|constructor| constructor.name.clone()).collect())
    }

    /// The labels of the closed row `r` that `unvariant :: Variant r -> Unvariant r` is
    /// specialized at.
    fn unvariant_row_labels(
        &mut self,
        (file_id, term): (FileId, TermItemId),
        instantiations: &Substitution,
    ) -> GoResult<Option<Vec<SmolStr>>> {
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else { return Ok(None) };
        let declared = self.outer_body(declared, &mut vec![]);
        let declared = self.context.types.substitute(declared, instantiations);
        let Some((variant, _)) = self.context.types.function_parts(declared) else {
            return Ok(None);
        };
        let (_, arguments) = self.context.types.spine(variant);
        let Some(&row) = arguments.first() else { return Ok(None) };
        let row = self.context.types.strip_annotations(row);
        let Type::Row(row) = *self.context.types.lookup(row) else { return Ok(None) };
        let row = self.context.queries.lookup_row_type(row).clone();
        if row.tail.is_some() {
            return Ok(None);
        }
        Ok(Some(row.fields.iter().map(|field| field.label.clone()).collect()))
    }

    /// The scheme of `Unvariant' r x`, the continuation an `Unvariant r` runs.
    fn unvariant_continuation(
        &mut self,
        (file_id, term): (FileId, TermItemId),
        instantiations: &Substitution,
    ) -> GoResult<Option<ConstrainedScheme>> {
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else { return Ok(None) };
        let declared = self.outer_body(declared, &mut vec![]);
        let declared = self.context.types.substitute(declared, instantiations);
        let Some((_, unvariant)) = self.context.types.function_parts(declared) else {
            return Ok(None);
        };
        let Some(unwrapped) = crate::monotype::newtype_unwrapped(&mut self.context, unvariant)?
        else {
            return Ok(None);
        };
        let unwrapped = crate::monotype::expand_synonyms(&mut self.context, unwrapped)?;
        let (_, runner) = self.context.types.peel_quantifiers(unwrapped);
        let Some((continuation, _)) = self.context.types.function_parts(runner) else {
            return Ok(None);
        };
        let continuation = crate::monotype::expand_synonyms(&mut self.context, continuation)?;
        Ok(crate::scheme::constrained_scheme(&mut self.context, continuation)?)
    }

    /// Each label of the Variant with the continuation's field for it, or None
    /// when some label's instantiation is discovered in this pass.
    fn label_continuations(
        &mut self,
        scope: &Scope,
        continuation: &ConstrainedScheme,
        labels: &[SmolStr],
    ) -> GoResult<Option<Vec<(SmolStr, SmolStr)>>> {
        let mut fields = Vec::with_capacity(labels.len());
        let mut discovered = false;
        for label in labels {
            let Some((types, dictionaries)) = self.label_instantiation(continuation, label)? else {
                return Ok(None);
            };
            match self.monotypes.schemes.find(&continuation.key, &types) {
                Some(known) => fields.push((label.clone(), known.label.clone())),
                None => {
                    let key = continuation.key.clone();
                    self.discover_labelled(scope, key, types, dictionaries, None)?;
                    discovered = true;
                }
            }
        }
        Ok((!discovered).then_some(fields))
    }

    /// The types and dictionaries of the continuation's instantiation at one
    /// label: its `Cons s t o r` solved by the label, its payload and the rest
    /// of the row, and `IsSymbol s` by the label itself.
    fn label_instantiation(
        &mut self,
        continuation: &ConstrainedScheme,
        label: &SmolStr,
    ) -> GoResult<Option<(Vec<TypeId>, Vec<Dictionary>)>> {
        let mut solved = Substitution::default();
        let mut dictionaries = Vec::with_capacity(continuation.constraints.len());
        for &constraint in &continuation.constraints {
            let (head, arguments) = self.context.types.spine(constraint);
            let Type::Constructor(file_id, item) = *self.context.types.lookup(head) else {
                return Ok(None);
            };
            if self.context.is_type(file_id, item, "Data.Symbol", "IsSymbol")? {
                dictionaries.push(Dictionary::Symbol(label.clone()));
                continue;
            }
            if !self.context.is_type(file_id, item, "Prim.Row", "Cons")? {
                return Ok(None);
            }
            let [symbol, payload, rest, row] = arguments[..] else { return Ok(None) };
            let Some((field, remaining)) = self.row_without(row, label) else { return Ok(None) };
            for (variable, solution) in
                [(symbol, self.symbol_type(label)), (payload, field), (rest, remaining)]
            {
                let Type::Rigid(name, ..) = *self.context.types.lookup(variable) else {
                    return Ok(None);
                };
                solved.insert(name, solution);
            }
            dictionaries.push(Dictionary::Trivial);
        }
        let types = continuation.names.iter().map(|name| solved.get(name).copied());
        let types: Option<Vec<TypeId>> = types.collect();
        Ok(types.map(|types| (types, dictionaries)))
    }

    /// The type of the row's field `label` and the row without it.
    fn row_without(&mut self, row: TypeId, label: &str) -> Option<(TypeId, TypeId)> {
        let row = self.context.types.strip_annotations(row);
        let Type::Row(row) = *self.context.types.lookup(row) else { return None };
        let row = self.context.queries.lookup_row_type(row).clone();
        let field = row.fields.iter().find(|field| field.label == label)?.id;
        let remaining = row.fields.iter().filter(|field| field.label != label).cloned();
        let remaining: Vec<RowField> = remaining.collect();
        let remaining = RowType { fields: Arc::from(remaining), tail: row.tail };
        let remaining = self.context.queries.intern_row_type(remaining);
        Some((field, self.context.queries.intern_type(Type::Row(remaining))))
    }

    fn symbol_type(&mut self, label: &str) -> TypeId {
        let text: Vec<u16> = label.encode_utf16().collect();
        let literal = lowering::StringLiteral::from_utf16(text);
        let literal = self.context.queries.intern_string_literal(literal);
        self.context.queries.intern_type(Type::String(lowering::StringKind::String, literal))
    }

    /// The Unvariant of one label: a function of the continuation, or one per
    /// answer type the Unvariant is run at, that applies the continuation's
    /// field for the label to a Proxy and the payload.
    fn run_continuation(
        &mut self,
        unvariant: MonotypeId,
        field: &str,
        hidden: &Local,
    ) -> Expression {
        let impossible = |monotype| {
            Expression::new(ExpressionKind::Fail(SmolStr::new_static(IMPOSSIBLE)), monotype)
        };
        match self.monotypes.get(unvariant).clone() {
            Monotype::Record(answers) => {
                let fields = answers.iter().map(|answer| {
                    (answer.label.clone(), self.run_continuation(answer.monotype, field, hidden))
                });
                let fields = fields.collect();
                Expression::new(ExpressionKind::Record(fields), unvariant)
            }
            Monotype::Function(continuation, answer) => {
                let Monotype::Record(handlers) = self.monotypes.get(continuation).clone() else {
                    return impossible(unvariant);
                };
                let Some(handler) = handlers.iter().find(|handler| handler.label == field) else {
                    return impossible(unvariant);
                };
                let Some((proxy, rest)) = self.monotypes.function_parts(handler.monotype) else {
                    return impossible(unvariant);
                };
                let Some((payload, result)) = self.monotypes.function_parts(rest) else {
                    return impossible(unvariant);
                };
                let Monotype::Data(proxy_data) = self.monotypes.get(proxy).clone() else {
                    return impossible(unvariant);
                };
                let parameter = self.fresh_local(SmolStr::new_static("continuation"), continuation);
                let kind = ExpressionKind::Access {
                    record: Box::new(parameter.expression()),
                    label: handler.label.clone(),
                };
                let function = Expression::new(kind, handler.monotype);
                let proxy_value = ExpressionKind::Construct {
                    data: proxy_data,
                    constructor: 0,
                    arguments: vec![],
                };
                let arguments = vec![
                    Expression::new(proxy_value, proxy),
                    self.coerce(hidden.expression(), payload),
                ];
                let kind = ExpressionKind::Apply { function: Box::new(function), arguments };
                let applied = self.coerce(Expression::new(kind, result), answer);
                self.lambda(vec![parameter], applied)
            }
            _ => impossible(unvariant),
        }
    }

    fn alternatives(
        &mut self,
        scope: &Scope,
        data: &DataType,
        variant: MonotypeId,
        mut body: impl FnMut(&mut Specializer<'q, Q>, SmolStr, Local) -> GoResult<Expression>,
    ) -> GoResult<Vec<Alternative>> {
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&scope.definition))?;
        let mut alternatives = Vec::with_capacity(constructors.len());
        for (index, constructor) in constructors.iter().enumerate() {
            let payload = constructor.fields[0];
            let hidden = self.fresh_local(self.monotypes.value_name(payload), payload);
            let expression = body(self, constructor.name.clone(), hidden.clone())?;
            let variable = PatternKind::Variable(hidden);
            let arguments = vec![Pattern { kind: variable, monotype: payload }];
            let data = data.clone();
            let kind = PatternKind::Constructor { data, constructor: index, arguments };
            let patterns = vec![Pattern { kind, monotype: variant }];
            let body = Guarded::Unconditional(expression);
            alternatives.push(Alternative { patterns, body, position: None });
        }
        Ok(alternatives)
    }

    fn apply_handler(
        &mut self,
        handler: Expression,
        hidden: Local,
        result: MonotypeId,
    ) -> GoResult<Expression> {
        let Some((parameter, answer)) = self.monotypes.function_parts(handler.monotype) else {
            return Ok(Expression::new(
                ExpressionKind::Fail(SmolStr::new_static(IMPOSSIBLE)),
                result,
            ));
        };
        let argument = self.coerce(hidden.expression(), parameter);
        let kind = ExpressionKind::Apply { function: Box::new(handler), arguments: vec![argument] };
        Ok(self.coerce(Expression::new(kind, answer), result))
    }

    fn handler(&self, handlers: &Local, label: &str) -> Option<Expression> {
        let Monotype::Record(fields) = self.monotypes.get(handlers.monotype) else { return None };
        let field = fields.iter().find(|field| field.label == label)?;
        let kind = ExpressionKind::Access {
            record: Box::new(handlers.expression()),
            label: field.label.clone(),
        };
        Some(Expression::new(kind, field.monotype))
    }

    fn reinject(
        &mut self,
        scope: &Scope,
        data: &DataType,
        variant: MonotypeId,
        label: SmolStr,
        hidden: Local,
    ) -> GoResult<Expression> {
        match self.label_index(scope, data, &label)? {
            Some(index) => self.inject_at(scope, data, index, hidden.expression(), variant),
            None => {
                let failure = ExpressionKind::Fail(SmolStr::new_static(UNHANDLED));
                Ok(Expression::new(failure, variant))
            }
        }
    }

    fn inject_at(
        &mut self,
        scope: &Scope,
        data: &DataType,
        index: usize,
        value: Expression,
        variant: MonotypeId,
    ) -> GoResult<Expression> {
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&scope.definition))?;
        let field = constructors[index].fields[0];
        let argument = self.coerce(value, field);
        let kind = ExpressionKind::Construct {
            data: data.clone(),
            constructor: index,
            arguments: vec![argument],
        };
        Ok(Expression::new(kind, variant))
    }

    fn label_index(
        &mut self,
        scope: &Scope,
        data: &DataType,
        label: &str,
    ) -> GoResult<Option<usize>> {
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&scope.definition))?;
        Ok(constructors.iter().position(|constructor| constructor.name == label))
    }

    fn variant_data(&self, monotype: MonotypeId) -> Option<DataType> {
        match self.monotypes.get(monotype) {
            Monotype::Data(data) if self.monotypes.variant_row(data).is_some() => {
                Some(data.clone())
            }
            _ => None,
        }
    }

    fn symbol(&self, type_id: TypeId) -> Option<SmolStr> {
        let type_id = self.context.types.strip_annotations(type_id);
        match *self.context.types.lookup(type_id) {
            Type::String(_, literal) => {
                let literal = self.context.queries.lookup_string_literal(literal);
                Some(SmolStr::from(super::symbol_text(literal)))
            }
            _ => None,
        }
    }

    fn arrows<const N: usize>(
        &self,
        monotype: MonotypeId,
    ) -> Option<([MonotypeId; N], MonotypeId)> {
        let mut parameters = [monotype; N];
        let mut rest = monotype;
        for parameter in parameters.iter_mut() {
            let (argument, result) = self.monotypes.function_parts(rest)?;
            *parameter = argument;
            rest = result;
        }
        Some((parameters, rest))
    }

    pub(super) fn note_variant_crossing(&mut self, source: &DataType, target: &DataType) {
        let rows = (self.monotypes.variant_row(source), self.monotypes.variant_row(target));
        let (Some(from), Some(to)) = rows else { return };
        if from == to {
            return;
        }
        self.variant_crossings.push((from, to));
        let labels = |this: &mut Specializer<'q, Q>, data: &DataType| -> Vec<SmolStr> {
            match this.monotypes.constructors(&mut this.context, data) {
                Ok(constructors) => {
                    constructors.iter().map(|constructor| constructor.name.clone()).collect()
                }
                Err(_) => vec![],
            }
        };
        let kept = labels(self, target);
        if labels(self, source).iter().any(|label| !kept.contains(label)) {
            self.narrowed_variant_rows.extend([from, to]);
            self.grown = true;
        }
    }

    pub(super) fn note_variant_narrowing(&mut self, target: &DataType) {
        if let Some(row) = self.monotypes.variant_row(target) {
            self.narrowed_variant_rows.push(row);
            self.grown = true;
        }
    }

    pub(super) fn narrowed_variant_rows_to_erase(&mut self) -> Vec<TypeId> {
        let narrowed = std::mem::take(&mut self.narrowed_variant_rows);
        if narrowed.is_empty() {
            return vec![];
        }
        let mut erased: Vec<TypeId> = vec![];
        let mut pending = narrowed;
        while let Some(row) = pending.pop() {
            if erased.contains(&row) || self.context.erased_variant_rows.contains(&row) {
                continue;
            }
            erased.push(row);
            for &(from, to) in &self.variant_crossings {
                if from == row {
                    pending.push(to);
                }
                if to == row {
                    pending.push(from);
                }
            }
        }
        erased
    }

    pub(super) fn mentions_variant(&self, monotype: MonotypeId) -> bool {
        match self.monotypes.get(monotype) {
            Monotype::Data(data) | Monotype::Recursive(data) | Monotype::ForeignData(data) => {
                self.monotypes.variant_row(data).is_some()
                    || data.arguments.iter().any(|&argument| self.type_mentions_variant(argument))
            }
            Monotype::Function(argument, result) => {
                self.mentions_variant(*argument) || self.mentions_variant(*result)
            }
            Monotype::Record(fields) => {
                fields.iter().any(|field| self.mentions_variant(field.monotype))
            }
            other => other.element().is_some_and(|element| self.mentions_variant(element)),
        }
    }

    fn type_mentions_variant(&self, type_id: TypeId) -> bool {
        let Some(variant) = self.monotypes.variant_type() else { return false };
        let type_id = self.context.types.strip_annotations(type_id);
        match self.context.types.lookup(type_id).clone() {
            Type::Constructor(file_id, item) => (file_id, item) == variant,
            Type::Application(function, argument) | Type::Function(function, argument) => {
                self.type_mentions_variant(function) || self.type_mentions_variant(argument)
            }
            Type::Row(row) => {
                let row = self.context.queries.lookup_row_type(row).clone();
                row.fields.iter().any(|field| self.type_mentions_variant(field.id))
                    || row.tail.is_some_and(|tail| self.type_mentions_variant(tail))
            }
            _ => false,
        }
    }
}

fn case_expression(
    scrutinee: Expression,
    mut alternatives: Vec<Alternative>,
    result: MonotypeId,
) -> Expression {
    let scrutinees = vec![scrutinee];
    if alternatives.is_empty() {
        alternatives.push(Alternative::match_failure(&scrutinees, result));
    }
    Expression::new(ExpressionKind::Case { scrutinees, alternatives }, result)
}
