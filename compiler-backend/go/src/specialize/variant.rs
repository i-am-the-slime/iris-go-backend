use checking::TypeId;
use checking::core::Type;
use smol_str::SmolStr;

use super::{Scope, Specializer};
use crate::error::GoResult;
use crate::mono::{Alternative, Expression, ExpressionKind, Guarded, Local, Pattern, PatternKind};
use crate::monotype::{DataType, Monotype, MonotypeId};
use crate::primitives::Primitive;

const IMPOSSIBLE: &str = "Data.Variant: pattern match failure";
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
            | Primitive::ReifyType
            | Primitive::ToSigned
            | Primitive::ToUnsigned
            | Primitive::ReadJson
            | Primitive::WriteJson => Ok(None),
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
        let Some(([proxy, handler, fallback, variant], result)) = self.arrows::<4>(monotype)
        else {
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
        let body = self.case(value.expression(), alternatives, result);
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
        let body = self.case(value.expression(), alternatives, result);
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
        let body = self.case(value.expression(), alternatives, result);
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
        let body = self.case(value.expression(), alternatives, result);
        Ok(Some(self.lambda(vec![handlers, fallback, value], body)))
    }

    fn alternatives(
        &mut self,
        scope: &Scope,
        data: &DataType,
        variant: MonotypeId,
        mut body: impl FnMut(&mut Self, SmolStr, Local) -> GoResult<Expression>,
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
            let arguments =
                vec![Pattern { kind: PatternKind::Variable(hidden), monotype: payload }];
            let kind = PatternKind::Constructor { data: data.clone(), constructor: index, arguments };
            let patterns = vec![Pattern { kind, monotype: variant }];
            alternatives.push(Alternative { patterns, body: Guarded::Unconditional(expression) });
        }
        Ok(alternatives)
    }

    fn case(
        &mut self,
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

    fn apply_handler(
        &mut self,
        handler: Expression,
        hidden: Local,
        result: MonotypeId,
    ) -> GoResult<Expression> {
        let Some((parameter, answer)) = self.monotypes.function_parts(handler.monotype) else {
            return Ok(Expression::new(ExpressionKind::Fail(SmolStr::new_static(IMPOSSIBLE)), result));
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
            Monotype::Data(data) if self.monotypes.variant_row(data).is_some() => Some(data.clone()),
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

    fn arrows<const N: usize>(&self, monotype: MonotypeId) -> Option<([MonotypeId; N], MonotypeId)> {
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
        let (Some(from), Some(to)) =
            (self.monotypes.variant_row(source), self.monotypes.variant_row(target))
        else {
            return;
        };
        if from == to {
            return;
        }
        self.variant_crossings.push((from, to));
        let labels = |this: &mut Self, data: &DataType| -> Vec<SmolStr> {
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
