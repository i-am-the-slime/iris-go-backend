//! `Data.Reflectable.reifyType`, which hands its continuation a `Reflectable v t` dictionary that
//! reflects a value known only at run time.

use checking::core::Type;
use files::FileId;
use indexing::TermItemId;
use smol_str::SmolStr;

use super::{Scope, Specializer};
use crate::dictionary::{Dictionary, Reflected};
use crate::error::{GoResult, UnsupportedState};
use crate::monomorphic::{Expression, ExpressionKind};
use crate::monotype::{Monotype, MonotypeId};
use crate::scheme::constrained_scheme;
use crate::types::Substitution;

const PENDING: &str = "reified instantiation discovered in this pass";

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// `reifyType value continuation` applies the continuation's instantiation that takes the
    /// reified value, for a `v` nothing else constrains, to that value and a `Proxy`.
    pub(super) fn reify_type(
        &mut self,
        scope: &Scope,
        (file_id, term): (FileId, TermItemId),
        instantiations: &Substitution,
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        let Some((reified, rest)) = self.monotypes.function_parts(monotype) else {
            return Ok(None);
        };
        let Some((continuation, result)) = self.monotypes.function_parts(rest) else {
            return Ok(None);
        };
        let scheme = self.continuation_type((file_id, term), 1, instantiations)?;
        let Some(scheme) = constrained_scheme(&mut self.context, scheme)? else {
            return Err(scope.unsupported(unsupported("reifyType without its constraint")));
        };
        if scheme.names.len() != 1 || scheme.constraints.len() != 1 {
            return Err(scope.unsupported(unsupported("reifyType of another shape")));
        }
        let types = vec![self.context.queries.intern_type(Type::Unification(u32::MAX))];
        let Some(known) = self.monotypes.schemes.find(&scheme.key, &types) else {
            let dictionaries = vec![Dictionary::Reflectable(Reflected::Reified)];
            let label = Some(SmolStr::new_static("Reified"));
            self.discover_labelled(scope, scheme.key, types, dictionaries, label)?;
            return Ok(Some(self.reified_pending(monotype)));
        };
        let label = known.label.clone();
        let field = match self.monotypes.get(continuation) {
            Monotype::Record(fields) => fields.iter().find(|field| field.label == label),
            _ => None,
        };
        let Some(field) = field.map(|field| field.monotype) else {
            return Ok(Some(self.reified_pending(monotype)));
        };
        let Some((_, proxied)) = self.monotypes.function_parts(field) else {
            return Err(scope.unsupported(unsupported("reifyType of another shape")));
        };
        let Some((proxy, answer)) = self.monotypes.function_parts(proxied) else {
            return Err(scope.unsupported(unsupported("reifyType of another shape")));
        };
        let Monotype::Data(proxy_data) = self.monotypes.get(proxy).clone() else {
            return Err(scope.unsupported(unsupported("reifyType without a Proxy")));
        };
        let value = self.fresh_local(self.monotypes.value_name(reified), reified);
        let handler = self.fresh_local(SmolStr::new_static("continuation"), continuation);
        let access = ExpressionKind::Access { record: Box::new(handler.expression()), label };
        let access = Expression::new(access, field);
        let arguments = vec![value.expression()];
        let applied = ExpressionKind::Apply { function: Box::new(access), arguments };
        let applied = Expression::new(applied, proxied);
        let arguments = vec![];
        let proxy_value = ExpressionKind::Construct { data: proxy_data, constructor: 0, arguments };
        let arguments = vec![Expression::new(proxy_value, proxy)];
        let answered = ExpressionKind::Apply { function: Box::new(applied), arguments };
        let answered = self.coerce(Expression::new(answered, answer), result);
        let inner = self.lambda(vec![handler], answered);
        Ok(Some(self.lambda(vec![value], inner)))
    }

    pub(super) fn provide(
        &mut self,
        scope: &Scope,
        (file_id, term): (FileId, TermItemId),
        instantiations: &Substitution,
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        let Some((provided, rest)) = self.monotypes.function_parts(monotype) else {
            return Ok(None);
        };
        let Some((continuation, result)) = self.monotypes.function_parts(rest) else {
            return Ok(None);
        };
        let scheme = self.continuation_type((file_id, term), 1, instantiations)?;
        let Some(scheme) = constrained_scheme(&mut self.context, scheme)? else {
            return Err(scope.unsupported(unsupported("provide without its constraint")));
        };
        if !scheme.names.is_empty() || scheme.constraints.len() != 1 {
            return Err(scope.unsupported(unsupported("provide of another shape")));
        }
        let Some((runtime, _)) = self.monotypes.schemes.at_run_time(&scheme.key) else {
            self.pass_scheme_at_run_time(scope, &scheme, false)?;
            return Ok(Some(self.reified_pending(monotype)));
        };
        let label = runtime.label;
        let field = match self.monotypes.get(continuation) {
            Monotype::Record(fields) => fields.iter().find(|field| field.label == label),
            _ => None,
        };
        let Some(field) = field.map(|field| field.monotype) else {
            return Ok(Some(self.reified_pending(monotype)));
        };
        let Some((dictionary, answer)) = self.monotypes.function_parts(field) else {
            return Err(scope.unsupported(unsupported("provide of another shape")));
        };
        let Monotype::Record(members) = self.monotypes.get(dictionary).clone() else {
            return Err(scope.unsupported(unsupported("provide of another shape")));
        };
        let value = self.fresh_local(SmolStr::new_static("context"), provided);
        let mut fields = Vec::with_capacity(members.len());
        for member in members.iter() {
            let member_value = match self.monotypes.get(member.monotype) {
                Monotype::Record(superclass) if superclass.is_empty() => {
                    Expression::new(ExpressionKind::Record(vec![]), member.monotype)
                }
                _ => self.coerce(value.expression(), member.monotype),
            };
            fields.push((member.label.clone(), member_value));
        }
        let dictionary = Expression::new(ExpressionKind::Record(fields), dictionary);
        let handler = self.fresh_local(SmolStr::new_static("continuation"), continuation);
        let access = ExpressionKind::Access { record: Box::new(handler.expression()), label };
        let access = Expression::new(access, field);
        let arguments = vec![dictionary];
        let applied = ExpressionKind::Apply { function: Box::new(access), arguments };
        let answered = self.coerce(Expression::new(applied, answer), result);
        let inner = self.lambda(vec![handler], answered);
        Ok(Some(self.lambda(vec![value], inner)))
    }

    fn reified_pending(&mut self, monotype: MonotypeId) -> Expression {
        self.note_pending();
        Expression::new(ExpressionKind::Fail(SmolStr::new_static(PENDING)), monotype)
    }
}

fn unsupported(construct: &'static str) -> UnsupportedState {
    UnsupportedState::Construct { construct }
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn call_by_name(
        &mut self,
        scope: &Scope,
        primitive: crate::primitives::Primitive,
        (file_id, term): (FileId, TermItemId),
        instantiations: &Substitution,
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        use crate::primitives::Primitive;
        let applies = matches!(primitive, Primitive::DeferApply | Primitive::DeferLazyApply);
        let position = usize::from(applies);
        let scheme = self.continuation_type((file_id, term), position, instantiations)?;
        let scheme = crate::monotype::expand_synonyms(&mut self.context, scheme)?;
        let Some(scheme) = constrained_scheme(&mut self.context, scheme)? else {
            return Err(scope.unsupported(unsupported("a CBN value without its constraint")));
        };
        if !scheme.names.is_empty() || scheme.constraints.len() != 1 {
            return Err(scope.unsupported(unsupported("a CBN value of another shape")));
        }
        let Some((runtime, _)) = self.monotypes.schemes.at_run_time(&scheme.key) else {
            self.pass_scheme_at_run_time(scope, &scheme, false)?;
            return Ok(Some(self.reified_pending(monotype)));
        };
        let Some((first, rest)) = self.monotypes.function_parts(monotype) else { return Ok(None) };
        let (applied, value, result) = match applies {
            true => {
                let Some((value, result)) = self.monotypes.function_parts(rest) else {
                    return Ok(None);
                };
                (Some(first), value, result)
            }
            false => (None, first, rest),
        };
        let field = match self.monotypes.get(value) {
            Monotype::Record(fields) => fields.iter().find(|field| field.label == runtime.label),
            _ => None,
        };
        let Some(field) = field.map(|field| field.monotype) else {
            return Ok(Some(self.reified_pending(monotype)));
        };
        let Some((dictionary, answer)) = self.monotypes.function_parts(field) else {
            return Err(scope.unsupported(unsupported("a CBN value of another shape")));
        };
        let handler = self.fresh_local(SmolStr::new_static("deferred"), value);
        let label = runtime.label;
        let access = ExpressionKind::Access { record: Box::new(handler.expression()), label };
        let access = Expression::new(access, field);
        let dictionary = Expression::new(ExpressionKind::Record(vec![]), dictionary);
        let arguments = vec![dictionary];
        let forced = ExpressionKind::Apply { function: Box::new(access), arguments };
        let forced = Expression::new(forced, answer);
        let delayed_monotype = match applied {
            Some(applied) => self.monotypes.function_parts(applied).map(|(argument, _)| argument),
            None => Some(result),
        };
        let Some(delayed_monotype) = delayed_monotype else { return Ok(None) };
        let thunk_monotype = match self.monotypes.get(delayed_monotype).clone() {
            Monotype::Lazy(inner) => {
                let unit = self.monotypes.intern(Monotype::Unit);
                self.monotypes.function(unit, inner)
            }
            _ => delayed_monotype,
        };
        let Some((unit, thunk_result)) = self.monotypes.function_parts(thunk_monotype) else {
            return Ok(None);
        };
        let ignored = self.fresh_local(SmolStr::new_static("unit"), unit);
        let forced = self.coerce(forced, thunk_result);
        let thunk = self.lambda(vec![ignored], forced);
        let thunk = Expression::new(thunk.kind, thunk_monotype);
        let delayed = match self.monotypes.get(delayed_monotype) {
            Monotype::Lazy(_) => {
                let kind = ExpressionKind::Foreign {
                    foreign: &crate::foreign::Foreign::LazyDefer,
                    arguments: vec![thunk],
                };
                Expression::new(kind, delayed_monotype)
            }
            _ => thunk,
        };
        let Some(applied) = applied else {
            return Ok(Some(self.lambda(vec![handler], delayed)));
        };
        let function = self.fresh_local(SmolStr::new_static("use"), applied);
        let call = ExpressionKind::Apply {
            function: Box::new(function.expression()),
            arguments: vec![delayed],
        };
        let call = Expression::new(call, result);
        let inner = self.lambda(vec![handler], call);
        Ok(Some(self.lambda(vec![function], inner)))
    }
}
