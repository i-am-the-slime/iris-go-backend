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
            return Err(self.unsupported(scope, unsupported("reifyType without its constraint")));
        };
        if scheme.names.len() != 1 || scheme.constraints.len() != 1 {
            return Err(self.unsupported(scope, unsupported("reifyType of another shape")));
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
            return Err(self.unsupported(scope, unsupported("reifyType of another shape")));
        };
        let Some((proxy, answer)) = self.monotypes.function_parts(proxied) else {
            return Err(self.unsupported(scope, unsupported("reifyType of another shape")));
        };
        let Monotype::Data(proxy_data) = self.monotypes.get(proxy).clone() else {
            return Err(self.unsupported(scope, unsupported("reifyType without a Proxy")));
        };
        let value = self.fresh_local(self.monotypes.value_name(reified), reified);
        let handler = self.fresh_local(SmolStr::new_static("continuation"), continuation);
        let access = ExpressionKind::Access { record: Box::new(handler.expression()), label };
        let access = Expression::new(access, field);
        let arguments = vec![value.expression()];
        let applied = ExpressionKind::Apply { function: Box::new(access), arguments };
        let applied = Expression::new(applied, proxied);
        let proxy_value =
            ExpressionKind::Construct { data: proxy_data, constructor: 0, arguments: vec![] };
        let arguments = vec![Expression::new(proxy_value, proxy)];
        let answered = ExpressionKind::Apply { function: Box::new(applied), arguments };
        let answered = self.coerce(Expression::new(answered, answer), result);
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
