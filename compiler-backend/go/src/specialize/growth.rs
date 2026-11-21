use checking::{TypeId, tree};

use super::{Scope, Specializer};
use crate::erasure::Erasure;
use crate::error::GoResult;
use crate::mono::Expression;
use crate::scheme::{SchemeKey, rank_n_scheme};

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn grows_construction(&self, key: &SchemeKey, types: &[TypeId]) -> bool {
        self.constructing.iter().any(|(constructed, enclosing)| {
            constructed == key
                && types
                    .iter()
                    .zip(enclosing.iter())
                    .any(|(&requested, &enclosing)| self.context.types.grows(requested, enclosing))
        })
    }

    pub(super) fn grown_construction(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
        closed: TypeId,
    ) -> GoResult<Option<Expression>> {
        if !self.monotypes.schemes.has_grown() {
            return Ok(None);
        }
        let Some(scheme) = rank_n_scheme(&mut self.context, closed)? else { return Ok(None) };
        let grown = self.monotypes.schemes.rank_n_erasure(&scheme.key);
        if grown != Erasure::PolymorphicRecursion
            || scheme.names.iter().any(|name| !name.scoped || scope.substitution.contains_key(name))
        {
            return Ok(None);
        }
        let erased = self.context.types.erased(Erasure::PolymorphicRecursion);
        let substitution = scope.substitution.clone();
        scope.substitution.extend(scheme.names.iter().map(|&name| (name, erased)));
        let enclosing = scope.rank_n_body.replace(id);
        let value = self.translate_expression_at(scope, id);
        scope.rank_n_body = enclosing;
        scope.substitution = substitution;
        value.map(Some)
    }
}
