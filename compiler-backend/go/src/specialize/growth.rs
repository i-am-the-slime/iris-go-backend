use std::sync::Arc;

use checking::{TypeId, tree};

use super::{PolymorphicLocal, Scope, SpecializationKey, Specializer, runtime};
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

    /// Polymorphic recursion requests a definition at ever larger types. When a
    /// request embeds the types of the same definition further up its chain of
    /// requesters, the growing positions are erased so specialization terminates.
    pub(super) fn terminate_growth(
        &mut self,
        mut key: SpecializationKey,
    ) -> GoResult<(SpecializationKey, Vec<runtime::Promotion>)> {
        let requested = Arc::clone(&key.types);
        let mut ancestor = self.current;
        let mut types: Vec<TypeId> = key.types.to_vec();
        let mut changed = false;
        let mut evidence_grows = false;
        while let Some(id) = ancestor {
            let ancestor_key = &self.function_keys[id.0 as usize];
            if ancestor_key.definition == key.definition {
                let mut grows = false;
                for (position, ancestor_type) in ancestor_key.types.iter().enumerate() {
                    let Some(requested) = types.get(position).copied() else { continue };
                    if self.context.types.grows(requested, *ancestor_type) {
                        types[position] = self.context.types.erased(Erasure::PolymorphicRecursion);
                        grows = true;
                    }
                }
                evidence_grows |= grows && ancestor_key.dictionaries != key.dictionaries;
                changed |= grows;
            }
            ancestor = self.parents[id.0 as usize];
        }
        if changed {
            key.types = Arc::from(types);
        }
        if !evidence_grows {
            return Ok((key, vec![]));
        }
        let promotions = self.promote_growing_evidence(&mut key, &requested)?;
        Ok((key, promotions))
    }

    pub(super) fn terminate_local_growth(
        &self,
        polymorphic: &PolymorphicLocal,
        requested: &[TypeId],
    ) -> Vec<TypeId> {
        let mut types = requested.to_vec();
        let mut ancestor = polymorphic.active;
        while let Some(index) = ancestor {
            let specialization = &polymorphic.specializations[index];
            for (position, &ancestor_type) in specialization.types.iter().enumerate() {
                let Some(&requested) = types.get(position) else { continue };
                if self.context.types.grows(requested, ancestor_type) {
                    types[position] = self.context.types.erased(Erasure::PolymorphicRecursion);
                }
            }
            ancestor = specialization.requester;
        }
        types
    }
}
