use std::sync::Arc;

use checking::{TypeId, tree};
use smol_str::SmolStr;

use super::{Definition, PolymorphicLocal, Scope, SpecializationKey, Specializer, runtime};
use crate::dictionary::{Dictionary, RuntimeDictionary};
use crate::erasure::Erasure;
use crate::error::{GoResult, UnsupportedState};
use crate::monomorphic::{Expression, ExpressionKind};
use crate::monotype::{Monotype, MonotypeId};
use crate::scheme::{
    ConstrainedScheme, SCHEME_INSTANTIATION_LIMIT, SchemeInstantiation, SchemeKey, rank_n_scheme,
};
use crate::types::Substitution;

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn grows_construction(&self, key: &SchemeKey, types: &[TypeId]) -> bool {
        self.constructing.iter().any(|(constructed, enclosing)| {
            constructed == key && self.context.types.grows_all(types, enclosing)
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
        key: SpecializationKey,
    ) -> GoResult<(SpecializationKey, Vec<runtime::Promotion>)> {
        let (key, mut promotions) = self.terminate_instance_growth(key)?;
        let (key, own) = self.terminate_definition_growth(key)?;
        promotions.extend(own);
        Ok((key, promotions))
    }

    /// An instance's members can reach the same instance at larger types, as
    /// `Show (Nested a)` shows a `Nested (Array a)`: the instance's growing
    /// types are erased, and the context dictionaries that mention them are
    /// passed at run time.
    fn terminate_instance_growth(
        &mut self,
        mut key: SpecializationKey,
    ) -> GoResult<(SpecializationKey, Vec<runtime::Promotion>)> {
        let Definition::Member { dictionary, member } = &key.definition else {
            return Ok((key, vec![]));
        };
        let requested = Arc::clone(&dictionary.types);
        let mut types: Vec<TypeId> = requested.to_vec();
        let mut grows = false;
        let mut ancestor = self.current;
        while let Some(id) = ancestor {
            let definition = &self.function_keys[id.0 as usize].definition;
            if let Definition::Member { dictionary: enclosing, .. } = definition
                && enclosing.origin == dictionary.origin
                && self.context.types.grows_all(&requested, &enclosing.types)
            {
                for (position, &enclosing_type) in enclosing.types.iter().enumerate() {
                    let Some(&requested_type) = types.get(position) else { continue };
                    if self.context.types.grows(requested_type, enclosing_type) {
                        types[position] = self.context.types.erased(Erasure::PolymorphicRecursion);
                        grows = true;
                    }
                }
            }
            ancestor = self.parents[id.0 as usize];
        }
        if !grows {
            return Ok((key, vec![]));
        }
        let member = *member;
        let promoted = self.promote_growing_context(&key.definition, dictionary, &types)?;
        let (dictionary, promotions) = promoted;
        key.definition = Definition::Member { dictionary, member };
        Ok((key, promotions))
    }

    fn terminate_definition_growth(
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
            if ancestor_key.definition == key.definition
                && self.context.types.grows_all(&requested, &ancestor_key.types)
            {
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
            if !self.context.types.grows_all(requested, &specialization.types) {
                ancestor = specialization.requester;
                continue;
            }
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

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn evidence_grows(&self, scheme: &ConstrainedScheme, types: &[TypeId]) -> bool {
        if scheme.constraints.is_empty()
            || self.monotypes.schemes.rank_n_owner(&scheme.key).is_some()
        {
            return false;
        }
        let known = self.monotypes.schemes.get(&scheme.key).len();
        known + 1 >= SCHEME_INSTANTIATION_LIMIT || self.grows_construction(&scheme.key, types)
    }

    pub(super) fn pass_scheme_at_run_time(
        &mut self,
        scope: &Scope,
        scheme: &ConstrainedScheme,
        grows: bool,
    ) -> GoResult<()> {
        let erased = self.context.types.erased(Erasure::PolymorphicRecursion);
        let substitution: Substitution = scheme.names.iter().map(|&name| (name, erased)).collect();
        let mut dictionaries = Vec::with_capacity(scheme.constraints.len());
        let mut monotypes = vec![];
        for &constraint in &scheme.constraints {
            if crate::monotype::is_partial(&mut self.context, constraint)? {
                dictionaries.push(Dictionary::Trivial);
                continue;
            }
            let constraint = self.context.types.substitute(constraint, &substitution);
            monotypes.push(self.runtime_monotype(&scope.definition, constraint)?);
            dictionaries.push(Dictionary::Runtime(RuntimeDictionary { constraint, value: None }));
            if grows {
                self.note_scheme_at_run_time(scope, constraint)?;
            }
        }
        let instantiation = SchemeInstantiation {
            types: scheme.names.iter().map(|_| erased).collect(),
            dictionaries: Arc::from(dictionaries),
            label: SmolStr::new_static("AtRunTime"),
        };
        if let Some(functions) = self.constructions.get(&scheme.key) {
            self.stale.extend(functions.iter().copied());
        }
        self.monotypes.schemes.pass_at_run_time(scheme.key.clone(), instantiation, monotypes);
        self.grown = true;
        Ok(())
    }

    pub(super) fn scheme_value_at_run_time(
        &mut self,
        scope: &mut Scope,
        scheme: &ConstrainedScheme,
        value: Expression,
        runtime: SchemeInstantiation,
        (types, dictionaries): (&[TypeId], Vec<Dictionary>),
        monotype: MonotypeId,
    ) -> GoResult<Expression> {
        let field = match self.monotypes.get(value.monotype) {
            Monotype::Record(fields) => fields.iter().find(|field| field.label == runtime.label),
            _ => None,
        };
        let Some(field) = field.map(|field| field.monotype) else {
            self.note_pending();
            let pending = SmolStr::new_static("run-time instantiation discovered in this pass");
            return Ok(Expression::new(ExpressionKind::Fail(pending), monotype));
        };
        if dictionaries.len() != scheme.constraints.len() {
            return Err(scope.unsupported(UnsupportedState::UnabstractedEvidence));
        }
        let substitution = scheme.names.iter().copied().zip(types.iter().copied());
        let substitution: Substitution = substitution.collect();
        let mut arguments = vec![];
        let passed = dictionaries.into_iter().zip(scheme.constraints.iter());
        for ((dictionary, &constraint), expected) in passed.zip(runtime.dictionaries.iter()) {
            let Dictionary::Runtime(RuntimeDictionary { constraint: erased, value: None }) =
                expected
            else {
                continue;
            };
            let constraint = self.context.types.substitute(constraint, &substitution);
            arguments.push(self.runtime_value(scope, dictionary, constraint, *erased)?);
        }
        let label = runtime.label;
        let access = ExpressionKind::Access { record: Box::new(value), label };
        let access = Expression::new(access, field);
        if arguments.is_empty() {
            return Ok(self.coerce(access, monotype));
        }
        let mut result = field;
        for _ in &arguments {
            let Some((_, rest)) = self.monotypes.function_parts(result) else {
                return Err(scope.unsupported(UnsupportedState::UnabstractedEvidence));
            };
            result = rest;
        }
        let applied = ExpressionKind::Apply { function: Box::new(access), arguments };
        Ok(self.coerce(Expression::new(applied, result), monotype))
    }
}
