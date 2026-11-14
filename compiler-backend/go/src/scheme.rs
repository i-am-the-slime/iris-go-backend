use std::sync::Arc;

use building_types::QueryResult;
use checking::TypeId;
use checking::core::{Depth, Name, Type};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::context::Context;
use crate::dictionary::Dictionary;
use crate::erasure::Erasure;
use crate::types::Substitution;

pub const SCHEME_INSTANTIATION_LIMIT: usize = 64;

pub struct ConstrainedScheme {
    pub names: Vec<Name>,
    pub constraints: Vec<TypeId>,
    pub body: TypeId,
    pub key: SchemeKey,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SchemeKey(Arc<[TypeId]>);

#[derive(Debug, Clone)]
pub struct SchemeInstantiation {
    pub types: Arc<[TypeId]>,
    pub dictionaries: Arc<[Dictionary]>,
    pub label: SmolStr,
}

#[derive(Debug, Clone, Default)]
pub struct SchemeInstantiations {
    known: FxHashMap<SchemeKey, Vec<SchemeInstantiation>>,
    rank_n: FxHashMap<SchemeKey, String>,
    erased_owners: rustc_hash::FxHashSet<String>,
    grown_keys: rustc_hash::FxHashSet<SchemeKey>,
}

impl SchemeInstantiations {
    pub fn get(&self, key: &SchemeKey) -> &[SchemeInstantiation] {
        self.known.get(key).map_or(&[], Vec::as_slice)
    }

    pub fn find(&self, key: &SchemeKey, types: &[TypeId]) -> Option<&SchemeInstantiation> {
        self.get(key).iter().find(|instantiation| *instantiation.types == *types)
    }

    /// Whether an unconstrained `forall` with this key is specialized.
    pub fn is_rank_n(&self, key: &SchemeKey) -> bool {
        self.rank_n.contains_key(key)
    }

    /// Specializes the rank-N field type `key` of `owner`, a newtype or
    /// constructor, unless that owner's fields stay erased.
    pub fn add_rank_n(&mut self, key: SchemeKey, owner: String) {
        if !self.erased_owners.contains(&owner) {
            self.rank_n.insert(key, owner);
        }
    }

    /// Keeps every rank-N field of `owner` erased: some occurrence of it holds
    /// already-erased types (a VariantF's functor, say), and values move
    /// between its occurrences by coercion, which only a shared representation
    /// allows.
    pub fn erase_owner(&mut self, owner: String) {
        self.rank_n.retain(|_, existing| *existing != owner);
        self.erased_owners.insert(owner);
    }

    pub fn is_erased_owner(&self, owner: &str) -> bool {
        self.erased_owners.contains(owner)
    }

    pub fn rank_n_owner(&self, key: &SchemeKey) -> Option<&str> {
        self.rank_n.get(key).map(String::as_str)
    }

    pub fn erase_growing_owner(&mut self, owner: String) {
        let grown = self.rank_n.iter().filter(|(_, existing)| **existing == owner);
        let grown: Vec<SchemeKey> = grown.map(|(key, _)| key.clone()).collect();
        self.grown_keys.extend(grown);
        self.erase_owner(owner);
    }

    pub fn has_grown(&self) -> bool {
        !self.grown_keys.is_empty()
    }

    pub fn rank_n_erasure(&self, key: &SchemeKey) -> Erasure {
        if self.grown_keys.contains(key) { Erasure::PolymorphicRecursion } else { Erasure::RankN }
    }

    pub fn insert(&mut self, key: SchemeKey, instantiation: SchemeInstantiation) {
        self.known.entry(key).or_default().push(instantiation);
    }
}

impl SchemeKey {
    /// The first keyed type: a rank-N scheme's canonical body.
    pub fn body(&self) -> TypeId {
        self.0[0]
    }
}

impl ConstrainedScheme {
    pub fn instantiate<Q>(&self, context: &Context<'_, Q>, types: &[TypeId]) -> TypeId
    where
        Q: checking::ExternalQueries,
    {
        let substitution: Substitution =
            self.names.iter().copied().zip(types.iter().copied()).collect();
        context.types.substitute(self.body, &substitution)
    }
}

pub fn constrained_scheme<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
) -> QueryResult<Option<ConstrainedScheme>>
where
    Q: checking::ExternalQueries,
{
    let type_id = context.types.strip_annotations(type_id);
    if !matches!(context.types.lookup(type_id), Type::Forall(..)) {
        return Ok(None);
    }
    let (names, inner) = context.types.peel_quantifiers(type_id);
    let (constraints, body) = context.types.peel_constraints(inner);
    let mut needs_dictionaries = false;
    for &constraint in &constraints {
        if !crate::monotype::is_partial(context, constraint)? {
            needs_dictionaries = true;
        }
    }
    if !needs_dictionaries {
        return Ok(None);
    }
    let placeholders: Substitution = names
        .iter()
        .enumerate()
        .map(|(position, &name)| (name, placeholder(context, position)))
        .collect();
    let canonical =
        constraints.iter().map(|&constraint| context.types.substitute(constraint, &placeholders));
    let key = SchemeKey(canonical.collect());
    Ok(Some(ConstrainedScheme { names, constraints, body, key }))
}

/// An unconstrained `forall`, such as a CPS parser's answer type, keyed by its
/// body: values of the type become one specialization per instantiation, like
/// constrained schemes. The caller decides whether the body depends on the
/// variables at all (a phantom region needs no specialization).
pub fn rank_n_scheme<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
) -> QueryResult<Option<ConstrainedScheme>>
where
    Q: checking::ExternalQueries,
{
    let type_id = context.types.strip_annotations(type_id);
    if !matches!(context.types.lookup(type_id), Type::Forall(..)) {
        return Ok(None);
    }
    let (names, inner) = context.types.peel_quantifiers(type_id);
    let (constraints, body) = context.types.peel_constraints(inner);
    for &constraint in &constraints {
        if !crate::monotype::is_partial(context, constraint)? {
            return Ok(None);
        }
    }
    let placeholders: Substitution = names
        .iter()
        .enumerate()
        .map(|(position, &name)| (name, placeholder(context, position)))
        .collect();
    // The key is the body in a canonical spelling, so that every occurrence of
    // the same rank-N type finds the same instantiations.
    let keyed = context.types.substitute(body, &placeholders);
    let keyed = crate::monotype::expand_synonyms(context, keyed)?;
    let key = SchemeKey(Arc::from([keyed]));
    Ok(Some(ConstrainedScheme { names, constraints: vec![], body, key }))
}

fn placeholder<Q>(context: &Context<'_, Q>, position: usize) -> TypeId
where
    Q: checking::ExternalQueries,
{
    let unique = u32::MAX - 1 - position as u32;
    let name = Name { file: context.queries.prim_id(), unique, scoped: false };
    let kind = context.queries.intern_type(Type::Unification(u32::MAX));
    context.queries.intern_type(Type::Rigid(name, Depth(0), kind))
}
