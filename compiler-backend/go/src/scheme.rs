use std::cell::RefCell;
use std::sync::Arc;

use building_types::QueryResult;
use checking::TypeId;
use checking::core::{Name, Type};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::context::Context;
use crate::dictionary::{Dictionary, Reflected};
use crate::erasure::Erasure;
use crate::monotype::DataType;
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
    /// Field types an erased owner holds, which stay erased whichever other
    /// owner holds them too.
    erased_keys: rustc_hash::FxHashSet<SchemeKey>,
    coerced_sources: FxHashMap<SchemeKey, Vec<SchemeKey>>,
    grown_keys: rustc_hash::FxHashSet<SchemeKey>,
    families: FxHashMap<TypeId, ExistsFamily>,
    erased_families: FxHashMap<TypeId, Erasure>,
    continuation_families: FxHashMap<SchemeKey, TypeId>,
    accumulators: FxHashMap<SchemeKey, TypeId>,
    version: u32,
    written: FxHashMap<Decision, u32>,
    reads: RefCell<Vec<Read>>,
}

/// One answer the schemes give, which specialization reads and growth may
/// change: a function that read an answer before it changed is specialized
/// again.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Decision {
    Instantiations(SchemeKey),
    RankN(SchemeKey),
    ErasedKey(SchemeKey),
    Grown(SchemeKey),
    AnyGrown,
    ErasedOwner(String),
    Coerced(SchemeKey),
    Witnesses(TypeId),
    Continuations(TypeId),
    FamilyErasure(TypeId),
    VariantErasure(TypeId),
    ContinuationFamily(SchemeKey),
    Accumulator(SchemeKey),
}

/// A read of the schemes: a decision at the version the schemes had then,
/// or a cached conversion whose own reads stand for it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Read {
    Decision(Decision, u32),
    Converted(TypeId),
    Unfolded(DataType),
    Constructors(DataType),
}

#[derive(Debug, Clone, Default)]
pub struct ExistsFamily {
    pub witnesses: Vec<SchemeInstantiation>,
    pub continuations: Vec<SchemeKey>,
}

impl SchemeInstantiations {
    fn note_read(&self, decision: Decision) {
        self.reads.borrow_mut().push(Read::Decision(decision, self.version));
    }

    fn note_write(&mut self, decision: Decision) {
        self.version += 1;
        self.written.insert(decision, self.version);
    }

    pub fn note_cached(&self, read: Read) {
        self.reads.borrow_mut().push(read);
    }

    pub fn reads_len(&self) -> usize {
        self.reads.borrow().len()
    }

    pub fn reads_since(&self, start: usize) -> Vec<Read> {
        self.reads.borrow()[start..].to_vec()
    }

    pub fn take_reads(&self) -> Vec<Read> {
        std::mem::take(&mut *self.reads.borrow_mut())
    }

    /// The number of writes so far; equal before and after a round that grew
    /// nothing.
    pub fn version(&self) -> u32 {
        self.version
    }

    /// Whether the decision changed after the version at which it was read.
    pub fn is_written_since(&self, decision: &Decision, version: u32) -> bool {
        self.written.get(decision).is_some_and(|&written| written > version)
    }

    pub fn get(&self, key: &SchemeKey) -> &[SchemeInstantiation] {
        self.note_read(Decision::Instantiations(key.clone()));
        self.known.get(key).map_or(&[], Vec::as_slice)
    }

    pub fn find(&self, key: &SchemeKey, types: &[TypeId]) -> Option<&SchemeInstantiation> {
        self.get(key).iter().find(|instantiation| *instantiation.types == *types)
    }

    pub fn accumulator(&self, key: &SchemeKey) -> Option<TypeId> {
        self.note_read(Decision::Accumulator(key.clone()));
        self.accumulators.get(key).copied()
    }

    pub fn add_accumulator(&mut self, key: SchemeKey, accumulator: TypeId) -> bool {
        if self.accumulators.contains_key(&key) {
            return false;
        }
        self.note_write(Decision::Accumulator(key.clone()));
        self.accumulators.insert(key, accumulator);
        true
    }

    /// Whether an unconstrained `forall` with this key is specialized.
    pub fn is_rank_n(&self, key: &SchemeKey) -> bool {
        self.note_read(Decision::RankN(key.clone()));
        self.rank_n.contains_key(key)
    }

    /// Specializes the rank-N field type `key` of `owner`, a newtype or
    /// constructor, unless that owner's fields stay erased.
    pub fn add_rank_n(&mut self, key: SchemeKey, owner: String) {
        if !self.erased_owners.contains(&owner) && !self.erased_keys.contains(&key) {
            self.note_write(Decision::RankN(key.clone()));
            self.rank_n.insert(key, owner);
        }
    }

    /// Keeps the rank-N field type `key` erased: an erased owner holds it, and
    /// its values move by coercion between that owner and any other holding
    /// the same type (`Mapper VariantFCase` inside a `List`), which only a
    /// shared representation allows.
    pub fn erase_key(&mut self, key: SchemeKey) {
        self.note_write(Decision::RankN(key.clone()));
        self.note_write(Decision::ErasedKey(key.clone()));
        self.rank_n.remove(&key);
        self.erased_keys.insert(key);
    }

    pub fn is_erased_key(&self, key: &SchemeKey) -> bool {
        self.note_read(Decision::ErasedKey(key.clone()));
        self.erased_keys.contains(key)
    }

    /// Keeps every rank-N field of `owner` erased: some occurrence of it holds
    /// already-erased types (a VariantF's functor, say), and values move
    /// between its occurrences by coercion, which only a shared representation
    /// allows.
    pub fn erase_owner(&mut self, owner: String) {
        let owned = self.rank_n.iter().filter(|(_, existing)| **existing == owner);
        let owned: Vec<SchemeKey> = owned.map(|(key, _)| key.clone()).collect();
        owned.into_iter().for_each(|key| self.erase_key(key));
        self.note_write(Decision::ErasedOwner(owner.clone()));
        self.erased_owners.insert(owner);
    }

    pub fn is_erased_owner(&self, owner: &str) -> bool {
        self.note_read(Decision::ErasedOwner(owner.to_string()));
        self.erased_owners.contains(owner)
    }

    pub fn rank_n_owner(&self, key: &SchemeKey) -> Option<&str> {
        self.note_read(Decision::RankN(key.clone()));
        self.rank_n.get(key).map(String::as_str)
    }

    pub fn erase_growing_owner(&mut self, owner: String) {
        let grown = self.rank_n.iter().filter(|(_, existing)| **existing == owner);
        let grown: Vec<SchemeKey> = grown.map(|(key, _)| key.clone()).collect();
        for key in &grown {
            self.note_write(Decision::Grown(key.clone()));
        }
        self.note_write(Decision::AnyGrown);
        self.grown_keys.extend(grown);
        self.erase_owner(owner);
    }

    pub fn has_grown(&self) -> bool {
        self.note_read(Decision::AnyGrown);
        !self.grown_keys.is_empty()
    }

    pub fn rank_n_erasure(&self, key: &SchemeKey) -> Erasure {
        self.note_read(Decision::Grown(key.clone()));
        if self.grown_keys.contains(key) { Erasure::PolymorphicRecursion } else { Erasure::RankN }
    }

    pub fn insert(&mut self, key: SchemeKey, instantiation: SchemeInstantiation) {
        self.note_write(Decision::Instantiations(key.clone()));
        self.known.entry(key).or_default().push(instantiation);
    }

    pub fn link_coercion(&mut self, source: SchemeKey, target: SchemeKey) -> bool {
        let sources = self.coerced_sources.entry(target.clone()).or_default();
        if sources.contains(&source) {
            return false;
        }
        sources.push(source);
        self.note_write(Decision::Coerced(target));
        true
    }

    pub fn coerced_sources(&self, target: &SchemeKey) -> &[SchemeKey] {
        self.note_read(Decision::Coerced(target.clone()));
        self.coerced_sources.get(target).map_or(&[], Vec::as_slice)
    }

    pub fn witnesses(&self, family: TypeId) -> &[SchemeInstantiation] {
        self.note_read(Decision::Witnesses(family));
        self.families.get(&family).map_or(&[], |family| family.witnesses.as_slice())
    }

    pub fn continuations(&self, family: TypeId) -> &[SchemeKey] {
        self.note_read(Decision::Continuations(family));
        self.families.get(&family).map_or(&[], |family| family.continuations.as_slice())
    }

    pub fn note_variant_read(&self, row: TypeId) {
        self.note_read(Decision::VariantErasure(row));
    }

    pub fn erase_variant(&mut self, row: TypeId) {
        self.note_write(Decision::VariantErasure(row));
    }

    pub fn family_erasure(&self, family: TypeId) -> Option<Erasure> {
        self.note_read(Decision::FamilyErasure(family));
        self.erased_families.get(&family).copied()
    }

    pub fn continuation_family(&self, key: &SchemeKey) -> Option<TypeId> {
        self.note_read(Decision::ContinuationFamily(key.clone()));
        self.continuation_families.get(key).copied()
    }

    pub fn add_witness(&mut self, family: TypeId, witness: SchemeInstantiation) {
        if self.erased_families.contains_key(&family) {
            return;
        }
        self.note_write(Decision::Witnesses(family));
        self.families.entry(family).or_default().witnesses.push(witness);
    }

    pub fn add_continuation(&mut self, family: TypeId, key: SchemeKey) {
        if self.erased_families.contains_key(&family) {
            return;
        }
        self.note_write(Decision::RankN(key.clone()));
        self.note_write(Decision::ContinuationFamily(key.clone()));
        self.note_write(Decision::Continuations(family));
        self.rank_n.insert(key.clone(), format!("Data.Exists.runExists {family:?}"));
        self.continuation_families.insert(key.clone(), family);
        self.families.entry(family).or_default().continuations.push(key);
    }

    pub fn erase_family(&mut self, family: TypeId, erasure: Erasure) {
        if let Some(erased) = self.families.remove(&family) {
            self.note_write(Decision::Witnesses(family));
            self.note_write(Decision::Continuations(family));
            for key in erased.continuations {
                self.note_write(Decision::ContinuationFamily(key.clone()));
                self.note_write(Decision::Instantiations(key.clone()));
                self.continuation_families.remove(&key);
                self.known.remove(&key);
                self.erase_key(key);
            }
        }
        self.note_write(Decision::FamilyErasure(family));
        self.erased_families.entry(family).or_insert(erasure);
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

    /// The constraints an instantiation reifies at run time, instantiated: its field takes the
    /// value of each one's reflected type, the constraint's last argument, before its body.
    pub fn reified_constraints<Q>(
        &self,
        context: &Context<'_, Q>,
        instantiation: &SchemeInstantiation,
    ) -> Vec<TypeId>
    where
        Q: checking::ExternalQueries,
    {
        let substitution: Substitution =
            self.names.iter().copied().zip(instantiation.types.iter().copied()).collect();
        let reified = self.constraints.iter().zip(instantiation.dictionaries.iter());
        reified
            .filter(|(_, dictionary)| {
                matches!(dictionary, Dictionary::Reflectable(Reflected::Reified))
            })
            .map(|(&constraint, _)| context.types.substitute(constraint, &substitution))
            .collect()
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
        .map(|(position, &name)| (name, context.types.placeholder(position)))
        .collect();
    let canonical = constraints.iter().map(|&constraint| {
        let constraint = context.types.substitute(constraint, &placeholders);
        let constraint = context.types.without_causes(constraint);
        context.types.without_class_kinds(constraint)
    });
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
        .map(|(position, &name)| (name, context.types.placeholder(position)))
        .collect();
    // The key is the body in a canonical spelling, so that every occurrence of
    // the same rank-N type finds the same instantiations.
    let keyed = context.types.substitute(body, &placeholders);
    let keyed = crate::monotype::expand_synonyms(context, keyed)?;
    let keyed = context.types.without_causes(keyed);
    let key = SchemeKey(Arc::from([keyed]));
    Ok(Some(ConstrainedScheme { names, constraints: vec![], body, key }))
}
