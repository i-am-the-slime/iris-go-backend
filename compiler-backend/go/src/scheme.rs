use std::sync::Arc;

use building_types::QueryResult;
use checking::TypeId;
use checking::core::{Depth, Name, Type};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::context::Context;
use crate::dictionary::Dictionary;
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
}

impl SchemeInstantiations {
    pub fn get(&self, key: &SchemeKey) -> &[SchemeInstantiation] {
        self.known.get(key).map_or(&[], Vec::as_slice)
    }

    pub fn find(&self, key: &SchemeKey, types: &[TypeId]) -> Option<&SchemeInstantiation> {
        self.get(key).iter().find(|instantiation| *instantiation.types == *types)
    }

    pub fn insert(&mut self, key: SchemeKey, instantiation: SchemeInstantiation) {
        self.known.entry(key).or_default().push(instantiation);
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

fn placeholder<Q>(context: &Context<'_, Q>, position: usize) -> TypeId
where
    Q: checking::ExternalQueries,
{
    let unique = u32::MAX - 1 - position as u32;
    let name = Name { file: context.queries.prim_id(), unique, scoped: false };
    let kind = context.queries.intern_type(Type::Unification(u32::MAX));
    context.queries.intern_type(Type::Rigid(name, Depth(0), kind))
}
