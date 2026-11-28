use std::sync::Arc;

use building_types::QueryResult;
use checking::TypeId;
use checking::core::Type;
use files::FileId;
use indexing::{IndexedTypeItemKind, TypeItemId};

use super::NEWTYPE_EXPANSION_LIMIT;
use super::types::{expand_synonym, expand_synonyms, newtype_underlying};
use crate::context::Context;

/// The signedness a type of kind `Signedness` names, if it is `Signed` or `Unsigned`.
pub fn signedness<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
) -> QueryResult<Option<crate::primitives::Signedness>>
where
    Q: checking::ExternalQueries,
{
    use crate::primitives::{KnownType, Signedness};
    let type_id = expand_synonyms(context, type_id)?;
    let Type::Constructor(file_id, item) = context.types.lookup(type_id).clone() else {
        return Ok(None);
    };
    let module = context.module(file_id)?;
    let Some(name) = module.indexed.items[item].name.clone() else { return Ok(None) };
    Ok(match crate::primitives::known_type(&module.name, &name) {
        Some(KnownType::Signed) => Some(Signedness::Signed),
        Some(KnownType::Unsigned) => Some(Signedness::Unsigned),
        _ => None,
    })
}

/// The signednesses of the Longs a closed type mentions: through `Long' s`,
/// a bare `Long` and a `Signedness` itself, and inside newtypes such as `Int64`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LongMentions {
    pub signed: bool,
    pub unsigned: bool,
    pub bare: bool,
}

impl LongMentions {
    /// The one signedness the type names, unless it names both or neither.
    pub fn signedness(self) -> Option<crate::primitives::Signedness> {
        match (self.signed, self.unsigned) {
            (true, false) => Some(crate::primitives::Signedness::Signed),
            (false, true) => Some(crate::primitives::Signedness::Unsigned),
            _ => None,
        }
    }
}

pub fn long_mentions<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    mentions: &mut LongMentions,
) -> QueryResult<()>
where
    Q: checking::ExternalQueries,
{
    long_mentions_within(context, type_id, mentions, &mut vec![], 0)
}

fn long_mentions_within<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    mentions: &mut LongMentions,
    visited: &mut Vec<(FileId, TypeItemId)>,
    expansions: usize,
) -> QueryResult<()>
where
    Q: checking::ExternalQueries,
{
    use crate::primitives::KnownType;
    if expansions > NEWTYPE_EXPANSION_LIMIT {
        return Ok(());
    }
    let type_id = context.types.strip_annotations(type_id);
    match context.types.lookup(type_id).clone() {
        Type::Function(argument, result) => {
            long_mentions_within(context, argument, mentions, visited, expansions)?;
            return long_mentions_within(context, result, mentions, visited, expansions);
        }
        Type::Row(row) => {
            let row = context.queries.lookup_row_type(row).clone();
            for field in row.fields.iter() {
                long_mentions_within(context, field.id, mentions, visited, expansions)?;
            }
            return Ok(());
        }
        Type::Forall(_, inner) | Type::Constrained(_, inner) => {
            return long_mentions_within(context, inner, mentions, visited, expansions);
        }
        _ => {}
    }
    let (head, arguments) = context.types.spine(type_id);
    for &argument in &arguments {
        long_mentions_within(context, argument, mentions, visited, expansions)?;
    }
    let (file_id, item) = match context.types.lookup(head).clone() {
        Type::Constructor(file_id, item) => (file_id, item),
        Type::Synonym(file_id, item) => {
            return match expand_synonym(context, file_id, item, &arguments)? {
                Some(expanded) => {
                    long_mentions_within(context, expanded, mentions, visited, expansions + 1)
                }
                None => Ok(()),
            };
        }
        _ => return Ok(()),
    };
    let module = context.module(file_id)?;
    let Some(name) = module.indexed.items[item].name.clone() else { return Ok(()) };
    match crate::primitives::known_type(&module.name, &name) {
        Some(KnownType::Long) => mentions.bare = true,
        Some(KnownType::SignedLong) => {
            // The argument was visited above: Signed or Unsigned, or open.
        }
        Some(KnownType::Signed) => mentions.signed = true,
        Some(KnownType::Unsigned) => mentions.unsigned = true,
        _ => {
            let kind = &module.indexed.items[item].kind;
            let IndexedTypeItemKind::Newtype { constructors, .. } = kind else { return Ok(()) };
            let Some(&constructor) = constructors.first() else { return Ok(()) };
            if visited.contains(&(file_id, item)) {
                return Ok(());
            }
            let Some(underlying) = newtype_underlying(context, file_id, constructor, type_id)?
            else {
                return Ok(());
            };
            visited.push((file_id, item));
            long_mentions_within(context, underlying, mentions, visited, expansions + 1)?;
            visited.pop();
        }
    }
    Ok(())
}

/// The type with every bare `Long` spelled `Long' signedness`: the Longs of a
/// definition whose types name one signedness have it.
pub fn spell_longs<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    signed_long: TypeId,
    long: (FileId, TypeItemId),
) -> TypeId
where
    Q: checking::ExternalQueries,
{
    let stripped = context.types.strip_annotations(type_id);
    let (head, _) = context.types.spine(stripped);
    if let Type::Synonym(..) = context.types.lookup(head) {
        let Ok(expanded) = expand_synonyms(context, stripped) else { return type_id };
        if expanded == stripped {
            return type_id;
        }
        return spell_longs(context, expanded, signed_long, long);
    }
    let rebuilt = match context.types.lookup(stripped).clone() {
        Type::Constructor(file_id, item) if (file_id, item) == long => return signed_long,
        Type::Application(function, argument) => {
            let spelled_function = spell_longs(context, function, signed_long, long);
            let spelled_argument = spell_longs(context, argument, signed_long, long);
            if spelled_function == function && spelled_argument == argument {
                return type_id;
            }
            Type::Application(spelled_function, spelled_argument)
        }
        Type::Function(argument, result) => {
            let spelled_argument = spell_longs(context, argument, signed_long, long);
            let spelled_result = spell_longs(context, result, signed_long, long);
            if spelled_argument == argument && spelled_result == result {
                return type_id;
            }
            Type::Function(spelled_argument, spelled_result)
        }
        Type::Forall(binder, inner) => {
            let spelled = spell_longs(context, inner, signed_long, long);
            if spelled == inner {
                return type_id;
            }
            Type::Forall(binder, spelled)
        }
        Type::Constrained(constraint, inner) => {
            let spelled_constraint = spell_longs(context, constraint, signed_long, long);
            let spelled_inner = spell_longs(context, inner, signed_long, long);
            if spelled_constraint == constraint && spelled_inner == inner {
                return type_id;
            }
            Type::Constrained(spelled_constraint, spelled_inner)
        }
        Type::Row(row) => {
            let row = context.queries.lookup_row_type(row).clone();
            let mut changed = false;
            let mut fields = Vec::with_capacity(row.fields.len());
            for field in row.fields.iter() {
                let id = spell_longs(context, field.id, signed_long, long);
                changed |= id != field.id;
                fields.push(checking::core::RowField { label: field.label.clone(), id });
            }
            let tail = row.tail.map(|tail| spell_longs(context, tail, signed_long, long));
            if !changed && tail == row.tail {
                return type_id;
            }
            let row = checking::core::RowType { fields: Arc::from(fields), tail };
            Type::Row(context.queries.intern_row_type(row))
        }
        _ => return type_id,
    };
    context.queries.intern_type(rebuilt)
}
