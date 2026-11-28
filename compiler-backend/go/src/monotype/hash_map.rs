use std::sync::Arc;

use building_types::QueryResult;
use checking::TypeId;
use checking::core::Type;
use files::FileId;
use indexing::TypeItemId;

use super::types::{erase_newtypes, expand_synonyms};
use super::{Converted, DataType, Monotype, Monotypes};
use crate::context::Context;
use crate::error::UnsupportedState;

impl Monotypes {
    pub(super) fn hash_map<Q>(
        context: &mut Context<'_, Q>,
        (file_id, item): (FileId, TypeItemId),
        arguments: &[TypeId],
        expansions: usize,
    ) -> Converted<Monotype>
    where
        Q: checking::ExternalQueries,
    {
        let [key, value] = arguments[..] else {
            let name = "HashMap".into();
            return Err(UnsupportedState::UnsaturatedType { name }.into());
        };
        let spelled = expand_synonyms(context, key)?;
        let erased = erase_newtypes(context, key, expansions, &mut vec![])?;
        let key = match is_native_key(context, erased)? && !is_native_key(context, spelled)? {
            true => spelled,
            false => erased,
        };
        let value = erase_newtypes(context, value, expansions, &mut vec![])?;
        let arguments = Arc::from([key, value]);
        Ok(Monotype::ForeignData(DataType { file_id, item, arguments }))
    }
}

pub fn native_hash_map<Q>(
    context: &mut Context<'_, Q>,
    data: &DataType,
) -> QueryResult<Option<bool>>
where
    Q: checking::ExternalQueries,
{
    let module = context.module(data.file_id)?;
    let name = context.type_name(data.file_id, data.item)?;
    if (module.name.as_str(), name.as_str()) != ("Data.HashMap", "HashMap") {
        return Ok(None);
    }
    let Some(&key) = data.arguments.first() else { return Ok(Some(false)) };
    Ok(Some(is_native_key(context, key)?))
}

fn is_native_key<Q>(context: &mut Context<'_, Q>, key: TypeId) -> QueryResult<bool>
where
    Q: checking::ExternalQueries,
{
    let key = context.types.strip_annotations(key);
    let Type::Constructor(file_id, item) = context.types.lookup(key).clone() else {
        return Ok(false);
    };
    if file_id != context.queries.prim_id() {
        return Ok(false);
    }
    let name = context.type_name(file_id, item)?;
    Ok(matches!(name.as_str(), "Int" | "Char" | "String"))
}
