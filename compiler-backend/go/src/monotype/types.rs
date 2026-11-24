use std::sync::Arc;

use building_types::QueryResult;
use checking::TypeId;
use checking::core::{Name, Type};
use files::FileId;
use indexing::{IndexedTypeItemKind, TermItemId, TypeItemId};

use super::{Failure, NEWTYPE_EXPANSION_LIMIT};
use crate::context::Context;
use crate::erasure::Erasure;
use crate::error::UnsupportedState;
use crate::types::Substitution;

const EQUALITY_UNWRAP_LIMIT: usize = 8;

/// Whether a type is an equality proof between apart types: after unwrapping
/// newtypes (`Leibniz a b`), `forall f. f a -> f b` where `a` and `b` are
/// closed and clash. No value has that type: `Data.Leibniz.refute` turns one
/// into a `Void` by choosing `f` to map `a` to `Unit` and `b` to `Void`.
pub(super) fn is_refuted_equality<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
) -> QueryResult<bool>
where
    Q: checking::ExternalQueries,
{
    let mut current = expand_synonyms(context, type_id)?;
    for _ in 0..EQUALITY_UNWRAP_LIMIT {
        let (head, _) = context.types.spine(current);
        let Type::Constructor(file_id, item) = context.types.lookup(head).clone() else { break };
        let module = context.module(file_id)?;
        let IndexedTypeItemKind::Newtype { constructors, .. } = &module.indexed.items[item].kind
        else {
            return Ok(false);
        };
        let Some(&constructor) = constructors.first() else { return Ok(false) };
        let Some(underlying) = newtype_underlying(context, file_id, constructor, current)? else {
            return Ok(false);
        };
        current = expand_synonyms(context, underlying)?;
    }
    let (names, body) = context.types.peel_quantifiers(current);
    let Some((argument, result)) = context.types.function_parts(body) else { return Ok(false) };
    let (argument_head, argument_arguments) = context.types.spine(argument);
    let (result_head, result_arguments) = context.types.spine(result);
    let (Type::Rigid(argument_variable, ..), Type::Rigid(result_variable, ..)) =
        (context.types.lookup(argument_head), context.types.lookup(result_head))
    else {
        return Ok(false);
    };
    let ([left], [right]) = (&argument_arguments[..], &result_arguments[..]) else {
        return Ok(false);
    };
    if argument_variable != result_variable || !names.contains(argument_variable) {
        return Ok(false);
    }
    // Data types share one representation for arguments that differ only by
    // newtypes, so equalities are refuted only between representations.
    let left = erase_newtypes(context, *left, 0, &mut vec![])?;
    let right = erase_newtypes(context, *right, 0, &mut vec![])?;
    Ok(apart(context, left, right))
}

/// Whether two types certainly differ: some position holds distinct type
/// constructors or literals. Anything not closed is never apart.
fn apart<Q>(context: &mut Context<'_, Q>, left: TypeId, right: TypeId) -> bool
where
    Q: checking::ExternalQueries,
{
    if let (Some((left_argument, left_result)), Some((right_argument, right_result))) =
        (context.types.function_parts(left), context.types.function_parts(right))
    {
        return apart(context, left_argument, right_argument)
            || apart(context, left_result, right_result);
    }
    let (left_head, left_arguments) = context.types.spine(left);
    let (right_head, right_arguments) = context.types.spine(right);
    match (context.types.lookup(left_head), context.types.lookup(right_head)) {
        (Type::Constructor(left_file, left_item), Type::Constructor(right_file, right_item)) => {
            if (left_file, left_item) != (right_file, right_item) {
                return true;
            }
            left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments.iter())
                    .any(|(&left, &right)| apart(context, left, right))
        }
        (Type::Integer(left), Type::Integer(right)) => left != right,
        (Type::String(_, left), Type::String(_, right)) => left != right,
        _ => false,
    }
}

/// Newtypes have the runtime representation of their underlying type, and synonyms
/// are only names, so two data types whose arguments differ only by either share one
/// Go type.
pub(super) fn erase_newtypes<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    expansions: usize,
    expanding: &mut Vec<TypeId>,
) -> QueryResult<TypeId>
where
    Q: checking::ExternalQueries,
{
    canonicalise(context, type_id, expansions, expanding, true)
}

pub(super) fn closed_row<Q>(
    context: &mut Context<'_, Q>,
    row: TypeId,
) -> QueryResult<Option<TypeId>>
where
    Q: checking::ExternalQueries,
{
    let row = context.types.strip_annotations(row);
    let row = match context.types.lookup(row) {
        Type::Row(row_id) if context.queries.lookup_row_type(*row_id).tail.is_none() => row,
        _ => expand_synonyms(context, row)?,
    };
    let Type::Row(row_id) = context.types.lookup(row).clone() else { return Ok(None) };
    let row_type = context.queries.lookup_row_type(row_id).clone();
    let closed = row_type.tail.is_none()
        && row_type.fields.iter().all(|field| !mentions_open_variable(context, field.id));
    if !closed {
        return Ok(None);
    }
    let canonical = erase_newtypes(context, row, 0, &mut vec![])?;
    match context.types.lookup(canonical) {
        Type::Row(_) => Ok(Some(canonical)),
        _ => Ok(None),
    }
}

fn mentions_open_variable<Q>(context: &Context<'_, Q>, type_id: TypeId) -> bool
where
    Q: checking::ExternalQueries,
{
    let type_id = context.types.strip_annotations(type_id);
    match context.types.lookup(type_id).clone() {
        Type::Free(_) | Type::Unknown(_) => true,
        Type::Application(function, argument) | Type::Function(function, argument) => {
            mentions_open_variable(context, function) || mentions_open_variable(context, argument)
        }
        Type::Forall(..) | Type::Constrained(..) => {
            let (_, inner) = context.types.peel_quantifiers(type_id);
            inner != type_id && mentions_open_variable(context, inner)
        }
        Type::Row(row) => {
            let row = context.queries.lookup_row_type(row).clone();
            row.fields.iter().any(|field| mentions_open_variable(context, field.id))
                || row.tail.is_some_and(|tail| mentions_open_variable(context, tail))
        }
        _ => false,
    }
}

pub fn data_argument<Q>(context: &mut Context<'_, Q>, type_id: TypeId) -> QueryResult<TypeId>
where
    Q: checking::ExternalQueries,
{
    erase_newtypes(context, type_id, 0, &mut vec![])
}

/// Expands every synonym in a closed type, so that instance heads match it
/// structurally.
pub fn expand_synonyms<Q>(context: &mut Context<'_, Q>, type_id: TypeId) -> QueryResult<TypeId>
where
    Q: checking::ExternalQueries,
{
    canonicalise(context, type_id, 0, &mut vec![], false)
}

fn canonicalise<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    expansions: usize,
    expanding: &mut Vec<TypeId>,
    erase: bool,
) -> QueryResult<TypeId>
where
    Q: checking::ExternalQueries,
{
    // Below a newtype expansion the result depends on the expansions above it,
    // so only outermost results are remembered.
    if expansions > 0 || !expanding.is_empty() {
        return canonicalise_uncached(context, type_id, expansions, expanding, erase);
    }
    if let Some(&canonical) = context.canonical.get(&(type_id, erase)) {
        return Ok(canonical);
    }
    let canonical = canonicalise_uncached(context, type_id, expansions, expanding, erase)?;
    context.canonical.insert((type_id, erase), canonical);
    Ok(canonical)
}

/// Whether a closed row's fields came back from canonicalisation as they were,
/// already in label order, so that rebuilding the row would intern it again.
fn is_canonical_already(
    row: &checking::core::RowType,
    fields: &[checking::core::RowField],
) -> bool {
    row.fields.iter().zip(fields).all(|(before, after)| before.id == after.id)
        && fields.windows(2).all(|pair| pair[0].label <= pair[1].label)
}

fn canonicalise_uncached<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    expansions: usize,
    expanding: &mut Vec<TypeId>,
    erase: bool,
) -> QueryResult<TypeId>
where
    Q: checking::ExternalQueries,
{
    if expansions > NEWTYPE_EXPANSION_LIMIT {
        return Ok(type_id);
    }
    let type_id = context.types.strip_annotations(type_id);
    match context.types.lookup(type_id).clone() {
        Type::Function(argument, result) => {
            let canonical_argument = canonicalise(context, argument, expansions, expanding, erase)?;
            let canonical_result = canonicalise(context, result, expansions, expanding, erase)?;
            if canonical_argument == argument && canonical_result == result {
                return Ok(type_id);
            }
            let function = Type::Function(canonical_argument, canonical_result);
            return Ok(context.queries.intern_type(function));
        }
        Type::Row(row) => {
            let row = context.queries.lookup_row_type(row).clone();
            let mut fields = Vec::with_capacity(row.fields.len());
            for field in row.fields.iter() {
                let id = canonicalise(context, field.id, expansions, expanding, erase)?;
                fields.push(checking::core::RowField { label: field.label.clone(), id });
            }
            if row.tail.is_none() && is_canonical_already(&row, &fields) {
                return Ok(type_id);
            }
            // A tail such as `RENDER ()` in `METRICS + RENDER + ()` is a synonym
            // for more fields: expand it and flatten, so that every spelling of a
            // closed row has one canonical form.
            let mut tail = row.tail;
            while let Some(current) = tail {
                let expanded = canonicalise(context, current, expansions, expanding, erase)?;
                let Type::Row(inner) = context.types.lookup(expanded).clone() else {
                    tail = Some(expanded);
                    break;
                };
                let inner = context.queries.lookup_row_type(inner).clone();
                fields.extend(inner.fields.iter().cloned());
                tail = inner.tail;
            }
            fields.sort_by(|left, right| left.label.cmp(&right.label));
            let row = checking::core::RowType { fields: Arc::from(fields), tail };
            let row = context.queries.intern_row_type(row);
            return Ok(context.queries.intern_type(Type::Row(row)));
        }
        _ => {}
    }
    let (head, arguments) = context.types.spine(type_id);
    match context.types.lookup(head).clone() {
        Type::Rigid(..) | Type::Unification(_) if erase && arguments.is_empty() => {
            if context.types.erasure(head).is_some() {
                return Ok(head);
            }
            Ok(context.types.erased(Erasure::ArgumentVariable))
        }
        Type::Constructor(file_id, item) => {
            let module = context.module(file_id)?;
            // `Long' Signed` and `Long' Unsigned` are two Go types, where the
            // Long they wrap would be one.
            let signed_long = module.indexed.items[item].name.as_deref().is_some_and(|name| {
                crate::primitives::known_type(&module.name, name)
                    == Some(crate::primitives::KnownType::SignedLong)
            });
            if erase
                && !signed_long
                && !is_recursive_newtype(context, file_id, item)?
                && let IndexedTypeItemKind::Newtype { constructors, .. } =
                    &module.indexed.items[item].kind
                && let Some(&constructor) = constructors.first()
                && let Some(underlying) =
                    newtype_underlying(context, file_id, constructor, type_id)?
            {
                if expanding.contains(&type_id) {
                    return Ok(context.types.erased(Erasure::NewtypeCycle));
                }
                expanding.push(type_id);
                let erased = canonicalise(context, underlying, expansions + 1, expanding, erase)?;
                expanding.pop();
                let erased_newtype = crate::context::ErasedNewtype {
                    file_id,
                    item,
                    arguments: Arc::from(arguments),
                    erased,
                };
                if !context.erased_newtypes.contains(&erased_newtype) {
                    context.erased_newtypes.push(erased_newtype);
                }
                return Ok(erased);
            }
            let typed_variant = module.name == "Data.Variant"
                && matches!(arguments[..], [row] if closed_row(context, row)?
                    .is_some_and(|row| !context.erased_variant_rows.contains(&row)));
            if erase
                && !arguments.is_empty()
                && !typed_variant
                && ignores_arguments(&module.name, module.indexed.items[item].name.as_deref())
            {
                let empty = checking::core::RowType { fields: Arc::from([]), tail: None };
                let empty = context.queries.intern_row_type(empty);
                let empty = context.queries.intern_type(Type::Row(empty));
                let mut rebuilt = head;
                for _ in arguments {
                    rebuilt = context.queries.intern_type(Type::Application(rebuilt, empty));
                }
                return Ok(rebuilt);
            }
            if module.name == "Prim"
                && module.indexed.items[item].name.as_deref() == Some("Function")
                && let [argument, result] = arguments[..]
            {
                let function = context.queries.intern_type(Type::Function(argument, result));
                return canonicalise(context, function, expansions, expanding, erase);
            }
            if arguments.is_empty() {
                return Ok(type_id);
            }
            let mut rebuilt = head;
            for argument in arguments {
                let argument = canonicalise(context, argument, expansions, expanding, erase)?;
                rebuilt = context.queries.intern_type(Type::Application(rebuilt, argument));
            }
            Ok(rebuilt)
        }
        Type::Synonym(file_id, item) => match expand_synonym(context, file_id, item, &arguments)? {
            Some(expanded) => canonicalise(context, expanded, expansions + 1, expanding, erase),
            None => Ok(type_id),
        },
        _ => Ok(type_id),
    }
}

fn ignores_arguments(module: &str, name: Option<&str>) -> bool {
    matches!(
        (module, name),
        ("Data.Variant", Some("Variant")) | ("Data.Functor.Variant", Some("VariantF"))
    )
}

pub(super) fn regular_occurrences<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    file_id: FileId,
    item: TypeItemId,
    parameters: &[TypeId],
) -> bool
where
    Q: checking::ExternalQueries,
{
    let type_id = context.types.strip_annotations(type_id);
    let (head, arguments) = context.types.spine(type_id);
    if !arguments.is_empty() {
        if let Type::Constructor(head_file, head_item) = *context.types.lookup(head)
            && head_file == file_id
            && head_item == item
        {
            let same = arguments.len() == parameters.len()
                && arguments.iter().zip(parameters).all(|(&argument, &parameter)| {
                    context.types.strip_annotations(argument) == parameter
                });
            if !same {
                return false;
            }
        }
        return arguments
            .iter()
            .all(|&argument| regular_occurrences(context, argument, file_id, item, parameters));
    }
    match context.types.lookup(type_id).clone() {
        Type::Function(argument, result) => {
            regular_occurrences(context, argument, file_id, item, parameters)
                && regular_occurrences(context, result, file_id, item, parameters)
        }
        Type::Row(row) => {
            let row = context.queries.lookup_row_type(row).clone();
            row.fields
                .iter()
                .all(|field| regular_occurrences(context, field.id, file_id, item, parameters))
        }
        _ => true,
    }
}

pub fn is_recursive_newtype<Q>(
    context: &mut Context<'_, Q>,
    file_id: FileId,
    item: TypeItemId,
) -> QueryResult<bool>
where
    Q: checking::ExternalQueries,
{
    if let Some(&recursive) = context.recursive_newtypes.get(&(file_id, item)) {
        return Ok(recursive);
    }
    let mut visited = vec![(file_id, item)];
    let recursive = match declared_underlying(context, file_id, item)? {
        Some(underlying) => mentions_type(context, underlying, (file_id, item), &mut visited, 0)?,
        None => false,
    };
    context.recursive_newtypes.insert((file_id, item), recursive);
    Ok(recursive)
}

fn declared_underlying<Q>(
    context: &mut Context<'_, Q>,
    file_id: FileId,
    item: TypeItemId,
) -> QueryResult<Option<TypeId>>
where
    Q: checking::ExternalQueries,
{
    let module = context.module(file_id)?;
    let IndexedTypeItemKind::Newtype { constructors, .. } = &module.indexed.items[item].kind else {
        return Ok(None);
    };
    let Some(signature) = constructors
        .first()
        .and_then(|&constructor| module.checked.lookup_term_item_type(constructor))
    else {
        return Ok(None);
    };
    let (_, body) = context.types.peel_quantifiers(signature);
    Ok(context.types.function_parts(body).map(|(underlying, _)| underlying))
}

fn mentions_type<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    target: (FileId, TypeItemId),
    visited: &mut Vec<(FileId, TypeItemId)>,
    expansions: usize,
) -> QueryResult<bool>
where
    Q: checking::ExternalQueries,
{
    if expansions > NEWTYPE_EXPANSION_LIMIT {
        return Ok(false);
    }
    let type_id = context.types.strip_annotations(type_id);
    match context.types.lookup(type_id).clone() {
        Type::Function(argument, result) => {
            return Ok(mentions_type(context, argument, target, visited, expansions)?
                || mentions_type(context, result, target, visited, expansions)?);
        }
        Type::Row(row) => {
            let row = context.queries.lookup_row_type(row).clone();
            for field in row.fields.iter() {
                if mentions_type(context, field.id, target, visited, expansions)? {
                    return Ok(true);
                }
            }
            return Ok(false);
        }
        Type::Forall(_, inner) | Type::Constrained(_, inner) => {
            return mentions_type(context, inner, target, visited, expansions);
        }
        _ => {}
    }
    let (head, arguments) = context.types.spine(type_id);
    for &argument in &arguments {
        if mentions_type(context, argument, target, visited, expansions)? {
            return Ok(true);
        }
    }
    match context.types.lookup(head).clone() {
        Type::Constructor(file_id, item) => {
            if (file_id, item) == target {
                return Ok(true);
            }
            if visited.contains(&(file_id, item)) {
                return Ok(false);
            }
            visited.push((file_id, item));
            match declared_underlying(context, file_id, item)? {
                Some(underlying) => {
                    mentions_type(context, underlying, target, visited, expansions + 1)
                }
                None => Ok(false),
            }
        }
        Type::Synonym(file_id, item) => {
            let expanded = match expand_synonym(context, file_id, item, &arguments)? {
                Some(expanded) => expanded,
                None => {
                    let module = context.module(file_id)?;
                    match module.checked.lookup_synonym(item) {
                        Some(synonym) => synonym.expansion,
                        None => return Ok(false),
                    }
                }
            };
            mentions_type(context, expanded, target, visited, expansions + 1)
        }
        _ => Ok(false),
    }
}

pub fn is_partial<Q>(context: &mut Context<'_, Q>, constraint: TypeId) -> QueryResult<bool>
where
    Q: checking::ExternalQueries,
{
    let (head, _) = context.types.spine(constraint);
    let Type::Constructor(file_id, item) = *context.types.lookup(head) else {
        return Ok(false);
    };
    context.is_type(file_id, item, "Prim", "Partial")
}

pub(super) fn newtype_underlying<Q>(
    context: &mut Context<'_, Q>,
    file_id: FileId,
    constructor: TermItemId,
    applied: TypeId,
) -> QueryResult<Option<TypeId>>
where
    Q: checking::ExternalQueries,
{
    let module = context.module(file_id)?;
    let Some(signature) = module.checked.lookup_term_item_type(constructor) else {
        return Ok(None);
    };
    let (variables, body) = context.types.peel_quantifiers(signature);
    let Some((underlying, result)) = context.types.function_parts(body) else {
        return Ok(None);
    };
    let mut bindings = Substitution::default();
    if !context.types.match_type(result, applied, &variables, &mut bindings) {
        return Ok(None);
    }
    Ok(Some(context.types.substitute(underlying, &bindings)))
}

/// The type a non-recursive newtype wraps, its arguments substituted: `Effect a` for an
/// `IO a` whose `newtype IO a = IO (Effect a)`. None for any other type.
pub fn newtype_unwrapped<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
) -> QueryResult<Option<TypeId>>
where
    Q: checking::ExternalQueries,
{
    let type_id = context.types.strip_annotations(type_id);
    let (head, _) = context.types.spine(type_id);
    let Type::Constructor(file_id, item) = *context.types.lookup(head) else { return Ok(None) };
    if is_recursive_newtype(context, file_id, item)? {
        return Ok(None);
    }
    let module = context.module(file_id)?;
    let IndexedTypeItemKind::Newtype { constructors, .. } = &module.indexed.items[item].kind else {
        return Ok(None);
    };
    let Some(&constructor) = constructors.first() else { return Ok(None) };
    newtype_underlying(context, file_id, constructor, type_id)
}

pub fn expand_synonym<Q>(
    context: &mut Context<'_, Q>,
    file_id: FileId,
    item: TypeItemId,
    arguments: &[TypeId],
) -> QueryResult<Option<TypeId>>
where
    Q: checking::ExternalQueries,
{
    let module = context.module(file_id)?;
    let Some(synonym) = module.checked.lookup_synonym(item) else {
        return Ok(None);
    };
    if arguments.len() < synonym.parameters.len() {
        return Ok(None);
    }
    let names: Vec<Name> = synonym.parameters.iter().map(|binder| binder.name).collect();
    let substitution: Substitution = names.iter().copied().zip(arguments.iter().copied()).collect();
    let mut expanded = context.types.substitute(synonym.expansion, &substitution);
    for &argument in &arguments[synonym.parameters.len()..] {
        expanded = context.queries.intern_type(Type::Application(expanded, argument));
    }
    Ok(Some(expanded))
}

pub(super) fn erased_newtypes<Q>(
    context: &mut Context<'_, Q>,
    arguments: impl IntoIterator<Item = TypeId>,
    expansions: usize,
) -> QueryResult<Arc<[TypeId]>>
where
    Q: checking::ExternalQueries,
{
    arguments
        .into_iter()
        .map(|argument| erase_newtypes(context, argument, expansions, &mut vec![]))
        .collect()
}

pub(super) fn open_type<Q>(context: &mut Context<'_, Q>, type_id: TypeId) -> QueryResult<Failure>
where
    Q: checking::ExternalQueries,
{
    let prim = context.module(context.queries.prim_id())?;
    let pretty = checking::core::pretty::Pretty::new(context.queries, &prim.checked);
    let rendered = pretty.render(type_id)?.to_string();
    Ok(UnsupportedState::OpenType { rendered }.into())
}
