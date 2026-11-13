use std::sync::Arc;

use building_types::QueryResult;
use checking::TypeId;
use checking::core::{Name, Type};
use files::FileId;
use indexing::{IndexedTypeItemKind, TermItemId, TypeItemId};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::context::Context;
use crate::error::UnsupportedState;
use crate::types::Substitution;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MonotypeId(u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Monotype {
    Int,
    Number,
    Boolean,
    Char,
    String,
    Unit,
    Array(MonotypeId),
    Record(Arc<[RecordField]>),
    Function(MonotypeId, MonotypeId),
    Effect(MonotypeId),
    Reference(MonotypeId),
    Data(DataType),
    Erased,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordField {
    pub label: SmolStr,
    pub monotype: MonotypeId,
}

/// A data type applied to closed type arguments. Arguments stay checker types rather
/// than monotypes because they may be higher-kinded, as in `Free f a`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DataType {
    pub file_id: FileId,
    pub item: TypeItemId,
    pub arguments: Arc<[TypeId]>,
}

#[derive(Debug, Clone)]
pub struct DataConstructor {
    pub term: TermItemId,
    pub name: SmolStr,
    pub fields: Vec<MonotypeId>,
}

const NEWTYPE_EXPANSION_LIMIT: usize = 64;

#[derive(Default)]
pub struct Monotypes {
    interned: Vec<Monotype>,
    lookup: FxHashMap<Monotype, MonotypeId>,
    converted: FxHashMap<TypeId, MonotypeId>,
    constructors: FxHashMap<DataType, Arc<[DataConstructor]>>,
    regular: FxHashMap<(FileId, TypeItemId), bool>,
    expanding: Vec<(FileId, TypeItemId)>,
}

impl Monotypes {
    pub fn intern(&mut self, monotype: Monotype) -> MonotypeId {
        if let Some(&id) = self.lookup.get(&monotype) {
            return id;
        }
        let id = MonotypeId(self.interned.len() as u32);
        self.interned.push(monotype.clone());
        self.lookup.insert(monotype, id);
        id
    }

    pub fn get(&self, id: MonotypeId) -> &Monotype {
        &self.interned[id.0 as usize]
    }

    pub fn unit(&mut self) -> MonotypeId {
        self.intern(Monotype::Unit)
    }

    pub fn function(&mut self, argument: MonotypeId, result: MonotypeId) -> MonotypeId {
        self.intern(Monotype::Function(argument, result))
    }

    pub fn function_parts(&self, id: MonotypeId) -> Option<(MonotypeId, MonotypeId)> {
        match self.get(id) {
            Monotype::Function(argument, result) => Some((*argument, *result)),
            _ => None,
        }
    }

    pub fn effect_result(&self, id: MonotypeId) -> Option<MonotypeId> {
        match self.get(id) {
            Monotype::Effect(result) => Some(*result),
            _ => None,
        }
    }

    /// Strips `count` arguments off a curried function type.
    pub fn result_after(&self, mut id: MonotypeId, count: usize) -> MonotypeId {
        for _ in 0..count {
            match self.function_parts(id) {
                Some((_, result)) => id = result,
                None => break,
            }
        }
        id
    }

    pub fn monotype<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(&id) = self.converted.get(&type_id) {
            return Ok(Ok(id));
        }
        let converted = self.convert(context, type_id, 0)?;
        if let Ok(id) = converted {
            self.converted.insert(type_id, id);
        }
        Ok(converted)
    }

    fn convert<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
        expansions: usize,
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        if expansions > NEWTYPE_EXPANSION_LIMIT {
            return Ok(Err(UnsupportedState::Construct {
                construct: "infinitely nested newtypes",
            }));
        }
        let type_id = context.types.strip_annotations(type_id);
        let monotype = match context.types.lookup(type_id).clone() {
            Type::Function(argument, result) => {
                let argument = match self.convert(context, argument, expansions)? {
                    Ok(argument) => argument,
                    Err(error) => return Ok(Err(error)),
                };
                let result = match self.convert(context, result, expansions)? {
                    Ok(result) => result,
                    Err(error) => return Ok(Err(error)),
                };
                Monotype::Function(argument, result)
            }
            Type::Forall(_, inner) => return self.convert(context, inner, expansions),
            Type::Rigid(..) => Monotype::Erased,
            Type::Unification(_) => Monotype::Unit,
            Type::Application(..) | Type::Constructor(..) | Type::Synonym(..) => {
                return self.convert_application(context, type_id, expansions);
            }
            Type::Constrained(constraint, inner) => {
                if is_partial(context, constraint)? {
                    return self.convert(context, inner, expansions);
                }
                return Ok(Err(UnsupportedState::Construct {
                    construct: "constrained types in argument positions",
                }));
            }
            Type::Row(_) | Type::Integer(_) | Type::String(..) => {
                return Ok(Err(self.open_type(type_id)));
            }
            Type::Free(_) | Type::Unknown(_) => return Ok(Err(self.open_type(type_id))),
            Type::Kinded(..) | Type::KindApplication(..) | Type::ConstraintOrigin(..) => {
                unreachable!("invariant violated: annotations are stripped before conversion")
            }
        };
        Ok(Ok(self.intern(monotype)))
    }

    fn open_type(&self, type_id: TypeId) -> UnsupportedState {
        UnsupportedState::OpenType { rendered: format!("{type_id:?}") }
    }

    fn convert_application<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
        expansions: usize,
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        let (head, arguments) = context.types.spine(type_id);
        let (file_id, item) = match context.types.lookup(head).clone() {
            Type::Constructor(file_id, item) => (file_id, item),
            Type::Synonym(file_id, item) => {
                return match expand_synonym(context, file_id, item, &arguments)? {
                    Some(expanded) => self.convert(context, expanded, expansions + 1),
                    None => Ok(Err(UnsupportedState::UnsaturatedType {
                        name: context.type_name(file_id, item)?.to_string(),
                    })),
                };
            }
            Type::Rigid(..) => return Ok(Ok(self.intern(Monotype::Erased))),
            Type::Function(..) if arguments.is_empty() => {
                return self.convert(context, head, expansions);
            }
            _ => return Ok(Err(self.open_type(type_id))),
        };

        let module = context.module(file_id)?;
        let name = module.indexed.items[item].name.clone().unwrap_or_default();
        let unary = |monotypes: &mut Monotypes,
                     context: &mut Context<'_, Q>,
                     argument: Option<&TypeId>|
         -> QueryResult<Result<MonotypeId, UnsupportedState>> {
            match argument {
                Some(&argument) => monotypes.convert(context, argument, expansions),
                None => Ok(Err(UnsupportedState::UnsaturatedType { name: name.to_string() })),
            }
        };

        let monotype = match (module.name.as_str(), name.as_str()) {
            ("Prim", "Int") => Monotype::Int,
            ("Prim", "Number") => Monotype::Number,
            ("Prim", "Boolean") => Monotype::Boolean,
            ("Prim", "Char") => Monotype::Char,
            ("Prim", "String") => Monotype::String,
            ("Prim", "Array") => match unary(self, context, arguments.first())? {
                Ok(element) => Monotype::Array(element),
                Err(error) => return Ok(Err(error)),
            },
            ("Prim", "Function") => {
                let [argument, result] = arguments[..] else {
                    return Ok(Err(UnsupportedState::UnsaturatedType { name: name.to_string() }));
                };
                let function = context.queries.intern_type(Type::Function(argument, result));
                return self.convert(context, function, expansions);
            }
            ("Prim", "Record") => {
                let Some(&row) = arguments.first() else {
                    return Ok(Err(UnsupportedState::UnsaturatedType { name: name.to_string() }));
                };
                return self.convert_record(context, row, expansions);
            }
            ("Data.Unit", "Unit") => Monotype::Unit,
            ("Data.Function.Uncurried", name) if name.starts_with("Fn") => {
                let Some((&result, parameters)) = arguments.split_last() else {
                    return Ok(Err(UnsupportedState::UnsaturatedType { name: name.to_string() }));
                };
                let mut curried = result;
                for &parameter in parameters.iter().rev() {
                    curried = context.queries.intern_type(Type::Function(parameter, curried));
                }
                if parameters.is_empty() {
                    let unit = context.queries.intern_type(Type::Unification(u32::MAX));
                    curried = context.queries.intern_type(Type::Function(unit, curried));
                }
                return self.convert(context, curried, expansions);
            }
            ("Effect", "Effect") => match unary(self, context, arguments.first())? {
                Ok(result) => Monotype::Effect(result),
                Err(error) => return Ok(Err(error)),
            },
            ("Control.Monad.ST.Internal", "ST") => match unary(self, context, arguments.get(1))? {
                Ok(result) => Monotype::Effect(result),
                Err(error) => return Ok(Err(error)),
            },
            ("Effect.Ref", "Ref") => match unary(self, context, arguments.first())? {
                Ok(value) => Monotype::Reference(value),
                Err(error) => return Ok(Err(error)),
            },
            ("Control.Monad.ST.Internal", "STRef") => {
                match unary(self, context, arguments.get(1))? {
                    Ok(value) => Monotype::Reference(value),
                    Err(error) => return Ok(Err(error)),
                }
            }
            _ => match &module.indexed.items[item].kind {
                IndexedTypeItemKind::Newtype { constructors, .. } => {
                    let Some(&constructor) = constructors.first() else {
                        return Ok(Err(self.open_type(type_id)));
                    };
                    if self.expanding.contains(&(file_id, item)) {
                        return Ok(Ok(self.intern(Monotype::Erased)));
                    }
                    let Some(underlying) =
                        newtype_underlying(context, file_id, constructor, type_id)?
                    else {
                        return Ok(Err(self.open_type(type_id)));
                    };
                    self.expanding.push((file_id, item));
                    let converted = self.convert(context, underlying, expansions + 1);
                    self.expanding.pop();
                    return converted;
                }
                IndexedTypeItemKind::Data { .. } => {
                    let regular = self.is_regular(context, file_id, item)?;
                    let mut canonical = Vec::with_capacity(arguments.len());
                    for argument in arguments {
                        if regular {
                            canonical.push(erase_newtypes(
                                context,
                                argument,
                                expansions,
                                &mut vec![],
                            )?);
                        } else {
                            canonical.push(context.types.erased());
                        }
                    }
                    Monotype::Data(DataType { file_id, item, arguments: Arc::from(canonical) })
                }
                _ => {
                    return Ok(Err(UnsupportedState::Construct {
                        construct: "foreign data types without a Go representation",
                    }));
                }
            },
        };
        Ok(Ok(self.intern(monotype)))
    }

    fn convert_record<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        row: TypeId,
        expansions: usize,
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        let row = context.types.strip_annotations(row);
        let Type::Row(row_id) = context.types.lookup(row).clone() else {
            return Ok(Err(self.open_type(row)));
        };
        let row_type = context.queries.lookup_row_type(row_id).clone();
        if let Some(tail) = row_type.tail
            && !matches!(context.types.lookup(tail), Type::Unification(_))
        {
            return Ok(Err(self.open_type(row)));
        }
        let mut fields = Vec::with_capacity(row_type.fields.len());
        for field in row_type.fields.iter() {
            let monotype = match self.convert(context, field.id, expansions)? {
                Ok(monotype) => monotype,
                Err(error) => return Ok(Err(error)),
            };
            fields.push(RecordField { label: field.label.clone(), monotype });
        }
        fields.sort_by(|left, right| left.label.cmp(&right.label));
        Ok(Ok(self.intern(Monotype::Record(Arc::from(fields)))))
    }

    /// A non-regular data type, such as `data Nested a = Flat | Deep a (Nested (Array a))`,
    /// would need infinitely many specializations; its arguments are erased instead.
    fn is_regular<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        file_id: FileId,
        item: TypeItemId,
    ) -> QueryResult<bool>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(&regular) = self.regular.get(&(file_id, item)) {
            return Ok(regular);
        }
        self.regular.insert((file_id, item), true);
        let module = context.module(file_id)?;
        let terms = match &module.indexed.items[item].kind {
            IndexedTypeItemKind::Data { constructors, .. } => constructors.clone(),
            _ => vec![],
        };
        let mut regular = true;
        for term in terms {
            let Some(signature) = module.checked.lookup_term_item_type(term) else { continue };
            let (_, mut current) = context.types.peel_quantifiers(signature);
            let mut fields = vec![];
            while let Some((argument, result)) = context.types.function_parts(current) {
                fields.push(argument);
                current = result;
            }
            let (_, parameters) = context.types.spine(current);
            let parameters: Vec<TypeId> = parameters
                .iter()
                .map(|&parameter| context.types.strip_annotations(parameter))
                .collect();
            for field in fields {
                if !regular_occurrences(context, field, file_id, item, &parameters) {
                    regular = false;
                }
            }
        }
        self.regular.insert((file_id, item), regular);
        Ok(regular)
    }

    pub fn constructors<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        data: &DataType,
    ) -> QueryResult<Result<Arc<[DataConstructor]>, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(constructors) = self.constructors.get(data) {
            return Ok(Ok(Arc::clone(constructors)));
        }
        let module = context.module(data.file_id)?;
        let terms = match &module.indexed.items[data.item].kind {
            IndexedTypeItemKind::Data { constructors, .. }
            | IndexedTypeItemKind::Newtype { constructors, .. } => constructors.clone(),
            _ => vec![],
        };
        let mut constructors = Vec::with_capacity(terms.len());
        for term in terms {
            let Some(signature) = module.checked.lookup_term_item_type(term) else {
                return Ok(Err(UnsupportedState::MissingDeclaration));
            };
            let (_, body) = context.types.peel_quantifiers(signature);
            let mut field_types = vec![];
            let mut current = body;
            while let Some((argument, result)) = context.types.function_parts(current) {
                field_types.push(argument);
                current = result;
            }
            let (_, parameters) = context.types.spine(current);
            let mut substitution = Substitution::default();
            for (parameter, &argument) in parameters.iter().zip(data.arguments.iter()) {
                if let Type::Rigid(name, _, _) = context.types.lookup(*parameter) {
                    substitution.insert(*name, argument);
                }
            }
            let mut fields = Vec::with_capacity(field_types.len());
            for field_type in field_types {
                let field_type = context.types.substitute(field_type, &substitution);
                match self.monotype(context, field_type)? {
                    Ok(field) => fields.push(field),
                    Err(error) => return Ok(Err(error)),
                }
            }
            let name = module.indexed.items[term].name.clone().unwrap_or_default();
            constructors.push(DataConstructor { term, name, fields });
        }
        let constructors: Arc<[DataConstructor]> = Arc::from(constructors);
        self.constructors.insert(data.clone(), Arc::clone(&constructors));
        Ok(Ok(constructors))
    }
}

/// Newtypes have the runtime representation of their underlying type, and synonyms
/// are only names, so two data types whose arguments differ only by either share one
/// Go type.
fn erase_newtypes<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    expansions: usize,
    expanding: &mut Vec<(FileId, TypeItemId)>,
) -> QueryResult<TypeId>
where
    Q: checking::ExternalQueries,
{
    canonicalise(context, type_id, expansions, expanding, true)
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
    expanding: &mut Vec<(FileId, TypeItemId)>,
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
            let argument = canonicalise(context, argument, expansions, expanding, erase)?;
            let result = canonicalise(context, result, expansions, expanding, erase)?;
            return Ok(context.queries.intern_type(Type::Function(argument, result)));
        }
        Type::Row(row) => {
            let row = context.queries.lookup_row_type(row).clone();
            let mut fields = Vec::with_capacity(row.fields.len());
            for field in row.fields.iter() {
                let id = canonicalise(context, field.id, expansions, expanding, erase)?;
                fields.push(checking::core::RowField { label: field.label.clone(), id });
            }
            fields.sort_by(|left, right| left.label.cmp(&right.label));
            let row = checking::core::RowType { fields: Arc::from(fields), tail: row.tail };
            let row = context.queries.intern_row_type(row);
            return Ok(context.queries.intern_type(Type::Row(row)));
        }
        _ => {}
    }
    let (head, arguments) = context.types.spine(type_id);
    match context.types.lookup(head).clone() {
        Type::Constructor(file_id, item) => {
            let module = context.module(file_id)?;
            if erase
                && let IndexedTypeItemKind::Newtype { constructors, .. } =
                    &module.indexed.items[item].kind
                && let Some(&constructor) = constructors.first()
                && let Some(underlying) =
                    newtype_underlying(context, file_id, constructor, type_id)?
            {
                if expanding.contains(&(file_id, item)) {
                    return Ok(context.types.erased());
                }
                expanding.push((file_id, item));
                let erased = canonicalise(context, underlying, expansions + 1, expanding, erase);
                expanding.pop();
                return erased;
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

fn regular_occurrences<Q>(
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

fn newtype_underlying<Q>(
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
