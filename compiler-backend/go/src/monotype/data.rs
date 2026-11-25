use std::sync::Arc;

use building_types::QueryResult;
use checking::TypeId;
use checking::core::Type;
use files::FileId;
use indexing::{IndexedTypeItemKind, TypeItemId};

use super::types::{
    expand_synonyms, is_refuted_equality, newtype_underlying, open_type, regular_occurrences,
};
use smol_str::SmolStr;

use super::{Converted, DataConstructor, DataType, Monotype, MonotypeId, Monotypes, RecordField};
use crate::context::Context;
use crate::error::{GoResult, UnsupportedState};
use crate::scheme::Read;
use crate::types::Substitution;

impl Monotypes {
    /// The record of a closed row.
    pub fn record<Q>(&mut self, context: &mut Context<'_, Q>, row: TypeId) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        self.convert_record(context, row, 0)
    }

    pub(super) fn convert_record<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        row: TypeId,
        expansions: usize,
    ) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        let row = context.types.strip_annotations(row);
        // A row synonym, `Padding (TokValue String ())`, or a row whose tail is
        // one spells a closed row only once it is expanded and flattened.
        let row = match context.types.lookup(row) {
            Type::Row(row_id) if context.queries.lookup_row_type(*row_id).tail.is_none() => row,
            _ => expand_synonyms(context, row)?,
        };
        let Type::Row(row_id) = context.types.lookup(row).clone() else {
            return Err(open_type(context, row)?);
        };
        let row_type = context.queries.lookup_row_type(row_id).clone();
        // An erased row variable, the `ops` of an erased `forall node ops.
        // Record (Operations node ops) -> ...`, stands for fields the code cannot
        // name; the record holds the ones it can.
        if let Some(tail) = row_type.tail
            && !matches!(context.types.lookup(tail), Type::Unification(_))
            && context.types.erasure(tail).is_none()
        {
            return Err(open_type(context, row)?);
        }
        let mut fields: Vec<RecordField> = Vec::with_capacity(row_type.fields.len());
        for field in row_type.fields.iter() {
            // A row lists a duplicated label leftmost first. A record value
            // holds only that one, as a JS object does after `Record.union`,
            // and `Lacks` keeps the shadowed types from being observed.
            if fields.iter().any(|known| known.label == field.label) {
                continue;
            }
            let monotype = self.convert(context, field.id, expansions)?;
            fields.push(RecordField { label: field.label.clone(), monotype });
        }
        fields.sort_by(|left, right| left.label.cmp(&right.label));
        Ok(self.intern(Monotype::Record(Arc::from(fields))))
    }

    /// A non-regular data type, such as `data Nested a = Flat | Deep a (Nested (Array a))`,
    /// would need infinitely many specializations; its arguments are erased instead.
    pub(super) fn is_regular<Q>(
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

    pub fn unfold<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        data: &DataType,
    ) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(&unfolded) = self.unfolded.get(data) {
            self.schemes.note_cached(Read::Unfolded(data.clone()));
            return Ok(unfolded);
        }
        let reads_start = self.schemes.read_count();
        let module = context.module(data.file_id)?;
        let IndexedTypeItemKind::Newtype { constructors, .. } =
            &module.indexed.items[data.item].kind
        else {
            return Err(UnsupportedState::MissingDeclaration.into());
        };
        let Some(&constructor) = constructors.first() else {
            return Err(UnsupportedState::MissingDeclaration.into());
        };
        let mut applied = context.queries.intern_type(Type::Constructor(data.file_id, data.item));
        for &argument in data.arguments.iter() {
            applied = context.queries.intern_type(Type::Application(applied, argument));
        }
        let Some(underlying) = newtype_underlying(context, data.file_id, constructor, applied)?
        else {
            return Err(open_type(context, applied)?);
        };
        let unfolded = self.monotype(context, underlying)?;
        self.unfolded.insert(data.clone(), unfolded);
        self.unfolded_reads.insert(data.clone(), self.schemes.reads_since(reads_start));
        Ok(unfolded)
    }

    /// [`Self::unfold`], reporting what cannot be unfolded against `definition`.
    pub fn unfold_in<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        data: &DataType,
        definition: &str,
    ) -> GoResult<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        self.unfold(context, data).map_err(|failure| failure.at(definition))
    }

    pub fn constructors<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        data: &DataType,
    ) -> Converted<Arc<[DataConstructor]>>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(family) = self.exists_family(data) {
            return self.witness_constructors(context, family);
        }
        if let Some(constructors) = self.constructors.get(data) {
            self.schemes.note_cached(Read::Constructors(data.clone()));
            return Ok(Arc::clone(constructors));
        }
        if let Some(row) = self.variant_row(data) {
            let constructors = self.variant_constructors(context, row)?;
            self.constructors.insert(data.clone(), Arc::clone(&constructors));
            return Ok(constructors);
        }
        let reads_start = self.schemes.read_count();
        let module = context.module(data.file_id)?;
        let terms = match &module.indexed.items[data.item].kind {
            IndexedTypeItemKind::Data { constructors, .. }
            | IndexedTypeItemKind::Newtype { constructors, .. } => constructors.clone(),
            _ => vec![],
        };
        let mut constructors = Vec::with_capacity(terms.len());
        for term in terms {
            let Some(signature) = module.checked.lookup_term_item_type(term) else {
                return Err(UnsupportedState::MissingDeclaration.into());
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
            let mut refuted = false;
            for field_type in field_types {
                let field_type = context.types.substitute(field_type, &substitution);
                refuted |= is_refuted_equality(context, field_type)?;
                let constructor = module.indexed.items[term].name.clone().unwrap_or_default();
                let owner = format!("{}.{constructor}", module.name);
                self.note_rank_n_field(context, field_type, &owner)?;
                let field = self.monotype(context, field_type)?;
                refuted |= self.is_uninhabited_family(field);
                fields.push(field)
            }
            let name = module.indexed.items[term].name.clone().unwrap_or_default();
            constructors.push(DataConstructor { term: Some(term), name, fields, refuted });
        }
        let constructors: Arc<[DataConstructor]> = Arc::from(constructors);
        self.constructors.insert(data.clone(), Arc::clone(&constructors));
        self.constructors_reads.insert(data.clone(), self.schemes.reads_since(reads_start));
        Ok(constructors)
    }

    /// How many constructors a data type has, when every one of them is
    /// known and has no fields: values of it are told apart, and ordered, by
    /// their constructor alone, as Go's constants of an enumeration are.
    pub fn constructor_name(&self, data: &DataType, constructor: usize) -> Option<SmolStr> {
        Some(self.constructors.get(data)?.get(constructor)?.name.clone())
    }

    pub fn enumeration_size(&self, data: &DataType) -> Option<usize> {
        let constructors = self.constructors.get(data)?;
        let nullary = constructors.iter().all(|constructor| constructor.fields.is_empty());
        (nullary && self.variant_row(data).is_none()).then_some(constructors.len())
    }

    pub fn holds_function(&self, id: MonotypeId) -> bool {
        match self.get(id) {
            Monotype::Function(..) => true,
            Monotype::Data(data) => self.constructors.get(data).is_some_and(|constructors| {
                constructors.iter().any(|constructor| {
                    constructor.fields.iter().any(|&field| self.function_parts(field).is_some())
                })
            }),
            _ => false,
        }
    }

    /// A data type at its arguments, with the argument of each phantom parameter
    /// replaced by one stand-in and each erasure at one cause. No field of
    /// `Free f a` holds an `a`, so `Free f Unit` and `Free f Int` are one
    /// representation, one Go type, and a value moves between them unchanged.
    pub fn data_type<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        file_id: FileId,
        item: TypeItemId,
        arguments: Arc<[TypeId]>,
    ) -> QueryResult<DataType>
    where
        Q: checking::ExternalQueries,
    {
        let used = self.used_parameters(context, file_id, item)?;
        let phantom = context.types.phantom();
        let arguments = arguments
            .iter()
            .enumerate()
            .map(|(position, &argument)| match used.get(position) {
                Some(false) => phantom,
                _ => context.types.without_causes(argument),
            })
            .collect();
        Ok(DataType { file_id, item, arguments })
    }

    pub fn exists_family(&self, data: &DataType) -> Option<TypeId> {
        let existential = self.existential?;
        let [family] = data.arguments[..] else { return None };
        ((data.file_id, data.item) == existential).then_some(family)
    }

    fn is_uninhabited_family(&self, monotype: MonotypeId) -> bool {
        let Monotype::Data(data) = self.get(monotype) else { return false };
        self.exists_family(data).is_some_and(|family| self.schemes.witnesses(family).is_empty())
    }

    pub(super) fn converts_every_field<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        row: TypeId,
        expansions: usize,
    ) -> bool
    where
        Q: checking::ExternalQueries,
    {
        let Type::Row(row_id) = context.types.lookup(row).clone() else { return false };
        let fields = context.queries.lookup_row_type(row_id).fields.clone();
        fields.iter().all(|field| self.convert(context, field.id, expansions).is_ok())
    }

    pub fn variant_type(&self) -> Option<(FileId, TypeItemId)> {
        self.variant
    }

    pub fn variant_row(&self, data: &DataType) -> Option<TypeId> {
        let variant = self.variant?;
        let [row] = data.arguments[..] else { return None };
        ((data.file_id, data.item) == variant).then_some(row)
    }

    fn variant_constructors<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        row: TypeId,
    ) -> Converted<Arc<[DataConstructor]>>
    where
        Q: checking::ExternalQueries,
    {
        let Type::Row(row_id) = context.types.lookup(row).clone() else {
            return Err(open_type(context, row)?);
        };
        let row_type = context.queries.lookup_row_type(row_id).clone();
        let mut constructors: Vec<DataConstructor> = Vec::with_capacity(row_type.fields.len());
        for field in row_type.fields.iter() {
            if constructors.iter().any(|known| known.name == field.label) {
                continue;
            }
            let fields = vec![self.monotype(context, field.id)?];
            let name = field.label.clone();
            constructors.push(DataConstructor { term: None, name, fields, refuted: false });
        }
        constructors.sort_by(|left, right| left.name.cmp(&right.name));
        Ok(Arc::from(constructors))
    }

    fn witness_constructors<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        family: TypeId,
    ) -> Converted<Arc<[DataConstructor]>>
    where
        Q: checking::ExternalQueries,
    {
        let witnesses = self.schemes.witnesses(family).to_vec();
        let mut constructors = Vec::with_capacity(witnesses.len());
        for witness in witnesses {
            let payload = context.queries.intern_type(Type::Application(family, witness.types[0]));
            let fields = vec![self.monotype(context, payload)?];
            constructors.push(DataConstructor {
                term: None,
                name: witness.label,
                fields,
                refuted: false,
            });
        }
        Ok(Arc::from(constructors))
    }

    pub fn used_parameters<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        file_id: FileId,
        item: TypeItemId,
    ) -> QueryResult<Arc<[bool]>>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(used) = self.used_parameters.get(&(file_id, item)) {
            return Ok(Arc::clone(used));
        }
        let module = context.module(file_id)?;
        let terms = match &module.indexed.items[item].kind {
            IndexedTypeItemKind::Data { constructors, .. }
            | IndexedTypeItemKind::Newtype { constructors, .. } => constructors.clone(),
            _ => vec![],
        };
        let mut used: Vec<bool> = vec![];
        for term in terms {
            let Some(signature) = module.checked.lookup_term_item_type(term) else { continue };
            let (_, mut current) = context.types.peel_quantifiers(signature);
            let mut fields = vec![];
            while let Some((field, result)) = context.types.function_parts(current) {
                fields.push(field);
                current = result;
            }
            let mut mentioned = vec![];
            for field in fields {
                context.types.rigid_names_outside(field, Some(current), &mut mentioned);
            }
            let (_, parameters) = context.types.spine(current);
            used.resize(used.len().max(parameters.len()), false);
            for (position, parameter) in parameters.iter().enumerate() {
                if let Type::Rigid(name, _, _) = context.types.lookup(*parameter)
                    && mentioned.contains(name)
                {
                    used[position] = true;
                }
            }
        }
        let used: Arc<[bool]> = Arc::from(used);
        self.used_parameters.insert((file_id, item), Arc::clone(&used));
        Ok(used)
    }
}
