use checking::TypeId;
use checking::core::Type;
use files::FileId;
use indexing::{IndexedTermItemKind, IndexedTypeItemKind, TermItemId, TypeItemId};
use rustc_hash::{FxHashMap, FxHashSet};

use super::Specializer;
use crate::error::GoResult;
use crate::foreign::{ForeignSource, OpaqueDeclaration};

struct ForeignFunction {
    key: (FileId, TermItemId),
    boxed: bool,
    mentioned: Vec<(FileId, TypeItemId)>,
    mentioned_at_quantified: Vec<(FileId, TypeItemId)>,
    names_a_row: bool,
}

struct ForeignData {
    generic: bool,
    boxed: bool,
    empty_interface: bool,
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub fn adopt_native_foreigns(&mut self) -> GoResult<()> {
        let mut functions = vec![];
        let mut data = FxHashMap::default();
        let foreign_packages = self.foreign_packages;
        for source in &foreign_packages.sources {
            let Some(file_id) = self.context.queries.module_file(&source.module) else { continue };
            data.extend(self.foreign_data(file_id, source)?);
            functions.extend(self.foreign_functions(file_id, source)?);
        }
        let native_data = data.iter().filter(|(_, data)| !data.boxed).map(|(&key, _)| key);
        let mut native_data: FxHashSet<(FileId, TypeItemId)> = native_data.collect();
        let mut native_functions: FxHashSet<(FileId, TermItemId)> = functions
            .iter()
            .filter(|function| !function.boxed)
            .map(|function| function.key)
            .collect();
        loop {
            let before = (native_data.len(), native_functions.len());
            native_functions.retain(|key| {
                let function = functions.iter().find(|function| function.key == *key);
                function.is_some_and(|function| {
                    function.mentioned.iter().all(|mentioned| native_data.contains(mentioned))
                })
            });
            native_data.retain(|key| {
                let mut mentioning = functions
                    .iter()
                    .filter(|function| function.mentioned_at_quantified.contains(key));
                let generic = data.get(key).is_some_and(|data: &ForeignData| data.generic);
                !generic || mentioning.all(|function| native_functions.contains(&function.key))
            });
            if (native_data.len(), native_functions.len()) == before {
                break;
            }
        }
        self.monotypes.row_free_foreigns = functions
            .iter()
            .filter(|function| !function.names_a_row)
            .map(|function| function.key)
            .collect();
        self.monotypes.native_foreigns = native_functions;
        self.monotypes.native_foreign_data = native_data;
        let empty_interface = data.iter().filter(|(_, data)| data.empty_interface);
        let empty_interface = empty_interface.map(|(&key, _)| key).collect();
        self.monotypes.empty_interface_foreign_data = empty_interface;
        Ok(())
    }

    fn foreign_data(
        &mut self,
        file_id: FileId,
        source: &ForeignSource,
    ) -> GoResult<Vec<((FileId, TypeItemId), ForeignData)>> {
        let module = self.context.module(file_id)?;
        let mut data = vec![];
        for (item, indexed) in module.indexed.items.iter_types() {
            let IndexedTypeItemKind::Foreign { .. } = indexed.kind else { continue };
            let Some(name) = indexed.name.as_deref() else { continue };
            let go_name = module.foreign_type_name(name);
            let declaration = source.opacity.data_type(&go_name);
            let generic = declaration.is_some_and(|declaration| !declaration.parameters.is_empty());
            let boxed = generic && boxes_type_arguments(source, declaration, None);
            let empty_interface = source.opacity.interface_aliases.contains(&go_name);
            data.push(((file_id, item), ForeignData { generic, boxed, empty_interface }));
        }
        Ok(data)
    }

    fn foreign_functions(
        &mut self,
        file_id: FileId,
        source: &ForeignSource,
    ) -> GoResult<Vec<ForeignFunction>> {
        let module = self.context.module(file_id)?;
        let mut functions = vec![];
        for (term, indexed) in module.indexed.items.iter_terms() {
            let IndexedTermItemKind::Foreign { .. } = indexed.kind else { continue };
            let Some(name) = indexed.name.as_deref() else { continue };
            let Some(declared) = module.checked.lookup_term_item_type(term) else { continue };
            let declared = crate::monotype::expand_synonyms(&mut self.context, declared)?;
            let quantifiers = self.context.types.peel_quantifiers(declared).0.len();
            let mut mentioned = vec![];
            self.mentioned_foreign_data(declared, &mut mentioned, &mut FxHashSet::default())?;
            let mut mentioned_at_quantified = vec![];
            self.foreign_data_at_quantified(declared, &mut mentioned_at_quantified)?;
            let go_name = crate::naming::exported(name);
            let declaration = source.opacity.function(&go_name);
            let boxed = boxes_type_arguments(source, declaration, Some(quantifiers));
            let names_a_row = self.names_a_row(declared)?;
            functions.push(ForeignFunction {
                key: (file_id, term),
                boxed,
                mentioned,
                mentioned_at_quantified,
                names_a_row,
            });
        }
        Ok(functions)
    }

    fn mentioned_foreign_data(
        &mut self,
        type_id: TypeId,
        mentioned: &mut Vec<(FileId, TypeItemId)>,
        visited: &mut FxHashSet<(FileId, TypeItemId)>,
    ) -> GoResult<()> {
        match self.context.types.lookup(type_id).clone() {
            Type::Application(function, argument)
            | Type::Function(function, argument)
            | Type::Constrained(function, argument) => {
                self.mentioned_foreign_data(function, mentioned, visited)?;
                self.mentioned_foreign_data(argument, mentioned, visited)?;
            }
            Type::KindApplication(inner, _)
            | Type::Kinded(inner, _)
            | Type::ConstraintOrigin(inner, _)
            | Type::Forall(_, inner) => self.mentioned_foreign_data(inner, mentioned, visited)?,
            Type::Row(row) => {
                let row = self.context.queries.lookup_row_type(row).clone();
                for field in row.fields.iter() {
                    self.mentioned_foreign_data(field.id, mentioned, visited)?;
                }
                if let Some(tail) = row.tail {
                    self.mentioned_foreign_data(tail, mentioned, visited)?;
                }
            }
            Type::Constructor(file_id, item) | Type::Synonym(file_id, item) => {
                if !visited.insert((file_id, item)) {
                    return Ok(());
                }
                let module = self.context.module(file_id)?;
                let constructors = match &module.indexed.items[item].kind {
                    IndexedTypeItemKind::Foreign { .. } => {
                        if self.foreign_packages.source(&module.name).is_some() {
                            mentioned.push((file_id, item));
                        }
                        return Ok(());
                    }
                    IndexedTypeItemKind::Data { constructors, .. }
                    | IndexedTypeItemKind::Newtype { constructors, .. } => constructors.clone(),
                    IndexedTypeItemKind::Synonym { .. } => {
                        let Some(synonym) = module.checked.lookup_synonym(item) else {
                            return Ok(());
                        };
                        return self.mentioned_foreign_data(synonym.expansion, mentioned, visited);
                    }
                    _ => return Ok(()),
                };
                for constructor in constructors {
                    let constructor_type = module.checked.lookup_term_item_type(constructor);
                    if let Some(constructor_type) = constructor_type {
                        self.mentioned_foreign_data(constructor_type, mentioned, visited)?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn foreign_data_at_quantified(
        &mut self,
        type_id: TypeId,
        mentioned: &mut Vec<(FileId, TypeItemId)>,
    ) -> GoResult<()> {
        if !self.context.queries.lookup_type_flags(type_id).has_rigid() {
            return Ok(());
        }
        match self.context.types.lookup(type_id).clone() {
            Type::Application(..) => {
                let (head, arguments) = self.context.types.spine(type_id);
                if let Type::Constructor(..) | Type::Synonym(..) = self.context.types.lookup(head) {
                    return self.mentioned_foreign_data(
                        type_id,
                        mentioned,
                        &mut FxHashSet::default(),
                    );
                }
                self.foreign_data_at_quantified(head, mentioned)?;
                for argument in arguments {
                    self.foreign_data_at_quantified(argument, mentioned)?;
                }
            }
            Type::Function(argument, result) | Type::Constrained(argument, result) => {
                self.foreign_data_at_quantified(argument, mentioned)?;
                self.foreign_data_at_quantified(result, mentioned)?;
            }
            Type::KindApplication(inner, _)
            | Type::Kinded(inner, _)
            | Type::ConstraintOrigin(inner, _)
            | Type::Forall(_, inner) => self.foreign_data_at_quantified(inner, mentioned)?,
            Type::Row(row) => {
                let row = self.context.queries.lookup_row_type(row).clone();
                for field in row.fields.iter() {
                    self.foreign_data_at_quantified(field.id, mentioned)?;
                }
                if let Some(tail) = row.tail {
                    self.foreign_data_at_quantified(tail, mentioned)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn names_a_row(&mut self, type_id: TypeId) -> GoResult<bool> {
        Ok(match self.context.types.lookup(type_id).clone() {
            Type::Row(_) => true,
            Type::Application(function, argument)
            | Type::Function(function, argument)
            | Type::Constrained(function, argument) => {
                self.names_a_row(function)? || self.names_a_row(argument)?
            }
            Type::KindApplication(inner, _)
            | Type::Kinded(inner, _)
            | Type::ConstraintOrigin(inner, _)
            | Type::Forall(_, inner) => self.names_a_row(inner)?,
            Type::Synonym(file_id, item) => {
                let module = self.context.module(file_id)?;
                match module.checked.lookup_synonym(item) {
                    Some(synonym) => self.names_a_row(synonym.expansion)?,
                    None => true,
                }
            }
            _ => false,
        })
    }
}

fn boxes_type_arguments(
    source: &ForeignSource,
    declaration: Option<&OpaqueDeclaration>,
    quantifiers: Option<usize>,
) -> bool {
    if source.opacity.unreadable.is_some() {
        return true;
    }
    let Some(declaration) = declaration else {
        return true;
    };
    // Go infers the type parameters after the quantified ones from the arguments.
    if let Some(quantifiers) = quantifiers
        && !declaration.parameters.get(quantifiers..).is_some_and(|extra| {
            extra.iter().all(|parameter| declaration.inferred.contains(parameter))
        })
    {
        return true;
    }
    !declaration.escapes.is_empty()
}
