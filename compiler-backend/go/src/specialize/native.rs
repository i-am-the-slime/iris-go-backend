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
    name: String,
    generic: bool,
    boxed: Option<String>,
    mentioned: Vec<(FileId, TypeItemId)>,
    names_a_row: bool,
}

struct ForeignData {
    name: String,
    generic: bool,
    boxed: Option<String>,
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
        let mut native_data: FxHashSet<(FileId, TypeItemId)> =
            data.iter().filter(|(_, data)| data.boxed.is_none()).map(|(&key, _)| key).collect();
        let mut native_functions: FxHashSet<(FileId, TermItemId)> = functions
            .iter()
            .filter(|function| function.boxed.is_none())
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
                let mut mentioning =
                    functions.iter().filter(|function| function.mentioned.contains(key));
                let generic = data.get(key).is_some_and(|data: &ForeignData| data.generic);
                !generic || mentioning.all(|function| native_functions.contains(&function.key))
            });
            if (native_data.len(), native_functions.len()) == before {
                break;
            }
        }
        if std::env::var_os("IRIS_GO_FOREIGN_BOXING").is_some() {
            report_boxing(&functions, &data, &native_functions, &native_data);
        }
        self.monotypes.row_free_foreigns = functions
            .iter()
            .filter(|function| !function.names_a_row)
            .map(|function| function.key)
            .collect();
        self.monotypes.native_foreigns = native_functions;
        self.monotypes.native_foreign_data = native_data;
        self.monotypes.empty_interface_foreign_data =
            data.iter().filter(|(_, data)| data.empty_interface).map(|(&key, _)| key).collect();
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
            let boxed = boxed_reason(source, declaration, &go_name, None).filter(|_| generic);
            let name = format!("{}.{name}", module.name);
            let empty_interface = source.opacity.interface_aliases.contains(&go_name);
            data.push(((file_id, item), ForeignData { name, generic, boxed, empty_interface }));
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
            let go_name = crate::naming::exported(name);
            let declaration = source.opacity.function(&go_name);
            let boxed = boxed_reason(source, declaration, &go_name, Some(quantifiers));
            let names_a_row = self.names_a_row(declared)?;
            functions.push(ForeignFunction {
                key: (file_id, term),
                name: format!("{}.{name}", module.name),
                generic: quantifiers > 0,
                boxed,
                mentioned,
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
                    if let Some(constructor_type) =
                        module.checked.lookup_term_item_type(constructor)
                    {
                        self.mentioned_foreign_data(constructor_type, mentioned, visited)?;
                    }
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

fn boxed_reason(
    source: &ForeignSource,
    declaration: Option<&OpaqueDeclaration>,
    go_name: &str,
    quantifiers: Option<usize>,
) -> Option<String> {
    if let Some(reason) = &source.opacity.unreadable {
        return Some(format!("its Go could not be read: {reason}"));
    }
    let Some(declaration) = declaration else {
        return Some(format!("its Go declares no generic `{go_name}`"));
    };
    if let Some(quantifiers) = quantifiers
        && quantifiers != declaration.parameters.len()
    {
        let parameters = declaration.parameters.len();
        return Some(format!(
            "`{go_name}` takes {parameters} type parameters for {quantifiers} quantified types"
        ));
    }
    let escape = declaration.escapes.first()?;
    Some(format!("in `{go_name}`, {escape}"))
}

fn report_boxing(
    functions: &[ForeignFunction],
    data: &FxHashMap<(FileId, TypeItemId), ForeignData>,
    native_functions: &FxHashSet<(FileId, TermItemId)>,
    native_data: &FxHashSet<(FileId, TypeItemId)>,
) {
    for function in functions {
        if !function.generic || native_functions.contains(&function.key) {
            continue;
        }
        let reason = function.boxed.clone().unwrap_or_else(|| {
            let boxed = function.mentioned.iter().find(|key| !native_data.contains(*key));
            let name = boxed.and_then(|key| data.get(key)).map(|data| data.name.as_str());
            format!("it takes or returns {}, whose values are boxed", name.unwrap_or("a type"))
        });
        eprintln!("go: foreign {} boxes its type arguments: {reason}", function.name);
    }
    let mut boxed_data: Vec<_> = data
        .iter()
        .filter(|(key, foreign_data)| foreign_data.generic && !native_data.contains(*key))
        .collect();
    boxed_data.sort_by(|(_, left), (_, right)| left.name.cmp(&right.name));
    for (key, foreign_data) in boxed_data {
        let reason = foreign_data.boxed.clone().unwrap_or_else(|| {
            let boxing = functions.iter().find(|function| {
                function.mentioned.contains(key) && !native_functions.contains(&function.key)
            });
            let name = boxing.map(|function| function.name.as_str()).unwrap_or("a foreign");
            format!("{name} boxes its type arguments")
        });
        eprintln!("go: foreign data {} holds boxed values: {reason}", foreign_data.name);
    }
}
