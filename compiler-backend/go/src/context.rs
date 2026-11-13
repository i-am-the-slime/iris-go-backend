use std::sync::Arc;

use building_types::QueryResult;
use checking::CheckedModule;
use files::FileId;
use indexing::{IndexedModule, TermItemId, TypeItemId};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::types::TypeOperations;

pub struct Context<'q, Q> {
    pub queries: &'q Q,
    pub types: TypeOperations<'q, Q>,
    modules: FxHashMap<FileId, Arc<ModuleData>>,
    pub recursive_newtypes: FxHashMap<(FileId, TypeItemId), bool>,
}

pub struct ModuleData {
    pub name: SmolStr,
    pub indexed: Arc<IndexedModule>,
    pub checked: Arc<CheckedModule>,
    pub lowered: Arc<lowering::LoweredModule>,
}

impl<'q, Q> Context<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub fn new(queries: &'q Q) -> Context<'q, Q> {
        Context {
            queries,
            types: TypeOperations::new(queries),
            modules: FxHashMap::default(),
            recursive_newtypes: FxHashMap::default(),
        }
    }

    pub fn module(&mut self, file_id: FileId) -> QueryResult<Arc<ModuleData>> {
        if let Some(module) = self.modules.get(&file_id) {
            return Ok(Arc::clone(module));
        }
        let name = if file_id == self.queries.prim_id() {
            SmolStr::new_static("Prim")
        } else {
            let content = self.queries.content(file_id)?;
            let (parsed, _) = self.queries.parsed(file_id)?;
            parsed.module_name(&content).map(SmolStr::from).unwrap_or_default()
        };
        let indexed = self.queries.indexed(file_id)?;
        let checked = self.queries.checked(file_id)?;
        let lowered = self.queries.lowered(file_id)?;
        let module = Arc::new(ModuleData { name, indexed, checked, lowered });
        self.modules.insert(file_id, Arc::clone(&module));
        Ok(module)
    }

    pub fn term_name(&mut self, file_id: FileId, term: TermItemId) -> QueryResult<SmolStr> {
        let module = self.module(file_id)?;
        Ok(module.indexed.items[term].name.clone().unwrap_or_default())
    }

    pub fn type_name(&mut self, file_id: FileId, item: TypeItemId) -> QueryResult<SmolStr> {
        let module = self.module(file_id)?;
        Ok(module.indexed.items[item].name.clone().unwrap_or_default())
    }

    pub fn qualified_term_name(
        &mut self,
        file_id: FileId,
        term: TermItemId,
    ) -> QueryResult<String> {
        let module = self.module(file_id)?;
        let name = module.indexed.items[term].name.clone().unwrap_or_default();
        Ok(format!("{}.{}", module.name, name))
    }

    /// A readable rendering of a closed type for use inside Go identifiers.
    pub fn type_suffix(
        &mut self,
        type_id: checking::TypeId,
        output: &mut String,
    ) -> QueryResult<()> {
        use checking::core::Type;
        let type_id = self.types.strip_annotations(type_id);
        match self.types.lookup(type_id).clone() {
            Type::Application(function, argument) => {
                self.type_suffix(function, output)?;
                self.type_suffix(argument, output)?;
            }
            Type::Function(argument, result) => {
                output.push_str("Fn");
                self.type_suffix(argument, output)?;
                self.type_suffix(result, output)?;
            }
            Type::Constructor(file_id, item) | Type::Synonym(file_id, item) => {
                let name = self.type_name(file_id, item)?;
                output.push_str(match name.as_str() {
                    "Function" => "Fn",
                    "Record" => "",
                    name => name,
                });
            }
            Type::Row(row) => {
                let row = self.queries.lookup_row_type(row).clone();
                output.push_str("Record");
                for field in row.fields.iter() {
                    output.push_str(&capitalise(&field.label));
                }
            }
            _ => {}
        }
        Ok(())
    }

    pub fn is_type(
        &mut self,
        file_id: FileId,
        item: TypeItemId,
        module_name: &str,
        type_name: &str,
    ) -> QueryResult<bool> {
        let module = self.module(file_id)?;
        Ok(module.name == module_name
            && module.indexed.items[item].name.as_deref() == Some(type_name))
    }
}

pub fn capitalise(text: &str) -> String {
    let mut characters = text.chars();
    match characters.next() {
        Some(first) => first.to_uppercase().chain(characters).collect(),
        None => String::new(),
    }
}
