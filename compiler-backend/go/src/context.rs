use std::sync::Arc;

use building_types::QueryResult;
use checking::CheckedModule;
use files::FileId;
use indexing::{IndexedModule, TermItemId, TypeItemId};
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use crate::naming::capitalise;
use crate::types::{Substituted, TypeOperations};

pub struct Context<'q, Q> {
    pub queries: &'q Q,
    pub types: TypeOperations<'q, Q>,
    modules: FxHashMap<FileId, Arc<ModuleData>>,
    pub recursive_newtypes: FxHashMap<(FileId, TypeItemId), bool>,
    /// Canonical spellings of types, with and without erased newtypes, as
    /// `monotype::canonicalise` computes them from the outermost level.
    pub canonical: FxHashMap<(checking::TypeId, bool), checking::TypeId>,
    /// Newtypes, with their arguments, that canonicalisation erased to the
    /// type they wrap, in the order met; a record may be named after one.
    pub erased_newtypes: Vec<ErasedNewtype>,
    pub erased_variant_rows: FxHashSet<checking::TypeId>,
}

impl ModuleData {
    /// The Go name of a type a project's foreign package declares: the
    /// type's own name, capitalised, unless one of the module's values
    /// capitalises to it too (hyrule's `objHack` builds an `ObjHack`), in which
    /// case the type's name ends in `Type`.
    pub fn foreign_type_name(&self, type_name: &str) -> String {
        let name = capitalise(type_name);
        let taken = self.indexed.items.iter_terms().any(|(_, term)| {
            term.name.as_deref().is_some_and(|term_name| capitalise(term_name) == name)
        });
        if taken { format!("{name}Type") } else { name }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErasedNewtype {
    pub file_id: FileId,
    pub item: TypeItemId,
    pub arguments: Arc<[checking::TypeId]>,
    pub erased: checking::TypeId,
}

pub struct ModuleData {
    pub file_id: FileId,
    pub name: SmolStr,
    pub indexed: Arc<IndexedModule>,
    pub checked: Arc<CheckedModule>,
    pub lowered: Arc<lowering::LoweredModule>,
    /// Where each lowered expression is written, for the source positions of the Go.
    pub stabilized: Arc<stabilizing::StabilizedModule>,
}

impl<'q, Q> Context<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub fn new(queries: &'q Q) -> Context<'q, Q> {
        Context::sharing(queries, Substituted::default())
    }

    pub fn sharing(queries: &'q Q, substituted: Substituted) -> Context<'q, Q> {
        Context {
            queries,
            types: TypeOperations::sharing(queries, substituted),
            modules: FxHashMap::default(),
            recursive_newtypes: FxHashMap::default(),
            canonical: FxHashMap::default(),
            erased_newtypes: vec![],
            erased_variant_rows: FxHashSet::default(),
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
            parsed.module_name(&content).unwrap_or_default()
        };
        let indexed = self.queries.indexed(file_id)?;
        let checked = self.queries.checked(file_id)?;
        let lowered = self.queries.lowered(file_id)?;
        let stabilized = self.queries.stabilized(file_id)?;
        let module = Arc::new(ModuleData { file_id, name, indexed, checked, lowered, stabilized });
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
    /// `Int64` for `Long' Signed` and `UInt64` for `Long' Unsigned`, the
    /// newtypes' names for them.
    pub fn signed_long_name(
        &mut self,
        type_id: checking::TypeId,
    ) -> QueryResult<Option<&'static str>> {
        use crate::primitives::{KnownType, known_type};
        use checking::core::Type;
        let Type::Application(function, argument) = self.types.lookup(type_id).clone() else {
            return Ok(None);
        };
        let named = |context: &mut Context<'q, Q>, type_id| -> QueryResult<Option<KnownType>> {
            let type_id = context.types.strip_annotations(type_id);
            let Type::Constructor(file_id, item) = context.types.lookup(type_id).clone() else {
                return Ok(None);
            };
            let module = context.module(file_id)?;
            let name = module.indexed.items[item].name.clone().unwrap_or_default();
            Ok(known_type(&module.name, &name))
        };
        if named(self, function)? != Some(KnownType::SignedLong) {
            return Ok(None);
        }
        Ok(match named(self, argument)? {
            Some(KnownType::Signed) => Some("Int64"),
            Some(KnownType::Unsigned) => Some("UInt64"),
            _ => None,
        })
    }

    pub fn type_suffix(
        &mut self,
        type_id: checking::TypeId,
        output: &mut String,
    ) -> QueryResult<()> {
        use checking::core::Type;
        let type_id = self.types.strip_annotations(type_id);
        if let Some(spelled) = self.signed_long_name(type_id)? {
            output.push_str(spelled);
            return Ok(());
        }
        match self.types.lookup(type_id).clone() {
            Type::Application(function, argument) => {
                self.type_suffix(function, output)?;
                if let Some(labels) = self.variant_labels(function, argument)? {
                    output.push_str(&labels);
                    return Ok(());
                }
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

    pub fn variant_labels(
        &mut self,
        function: checking::TypeId,
        argument: checking::TypeId,
    ) -> QueryResult<Option<String>> {
        use checking::core::Type;
        let function = self.types.strip_annotations(function);
        let Type::Constructor(file_id, item) = self.types.lookup(function).clone() else {
            return Ok(None);
        };
        let module = self.module(file_id)?;
        let name = module.indexed.items[item].name.clone().unwrap_or_default();
        if crate::primitives::known_type(&module.name, &name)
            != Some(crate::primitives::KnownType::Variant)
        {
            return Ok(None);
        }
        let argument = self.types.strip_annotations(argument);
        let Type::Row(row) = self.types.lookup(argument).clone() else { return Ok(None) };
        let row = self.queries.lookup_row_type(row).clone();
        Ok(Some(row.fields.iter().map(|field| capitalise(&field.label)).collect()))
    }

    pub fn effect_function_arity(
        &mut self,
        type_id: checking::core::TypeId,
    ) -> QueryResult<Option<usize>> {
        self.uncurried_arity(type_id, false)
    }

    pub fn uncurried_function_arity(
        &mut self,
        type_id: checking::core::TypeId,
    ) -> QueryResult<Option<usize>> {
        self.uncurried_arity(type_id, true)
    }

    fn uncurried_arity(
        &mut self,
        type_id: checking::core::TypeId,
        pure: bool,
    ) -> QueryResult<Option<usize>> {
        use checking::core::Type;
        let type_id = crate::monotype::expand_synonyms(self, type_id)?;
        let (head, _) = self.types.spine(type_id);
        let head = self.types.strip_annotations(head);
        let Type::Constructor(file_id, item) = self.types.lookup(head).clone() else {
            return Ok(None);
        };
        let module = self.module(file_id)?;
        let name = module.indexed.items[item].name.clone().unwrap_or_default();
        let count = match module.name.as_str() {
            "Effect.Uncurried" => name.strip_prefix("EffectFn"),
            "Control.Monad.ST.Uncurried" => name.strip_prefix("STFn"),
            "Data.Function.Uncurried" if pure => name.strip_prefix("Fn"),
            _ => None,
        };
        Ok(count.and_then(|count| count.parse().ok()).filter(|&arity| arity > 0))
    }

    pub fn argument_groups(
        &mut self,
        type_id: checking::core::TypeId,
    ) -> QueryResult<Option<Vec<usize>>> {
        let mut groups = vec![];
        let mut current = type_id;
        loop {
            if let Some(arity) = self.effect_function_arity(current)? {
                groups.push(arity);
                break;
            }
            let expanded = crate::monotype::expand_synonyms(self, current)?;
            let (_, expanded) = self.types.peel_quantifiers(expanded);
            let Some((_, result)) = self.types.function_parts(expanded) else { break };
            groups.push(1);
            current = result;
        }
        Ok(groups.iter().any(|&size| size > 1).then_some(groups))
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
