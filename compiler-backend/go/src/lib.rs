//! Whole-program Go code generation from checked PureScript.
//!
//! The backend specializes the program from an entry point using the checker's
//! types and evidence, simplifies the resulting monomorphic tree, and renders it
//! as one Go package per PureScript module, the entry module's being `main`.

mod arity;
mod blocker;
mod call_sites;
mod context;
mod dictionary;
mod emit;
mod erasure;
mod error;
mod foreign;
mod go_traversal;
mod graph;
mod lift;
mod maps;
mod merge;
mod modules;
mod monomorphic;
mod monotype;
mod naming;
mod numeric;
mod primitives;
mod purity;
mod scheme;
mod simplify;
mod specialize;
mod suspension;
mod syntax;
mod types;
mod work;

pub use emit::{KERNEL_FILE_SUFFIXES, is_kernel_file};
pub use error::{GoError, GoResult, UnsupportedState};
pub use foreign::{
    EmbedError, ForeignPackages, ForeignSource, LineCoverage, LineDirectives, embedded_files,
    foreign_declarations, foreign_files, foreign_forwarders, foreign_opacity, foreign_source,
    foreign_structs, recovers, uses_event_loop,
};
pub use work::Work;

use crate::specialize::Specializer;
use rustc_hash::{FxHashMap, FxHashSet};

pub struct GoProgram {
    /// Each Go source file, by its path relative to the output directory, in
    /// order of path.
    pub files: Vec<(String, String)>,
    pub functions: usize,
    /// Where the program behaves differently from the JavaScript backend's, and why.
    pub notes: Vec<String>,
}

pub fn compile_program(
    queries: &impl checking::ExternalQueries,
    entry_module: &str,
    entry_name: &str,
    foreign_packages: &ForeignPackages,
    module_path: &str,
) -> GoResult<GoProgram> {
    let qualified = format!("{entry_module}.{entry_name}");
    let file_id = queries
        .module_file(entry_module)
        .ok_or_else(|| GoError::MissingEntry(qualified.clone()))?;

    let mut context = context::Context::new(queries);
    let modules = modules::Modules::collect(&mut context, file_id)?;
    reject_source_errors(queries, &modules)?;

    let indexed = queries.indexed(file_id)?;
    let (term, _) = indexed
        .items
        .iter_terms()
        .find(|(_, item)| item.name.as_deref() == Some(entry_name))
        .ok_or_else(|| GoError::MissingEntry(qualified.clone()))?;

    let substituted = types::Substituted::default();
    let mut specializer = Specializer::new(queries, foreign_packages, substituted);
    specializer.adopt_foreign_structs()?;
    specializer.adopt_native_foreigns()?;
    let entry = specializer.specialize_entry(file_id, term)?;
    if let Some(blockers) = specializer.blockers()? {
        return Err(GoError::Blocked(blockers));
    }
    let runtime_dictionary_notes = specializer.take_runtime_dictionary_notes();
    let erased_newtypes = std::mem::take(&mut specializer.context().erased_newtypes);
    let (functions, mut monotypes, next_local, thunk_parameters) = specializer.finish();
    monotypes.erased_newtypes = erased_newtypes;
    let program = monomorphic::Program { functions, entry };
    let eliminators = emit::Eliminators::find(&program, &monotypes);
    let coverage = foreign_packages.line_directives.as_ref().map(|directives| directives.coverage);
    let hash_operations = maps::hash_operations(&program, &monotypes, &modules, &mut context);
    let mut kept = maps::KeptOperations::new(&program, &hash_operations);
    let specialized = Specialized { program, next_local, thunk_parameters };
    let simplification = Simplification { coverage, modules: &modules, hash_operations };
    let program = simplification.simplify(specialized, &mut monotypes, &mut kept);
    let functions = program.functions.len();
    let inputs = emit::EmissionInputs {
        monotypes: &mut monotypes,
        eliminators: &eliminators,
        queries,
        foreign_packages,
        modules: &modules,
        module_path,
        kept: &kept,
    };
    let (files, notes) = emit::emit_program(program, inputs)?;
    let go_path = |path: &str| {
        let directives = foreign_packages.line_directives.as_ref()?;
        Some(std::path::Path::new(&directives.go_directory).join(path))
    };
    let mut files: Vec<(String, String)> = files
        .into_iter()
        .map(|file| {
            let path = go_path(&file.path);
            let (source, _) = file.file.render_at(path.as_deref(), coverage.unwrap_or_default());
            (file.path, source)
        })
        .collect();
    files.sort();
    let notes = runtime_dictionary_notes.into_iter().chain(notes).collect();
    Ok(GoProgram { files, functions, notes })
}

struct Specialized {
    program: monomorphic::Program,
    next_local: u32,
    thunk_parameters: FxHashSet<monomorphic::LocalId>,
}

impl Clone for Specialized {
    fn clone(&self) -> Self {
        let functions = self.program.functions.clone();
        Specialized {
            program: monomorphic::Program { functions, entry: self.program.entry },
            next_local: self.next_local,
            thunk_parameters: self.thunk_parameters.clone(),
        }
    }
}

struct Simplification<'a> {
    coverage: Option<LineCoverage>,
    modules: &'a modules::Modules,
    hash_operations: FxHashMap<monomorphic::FunctionId, maps::MapOperation>,
}

impl Simplification<'_> {
    fn simplify(
        &self,
        specialized: Specialized,
        monotypes: &mut monotype::Monotypes,
        kept: &mut maps::KeptOperations,
    ) -> monomorphic::Program {
        // The map operations stay calls through simplification only where a Go map does them; a
        // program whose maps all stay trees is simplified again from its unsimplified functions,
        // as if none were kept.
        let unsimplified = (!kept.is_empty()).then(|| specialized.clone());
        let calls_kept: FxHashSet<_> = self.hash_operations.keys().copied().collect();
        let simplified = self.simplify_and_merge(specialized, monotypes, &calls_kept, kept);
        let Some(unsimplified) = unsimplified else { return simplified };
        let operations = kept.find(&simplified, self.modules);
        let used = emit::hash_maps::operations_used(&simplified, monotypes, &operations);
        if used.len() == operations.len() {
            return simplified;
        }
        kept.retain(&used);
        let calls_kept: FxHashSet<_> = self
            .hash_operations
            .keys()
            .copied()
            .filter(|&id| kept.keeps(&unsimplified.program.function(id).name))
            .collect();
        self.simplify_and_merge(unsimplified, monotypes, &calls_kept, kept)
    }

    /// Simplifies the program and merges its identical functions, keeping the calls of the map
    /// operations that [`maps`] lets a Go map do.
    fn simplify_and_merge(
        &self,
        specialized: Specialized,
        monotypes: &mut monotype::Monotypes,
        calls_kept: &FxHashSet<monomorphic::FunctionId>,
        kept: &maps::KeptOperations,
    ) -> monomorphic::Program {
        let Specialized { program, next_local, thunk_parameters } = specialized;
        let program = simplify::simplify(
            program,
            monotypes,
            next_local,
            thunk_parameters,
            self.coverage,
            calls_kept,
        );
        merge::merge_identical_functions(program, self.modules, monotypes, kept)
    }
}

/// The module name a source file declares.
pub fn module_name(
    queries: &impl checking::ExternalQueries,
    file_id: files::FileId,
) -> Option<String> {
    let content = queries.content(file_id).ok()?;
    let (parsed, _) = queries.parsed(file_id).ok()?;
    parsed.module_name(&content).map(|name| name.to_string())
}

/// Specialization trusts the checker's types, so a module the checker rejected
/// would surface as a confusing representation error far from its cause.
fn reject_source_errors(
    queries: &impl checking::ExternalQueries,
    modules: &modules::Modules,
) -> GoResult<()> {
    let mut files = vec![];
    let mut module_names = vec![];
    for index in modules.indices() {
        let file = modules.file(index);
        if file == queries.prim_id() {
            continue;
        }
        if checking::has_frontend_errors(queries, file)? {
            files.push(file);
            module_names.push(modules.name(index).to_string());
        }
    }
    if files.is_empty() {
        return Ok(());
    }
    Err(GoError::SourceErrors { files, module_names })
}
