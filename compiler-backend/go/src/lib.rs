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
mod timing;
mod types;

pub use emit::{KERNEL_FILE_SUFFIXES, is_kernel_file};
pub use error::{GoError, GoResult, UnsupportedState};
pub use foreign::{
    EmbedError, ForeignPackages, ForeignSource, LineCoverage, LineDirectives, embedded_files,
    foreign_declarations, foreign_files, foreign_forwarders, foreign_opacity, foreign_source,
    foreign_structs, recovers, uses_event_loop,
};
pub use timing::Work;

use crate::specialize::Specializer;
use crate::timing::timed;
use rustc_hash::FxHashSet;

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
    let entry = timed("specialize", || specializer.specialize_entry(file_id, term))?;
    if let Some(blockers) = specializer.blockers()? {
        return Err(GoError::Blocked(blockers));
    }
    let runtime_dictionary_notes = specializer.take_runtime_dictionary_notes();
    let erased_newtypes = std::mem::take(&mut specializer.context().erased_newtypes);
    let (functions, mut monotypes, next_local, thunk_parameters) =
        timed("finish specialization", || specializer.finish());
    monotypes.erased_newtypes = erased_newtypes;
    let program = monomorphic::Program { functions, entry };
    let eliminators = emit::Eliminators::find(&program, &monotypes);
    let coverage = foreign_packages.line_directives.as_ref().map(|directives| directives.coverage);
    let hash_operations = maps::hash_operations(&program, &monotypes, &modules, &mut context);
    let mut kept = maps::KeptOperations::new(&program, &hash_operations);
    // The map operations stay calls through simplification only where a Go map does them; a
    // program whose maps all stay trees is simplified again from its unsimplified functions,
    // as if none were kept.
    let unsimplified = (!kept.is_empty()).then(|| {
        let functions = program.functions.clone();
        (monomorphic::Program { functions, entry: program.entry }, thunk_parameters.clone())
    });
    let calls_kept: FxHashSet<_> = hash_operations.keys().copied().collect();
    let simplified = simplify_and_merge(
        program,
        &mut monotypes,
        (next_local, thunk_parameters, coverage),
        &calls_kept,
        &modules,
        &kept,
    );
    let program = match unsimplified {
        None => simplified,
        Some((unsimplified, thunk_parameters)) => {
            let operations = kept.find(&simplified, &modules);
            let used = emit::hash_map_operations_used(&simplified, &monotypes, &operations);
            if used.len() == operations.len() {
                simplified
            } else {
                kept.retain(&used);
                let calls_kept: FxHashSet<_> = hash_operations
                    .keys()
                    .copied()
                    .filter(|&id| kept.keeps(&unsimplified.function(id).name))
                    .collect();
                simplify_and_merge(
                    unsimplified,
                    &mut monotypes,
                    (next_local, thunk_parameters, coverage),
                    &calls_kept,
                    &modules,
                    &kept,
                )
            }
        }
    };
    if std::env::var_os("IRIS_GO_DUMP").is_some() {
        for function in &program.functions {
            eprintln!("{function:#?}");
        }
        monotypes.dump();
    }
    let functions = program.functions.len();
    let (files, notes) = timed("emit", || {
        emit::emit_program(
            program,
            &mut monotypes,
            &eliminators,
            queries,
            foreign_packages,
            &modules,
            module_path,
            &kept,
        )
    })?;
    let go_path = |path: &str| {
        let directives = foreign_packages.line_directives.as_ref()?;
        Some(std::path::Path::new(&directives.go_directory).join(path))
    };
    let coverage = foreign_packages.line_directives.as_ref().map(|directives| directives.coverage);
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

/// Simplifies the program and merges its identical functions, keeping the calls of the map
/// operations that [`maps`] lets a Go map do.
fn simplify_and_merge(
    program: monomorphic::Program,
    monotypes: &mut monotype::Monotypes,
    (next_local, thunk_parameters, coverage): (
        u32,
        FxHashSet<monomorphic::LocalId>,
        Option<LineCoverage>,
    ),
    calls_kept: &FxHashSet<monomorphic::FunctionId>,
    modules: &modules::Modules,
    kept: &maps::KeptOperations,
) -> monomorphic::Program {
    let program = timed("simplify", || {
        simplify::simplify(program, monotypes, next_local, thunk_parameters, coverage, calls_kept)
    });
    timed("merge", || merge::merge_identical_functions(program, modules, monotypes, kept))
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
