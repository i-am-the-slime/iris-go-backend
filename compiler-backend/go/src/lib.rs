//! Whole-program Go code generation from checked PureScript.
//!
//! The backend specializes the program from an entry point using the checker's
//! types and evidence, simplifies the resulting monomorphic tree, and renders it
//! as one Go package per PureScript module, the entry module's being `main`.

mod arity;
mod blocker;
mod context;
mod dictionary;
mod emit;
mod erasure;
mod error;
mod foreign;
mod graph;
mod lift;
mod merge;
mod modules;
mod mono;
mod monotype;
mod naming;
mod primitives;
mod scheme;
mod simplify;
mod specialize;
mod suspension;
mod syntax;
mod timing;
mod types;
mod walk;

pub use error::{GoError, GoResult, UnsupportedState};
pub use foreign::{
    EmbedError, ForeignPackages, ForeignSource, LineDirectives, embedded_files,
    foreign_declarations, foreign_files, foreign_source, foreign_structs,
};
pub use timing::Work;

use crate::specialize::Specializer;
use crate::timing::timed;

pub struct GoProgram {
    /// Each Go source file, by its path relative to the output directory, in
    /// order of path.
    pub files: Vec<(String, String)>,
    pub functions: usize,
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
    let indexed = queries.indexed(file_id)?;
    let (term, _) = indexed
        .items
        .iter_terms()
        .find(|(_, item)| item.name.as_deref() == Some(entry_name))
        .ok_or_else(|| GoError::MissingEntry(qualified.clone()))?;

    let mut context = context::Context::new(queries);
    let modules = modules::Modules::collect(&mut context, file_id)?;
    reject_source_errors(queries, &modules)?;

    let substituted = types::Substituted::default();
    let mut specializer = Specializer::new(queries, foreign_packages, substituted);
    specializer.adopt_foreign_structs()?;
    let entry = timed("specialize", || specializer.specialize_entry(file_id, term))?;
    if let Some(blockers) = specializer.blockers()? {
        return Err(GoError::Blocked(blockers));
    }
    let erased_newtypes = std::mem::take(&mut specializer.context().erased_newtypes);
    let (functions, mut monotypes, next_local, thunk_parameters) =
        timed("finish specialization", || specializer.finish());
    monotypes.erased_newtypes = erased_newtypes;
    let program = mono::Program { functions, entry };
    let eliminators = emit::Eliminators::find(&program, &monotypes);
    let program = timed("simplify", || {
        simplify::simplify(program, &mut monotypes, next_local, thunk_parameters)
    });
    let program =
        timed("merge", || merge::merge_identical_functions(program, &modules, &mut monotypes));
    if std::env::var_os("IRIS_GO_DUMP").is_some() {
        for function in &program.functions {
            eprintln!("{function:#?}");
        }
        monotypes.dump();
    }
    let functions = program.functions.len();
    let files = timed("emit", || {
        emit::emit_program(
            program,
            &mut monotypes,
            &eliminators,
            queries,
            foreign_packages,
            &modules,
            module_path,
        )
    })?;
    let go_path = |path: &str| {
        let directives = foreign_packages.line_directives.as_ref()?;
        Some(std::path::Path::new(&directives.go_directory).join(path))
    };
    let mut files: Vec<(String, String)> = files
        .into_iter()
        .map(|file| {
            let (source, _) = file.file.render_at(go_path(&file.path).as_deref());
            (file.path, source)
        })
        .collect();
    files.sort();
    Ok(GoProgram { files, functions })
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
        if checking::has_source_errors(queries, file)?
            || checking::has_checking_errors(queries, file)?
        {
            files.push(file);
            module_names.push(modules.name(index).to_string());
        }
    }
    if files.is_empty() {
        return Ok(());
    }
    Err(GoError::SourceErrors { files, module_names })
}
