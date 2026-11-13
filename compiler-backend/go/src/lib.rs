//! Whole-program Go code generation from checked PureScript.
//!
//! The backend specializes the program from an entry point using the checker's
//! types and evidence, simplifies the resulting monomorphic tree, and renders it
//! as a single Go `main` package.

mod context;
mod dictionary;
mod emit;
pub mod error;
mod foreign;
mod mono;
mod monotype;
mod simplify;
mod specialize;
mod syntax;
mod types;

pub use error::{GoError, GoResult, UnsupportedState};
pub use foreign::ForeignPackages;

use crate::specialize::Specializer;

pub struct GoProgram {
    pub source: String,
    pub functions: usize,
}

pub fn compile_program(
    queries: &impl checking::ExternalQueries,
    entry_module: &str,
    entry_name: &str,
    foreign_packages: &ForeignPackages,
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

    let mut specializer = Specializer::new(queries, foreign_packages);
    let entry = specializer.specialize_entry(file_id, term)?;
    let (functions, mut monotypes, next_local) = specializer.finish();
    let program = mono::Program { functions, entry };
    let program = simplify::simplify(program, &mut monotypes, next_local);
    if std::env::var_os("IRIS_GO_DUMP").is_some() {
        for function in &program.functions {
            eprintln!("{function:#?}");
        }
    }
    let functions = program.functions.len();
    let source = emit::emit_program(&program, &mut monotypes, queries, foreign_packages)?;
    Ok(GoProgram { source, functions })
}
