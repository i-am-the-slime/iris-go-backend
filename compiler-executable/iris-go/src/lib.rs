//! Whole-program Go compilation of a Spago workspace.
//!
//! Loads and checks the workspace the way `iris dump-types` does, then hands the
//! checked modules to the Go backend, which specializes the program from the
//! entry point and writes `main.go`.

use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use iris_build::{BuildSession, BuildSessionConfig, ProjectConfig};

pub struct GoConfig {
    pub package: Option<String>,
    pub entry: String,
    pub destination: PathBuf,
    pub version: String,
}

pub fn run(config: GoConfig) -> Result<(), String> {
    let started = Instant::now();
    let (entry_module, entry_name) = config
        .entry
        .rsplit_once('.')
        .ok_or_else(|| format!("entry point {} is not qualified", config.entry))?;

    let scratch = tempfile::tempdir().map_err(|error| error.to_string())?;
    let output = Some(scratch.path().join("output"));
    let project = ProjectConfig { package: config.package, output, quiet: true };
    let project = iris_build::prepare_project(project).map_err(|error| error.to_string())?;
    let project = iris_build::initialize_project(project).map_err(|error| error.to_string())?;
    let session_config =
        BuildSessionConfig { color: false, diagnostics: false, version: config.version };
    let session = BuildSession::new(project, session_config).map_err(|error| error.to_string())?;
    let snapshot = session.snapshot();
    let loaded = started.elapsed();

    let program = go::compile_program(&snapshot.engine, entry_module, entry_name)
        .map_err(|error| error.to_string())?;
    fs::create_dir_all(&config.destination).map_err(|error| error.to_string())?;
    let path = config.destination.join("main.go");
    fs::write(&path, program.source).map_err(|error| error.to_string())?;
    eprintln!(
        "go: {} functions -> {} (load {:.0?}, total {:.0?})",
        program.functions,
        path.display(),
        loaded,
        started.elapsed()
    );
    Ok(())
}
