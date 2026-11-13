//! Whole-program Go compilation of a Spago workspace.
//!
//! Loads and checks the workspace the way `iris dump-types` does, then hands the
//! checked modules to the Go backend, which specializes the program from the
//! entry point and writes `main.go`.

use std::fs;
use std::path::{Path, PathBuf};
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

    fs::create_dir_all(&config.destination).map_err(|error| error.to_string())?;
    let foreign_packages = vendor_foreign_packages(&config.destination)?;
    let program =
        go::compile_program(&snapshot.engine, entry_module, entry_name, &foreign_packages)
            .map_err(|error| error.to_string())?;
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

const FOREIGN_DIRECTORY: &str = "go-ffi";

fn vendor_foreign_packages(destination: &Path) -> Result<go::ForeignPackages, String> {
    let Ok(entries) = fs::read_dir(FOREIGN_DIRECTORY) else {
        return Ok(go::ForeignPackages::default());
    };
    let mut modules = vec![];
    for entry in entries {
        let path = entry.map_err(|error| error.to_string())?.path();
        if path.extension().and_then(|extension| extension.to_str()) != Some("go") {
            continue;
        }
        let Some(module) = path.file_stem().and_then(|stem| stem.to_str()) else { continue };
        let package = destination.join(go::ForeignPackages::package_name(module));
        fs::create_dir_all(&package).map_err(|error| error.to_string())?;
        fs::copy(&path, package.join("ffi.go")).map_err(|error| error.to_string())?;
        modules.push(module.to_string());
    }
    if modules.is_empty() {
        return Ok(go::ForeignPackages::default());
    }
    let go_mod = destination.join("go.mod");
    let declaration = fs::read_to_string(&go_mod).map_err(|_| {
        format!(
            "{} must exist to name the Go module of the {FOREIGN_DIRECTORY} packages",
            go_mod.display()
        )
    })?;
    let module_path = declaration
        .lines()
        .find_map(|line| line.trim().strip_prefix("module "))
        .map(|module| module.trim().to_string())
        .ok_or_else(|| format!("{} does not declare a module", go_mod.display()))?;
    Ok(go::ForeignPackages { module_path, modules })
}
