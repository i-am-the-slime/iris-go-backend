//! Whole-program Go compilation of a Spago workspace.
//!
//! Loads and checks the workspace the way `iris watch` does, then hands the
//! checked modules to the Go backend, which specializes the program from the
//! entry point and writes one Go package per PureScript module: the entry
//! module's as `main.go`, every other in a directory named after the module.
//! The destination's `go.mod` names the Go module those packages import each
//! other through.

use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use iris_build::{
    BuildSession, BuildSessionConfig, BuildStage, ProjectConfig, SessionSnapshot, SourceKind,
};

pub use go::LineCoverage;

pub struct GoConfig {
    pub package: Option<String>,
    pub entry: String,
    pub destination: PathBuf,
    pub version: String,
    /// Leaves out the summary of what was written.
    pub quiet: bool,
    /// Writes `//line` directives, which make Go's stack traces, debuggers and profiles name
    /// the PureScript the code comes from, on the lines the coverage says; none leaves them out.
    pub line_directives: Option<go::LineCoverage>,
}

mod program;
pub use program::{Program, ProgramConfig, RUNTIME_VERSION, build_program, run_program};

pub fn run(config: GoConfig) -> Result<(), String> {
    let started = Instant::now();
    let work_started = go::Work::so_far();
    let (entry_module, entry_name) = config
        .entry
        .rsplit_once('.')
        .ok_or_else(|| format!("entry point {} is not qualified", config.entry))?;

    let scratch = tempfile::tempdir().map_err(|error| error.to_string())?;
    let output = Some(scratch.path().join("output"));
    let project = ProjectConfig { package: config.package, output, quiet: true };
    let project = iris_build::prepare_project(project).map_err(|error| error.to_string())?;
    let project = iris_build::initialize_project(project, BuildStage::Checked)
        .map_err(|error| error.to_string())?;
    let session_config =
        BuildSessionConfig { color: false, diagnostics: false, version: config.version };
    let session = BuildSession::new(project, session_config).map_err(|error| error.to_string())?;
    let snapshot = session.snapshot();
    let loaded = started.elapsed();
    let load_work = go::Work::so_far().since(work_started);

    fs::create_dir_all(&config.destination).map_err(|error| error.to_string())?;
    let module_path = go_module_path(&config.destination)?;
    let mut foreign_packages =
        vendor_foreign_packages(&snapshot, &config.destination, &module_path)?;
    if let Some(coverage) = config.line_directives {
        let directives = line_directives(&snapshot, &config.destination, coverage)?;
        foreign_packages.line_directives = Some(directives);
    }
    let backend_started = go::Work::so_far();
    let program = go::compile_program(
        &snapshot.engine,
        entry_module,
        entry_name,
        &foreign_packages,
        &module_path,
    );
    let backend_work = go::Work::so_far().since(backend_started);
    let program = match program {
        Ok(program) => program,
        // The checker's own diagnostics say what is wrong and where.
        Err(go::GoError::SourceErrors { files, module_names }) => {
            session.report_diagnostics(&files).map_err(|error| error.to_string())?;
            return Err(go::GoError::SourceErrors { files, module_names }.to_string());
        }
        Err(error) => return Err(error.to_string()),
    };
    for note in &program.notes {
        eprintln!("go: note: {note}");
    }
    let files = program.files.len();
    for (path, source) in program.files {
        let path = config.destination.join(path);
        if let Some(directory) = path.parent() {
            fs::create_dir_all(directory).map_err(|error| error.to_string())?;
        }
        fs::write(&path, source).map_err(|error| error.to_string())?;
    }
    if config.quiet {
        return Ok(());
    }
    eprintln!(
        "go: {} functions in {files} files -> {} (load {:.0?}, {load_work}; backend \
         {backend_work}; total {:.0?}, {})",
        program.functions,
        config.destination.display(),
        loaded,
        started.elapsed(),
        go::Work::so_far().since(work_started)
    );
    Ok(())
}

/// The Go module path the destination's `go.mod` declares.
fn go_module_path(destination: &Path) -> Result<String, String> {
    let go_mod = destination.join("go.mod");
    let declaration = fs::read_to_string(&go_mod).map_err(|_| {
        format!(
            "{} must exist to name the Go module the generated packages share",
            go_mod.display()
        )
    })?;
    declaration
        .lines()
        .find_map(|line| line.trim().strip_prefix("module "))
        .map(|module| module.trim().to_string())
        .ok_or_else(|| format!("{} does not declare a module", go_mod.display()))
}

/// Copies the Go files next to each source file into a package of the program, named after its
/// module, as the JavaScript backend copies `Foo.js` beside `Foo.purs`.
fn vendor_foreign_packages(
    snapshot: &SessionSnapshot,
    destination: &Path,
    module_path: &str,
) -> Result<go::ForeignPackages, String> {
    let mut modules = vec![];
    let mut structs = vec![];
    let mut sources = vec![];
    let here = std::env::current_dir().map_err(|error| error.to_string())?;
    let here = dunce::canonicalize(&here).unwrap_or(here);
    for (file_id, file) in snapshot.files.iter() {
        if file.kind != SourceKind::Project {
            continue;
        }
        let foreign_files = go::foreign_files(&file.path).map_err(|error| error.to_string())?;
        if foreign_files.is_empty() {
            continue;
        }
        let module = go::module_name(&snapshot.engine, *file_id)
            .ok_or_else(|| format!("{} does not declare a module", file.path.display()))?;
        let mut source = go::ForeignSource { module: module.clone(), ..Default::default() };
        let package = destination.join(go::ForeignPackages::package_name(&module));
        fs::create_dir_all(&package).map_err(|error| error.to_string())?;
        for foreign_file in foreign_files {
            let text = fs::read_to_string(&foreign_file).map_err(|error| error.to_string())?;
            for name in go::foreign_structs(&text) {
                structs.push((module.clone(), name));
            }
            let (values, types) = go::foreign_declarations(&text);
            source.values.extend(values);
            source.types.extend(types);
            let shown = shown_path(&foreign_file, &here);
            source.files.push(shown.clone());
            let Some(name) = foreign_file.file_name() else { continue };
            fs::write(package.join(name), go::foreign_source(&module, &text))
                .map_err(|error| error.to_string())?;
            copy_embedded_files(Path::new(&shown), &text, &package)?;
        }
        modules.push(module);
        sources.push(source);
    }
    modules.sort();
    structs.sort();
    let source_paths = snapshot
        .files
        .iter()
        .filter(|(_, file)| file.kind == SourceKind::Project)
        .map(|(&file_id, file)| (file_id, shown_path(&file.path, &here)))
        .collect();
    let module_path = module_path.to_string();
    let line_directives = None;
    Ok(go::ForeignPackages {
        module_path,
        modules,
        structs,
        sources,
        source_paths,
        line_directives,
    })
}

/// The path as messages show it: relative to the working directory `here` when it is inside it,
/// with `/` between its components on every platform.
fn shown_path(path: &Path, here: &Path) -> String {
    let relative = path.strip_prefix(here).unwrap_or(path);
    relative.to_string_lossy().replace(std::path::MAIN_SEPARATOR, "/")
}

/// The absolute paths of the destination and of the source files, which `//line` directives
/// name relative to each other.
fn line_directives(
    snapshot: &SessionSnapshot,
    destination: &Path,
    coverage: go::LineCoverage,
) -> Result<go::LineDirectives, String> {
    let absolute = |path: &Path| dunce::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    let go_directory = absolute(destination).display().to_string();
    let sources = snapshot
        .files
        .iter()
        .filter(|(_, file)| file.kind == SourceKind::Project)
        .map(|(&file_id, file)| (file_id, absolute(&file.path).display().to_string()))
        .collect();
    Ok(go::LineDirectives { go_directory, sources, coverage })
}

/// Copies the files the foreign file embeds with `//go:embed` into its package, at the same
/// paths relative to it, so that the embed finds them there. A symbolic link is copied as the
/// file it points to.
fn copy_embedded_files(foreign_file: &Path, text: &str, package: &Path) -> Result<(), String> {
    let directory = foreign_file.parent().unwrap_or(Path::new(""));
    for relative in go::embedded_files(foreign_file, text).map_err(|error| error.to_string())? {
        let (from, to) = (directory.join(&relative), package.join(&relative));
        if let Some(parent) = to.parent() {
            fs::create_dir_all(parent).map_err(|error| error.to_string())?;
        }
        // Read and written rather than `fs::copy`, which would keep a read-only file's mode
        // and so fail to overwrite it on the next compilation.
        let contents = fs::read(&from)
            .map_err(|error| format!("could not read {}: {error}", from.display()))?;
        fs::write(&to, contents)
            .map_err(|error| format!("could not write {}: {error}", to.display()))?;
    }
    Ok(())
}
