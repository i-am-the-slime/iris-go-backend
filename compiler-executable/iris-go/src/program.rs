//! Compiling a Spago package to a Go executable without any setup, for `iris run --go`.
//!
//! The Go module lives in `.spago/go/<package>/module/` with a `go.mod` Iris writes, requiring
//! the iris-go runtime this release targets. The executable is `.spago/go/<package>/bin/`, and
//! `go build` runs only when the generated Go, the `go.mod` or the build settings change.

use std::ffi::OsString;
use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::{env, fs};

use iris_build::Workspace;
use sha2::{Digest, Sha256};

use crate::GoConfig;

/// The release of github.com/i-am-the-slime/iris-go the generated Go is written against.
pub const RUNTIME_VERSION: &str = "v0.6.0";

/// The Go module path of the runtime.
const RUNTIME_MODULE: &str = "github.com/i-am-the-slime/iris-go";

/// Points the runtime at a local checkout instead of the published release.
const RUNTIME_CHECKOUT_VARIABLE: &str = "IRIS_GO";

/// The oldest Go that builds the runtime.
const MINIMUM_GO: &str = "1.27";

/// The experiment the runtime's string scanning uses when the environment names none.
const DEFAULT_EXPERIMENT: &str = "simd";

pub struct ProgramConfig {
    pub package: Option<String>,
    /// Qualified entry point; when absent, `main` in the package's configured `run.main` module,
    /// or in `Main`.
    pub entry: Option<String>,
    pub quiet: bool,
    pub version: String,
}

/// Compiles the package's entry point and runs the executable with `arguments`, or with the
/// package's configured `run.execArgs` when there are none. Returns the program's exit status.
pub fn run_program(config: ProgramConfig, arguments: Vec<String>) -> Result<i32, String> {
    let program = build_program(config)?;
    let arguments = if arguments.is_empty() { program.configured_arguments } else { arguments };
    let status = Command::new(&program.executable)
        .args(&arguments)
        .current_dir(&program.workspace_root)
        .status()
        .map_err(|error| format!("could not run {}: {error}", program.executable.display()))?;
    Ok(exit_code(status))
}

pub struct Program {
    pub executable: PathBuf,
    workspace_root: PathBuf,
    configured_arguments: Vec<String>,
}

/// Compiles the package's entry point to Go and builds the executable.
pub fn build_program(config: ProgramConfig) -> Result<Program, String> {
    require_go()?;
    let current_directory = env::current_dir().map_err(|error| error.to_string())?;
    let workspace = Workspace::discover(&current_directory, config.package.as_deref())
        .map_err(|error| error.to_string())?;
    let package = workspace.require_selected().map_err(|error| error.to_string())?;
    let name = workspace.selected.clone().expect("invariant violated: a package is selected");
    let execution = package.manifest.run.clone().unwrap_or_default();
    let entry = config
        .entry
        .unwrap_or_else(|| format!("{}.main", execution.main.as_deref().unwrap_or("Main")));

    let cache = workspace.root.join(".spago").join("go").join(&name);
    let module = cache.join("module");
    clear_generated(&module)?;
    write(&module.join("go.mod"), &go_mod(&name)?)?;
    crate::run(GoConfig {
        package: Some(name.clone()),
        entry,
        destination: PathBuf::clone(&module),
        version: config.version,
        quiet: config.quiet,
        line_directives: Some(crate::LineCoverage::Sparse),
    })?;

    let executable = cache.join("bin").join(format!("{name}{}", env::consts::EXE_SUFFIX));
    let fingerprint = fingerprint(&module)?;
    let recorded = cache.join("fingerprint");
    let unchanged = fs::read_to_string(&recorded).is_ok_and(|recorded| recorded == fingerprint);
    if !(unchanged && executable.is_file()) {
        go_build(&module, &executable)?;
        write(&recorded, &fingerprint)?;
    }
    Ok(Program {
        executable,
        workspace_root: workspace.root.clone(),
        configured_arguments: execution.exec_args,
    })
}

/// Fails with what to install when `go` is not on `PATH`.
fn require_go() -> Result<(), String> {
    match Command::new("go").arg("version").output() {
        Ok(_) => Ok(()),
        Err(error) if error.kind() == ErrorKind::NotFound => Err(format!(
            "`go` was not found on PATH; running a program with the Go backend needs Go \
             {MINIMUM_GO} or later from https://go.dev/dl/"
        )),
        Err(error) => Err(format!("could not run `go version`: {error}")),
    }
}

/// Removes the previous compilation's Go, keeping `go.sum`, so packages and foreign files the
/// program no longer has do not linger in the build.
fn clear_generated(module: &Path) -> Result<(), String> {
    let entries = match fs::read_dir(module) {
        Ok(entries) => entries,
        Err(error) if error.kind() == ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(format!("could not read {}: {error}", module.display())),
    };
    for entry in entries {
        let path = entry.map_err(|error| error.to_string())?.path();
        if path.file_name().is_some_and(|name| name == "go.sum") {
            continue;
        }
        let removed =
            if path.is_dir() { fs::remove_dir_all(&path) } else { fs::remove_file(&path) };
        removed.map_err(|error| format!("could not remove {}: {error}", path.display()))?;
    }
    Ok(())
}

/// The `go.mod` of the package's Go module, which requires the runtime release, or replaces it
/// with the checkout `IRIS_GO` names.
pub(crate) fn go_mod(package: &str) -> Result<String, String> {
    let mut go_mod = format!(
        "module iris.local/{package}\n\ngo {MINIMUM_GO}.0\n\nrequire {RUNTIME_MODULE} \
         {RUNTIME_VERSION}\n"
    );
    if let Some(checkout) = env::var_os(RUNTIME_CHECKOUT_VARIABLE).filter(|path| !path.is_empty()) {
        let checkout = runtime_checkout(&checkout)?;
        go_mod.push_str(&format!("\nreplace {RUNTIME_MODULE} => {}\n", checkout.display()));
    }
    Ok(go_mod)
}

fn runtime_checkout(checkout: &OsString) -> Result<PathBuf, String> {
    let shown = Path::new(checkout).display();
    let checkout = dunce::canonicalize(checkout).map_err(|error| {
        format!("{RUNTIME_CHECKOUT_VARIABLE}={shown} is not a directory: {error}")
    })?;
    if !checkout.join("go.mod").is_file() {
        return Err(format!(
            "{RUNTIME_CHECKOUT_VARIABLE}={shown} is not an iris-go checkout: it has no go.mod"
        ));
    }
    Ok(checkout)
}

/// Builds the module's main package into `executable`, printing Go's own errors.
fn go_build(module: &Path, executable: &Path) -> Result<(), String> {
    let status = Command::new("go")
        .arg("build")
        .args(build_flags())
        .arg("-o")
        .arg(executable)
        .arg(".")
        .env("GOEXPERIMENT", experiment())
        .current_dir(module)
        .status()
        .map_err(|error| format!("could not run `go build`: {error}"))?;
    if !status.success() {
        return Err(format!("`go build` failed in {}", module.display()));
    }
    Ok(())
}

/// `-mod=mod` lets Go record the runtime's checksum in `go.sum` on the first build.
/// Without DWARF, which Go would generate only for the linker to drop, linking takes half as
/// long.
fn build_flags() -> [&'static str; 4] {
    ["-buildvcs=false", "-mod=mod", "-gcflags=all=-dwarf=false", "-ldflags=-w"]
}

fn experiment() -> String {
    env::var("GOEXPERIMENT").unwrap_or_else(|_| DEFAULT_EXPERIMENT.to_string())
}

/// A digest of every file in the module, `go.sum` excepted, and of the build settings.
fn fingerprint(module: &Path) -> Result<String, String> {
    let mut files = vec![];
    collect_files(module, &mut files)?;
    files.sort();
    let mut digest = Sha256::new();
    for setting in build_flags() {
        digest.update(setting.as_bytes());
        digest.update([0]);
    }
    digest.update(experiment().as_bytes());
    for file in files {
        if file.file_name().is_some_and(|name| name == "go.sum") {
            continue;
        }
        let contents = fs::read(&file)
            .map_err(|error| format!("could not read {}: {error}", file.display()))?;
        let relative = file.strip_prefix(module).unwrap_or(&file);
        digest.update([0]);
        digest.update(relative.as_os_str().as_encoded_bytes());
        digest.update([0]);
        digest.update((contents.len() as u64).to_le_bytes());
        digest.update(&contents);
    }
    Ok(digest.finalize().iter().map(|byte| format!("{byte:02x}")).collect())
}

fn collect_files(directory: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = fs::read_dir(directory)
        .map_err(|error| format!("could not read {}: {error}", directory.display()))?;
    for entry in entries {
        let path = entry.map_err(|error| error.to_string())?.path();
        if path.is_dir() {
            collect_files(&path, files)?;
        } else {
            files.push(path);
        }
    }
    Ok(())
}

fn write(path: &Path, contents: &str) -> Result<(), String> {
    if let Some(directory) = path.parent() {
        fs::create_dir_all(directory)
            .map_err(|error| format!("could not create {}: {error}", directory.display()))?;
    }
    fs::write(path, contents)
        .map_err(|error| format!("could not write {}: {error}", path.display()))
}

/// The program's exit status, or 128 plus the signal that ended it, as shells report it.
fn exit_code(status: ExitStatus) -> i32 {
    if let Some(code) = status.code() {
        return code;
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = status.signal() {
            return 128 + signal;
        }
    }
    1
}
