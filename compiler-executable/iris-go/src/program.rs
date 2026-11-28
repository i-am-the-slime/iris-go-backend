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

use iris_build::{Workspace, WorkspacePackage};
use sha2::{Digest, Sha256};

use crate::{GoConfig, requirements};

/// The release of github.com/i-am-the-slime/iris-go the generated Go is written against.
pub const RUNTIME_VERSION: &str = "v0.9.1";

/// The Go module path of the runtime.
pub(crate) const RUNTIME_MODULE: &str = "github.com/i-am-the-slime/iris-go";

/// Points the runtime at a local checkout instead of the published release.
const RUNTIME_CHECKOUT_VARIABLE: &str = "IRIS_GO";

/// The oldest Go that builds the runtime.
const MINIMUM_GO: &str = "1.27";

/// The experiment the runtime's string scanning uses when the environment names none.
const DEFAULT_EXPERIMENT: &str = "simd";

/// The name of the CPU profile `--profile` keeps next to the generated module.
const RECORDED_PROFILE: &str = "default.pgo";

/// The CPU profile `go build` optimises the executable for.
pub enum Pgo {
    /// The profile the last `--profile` run recorded, when there is one.
    Recorded,
    Off,
    File(PathBuf),
}

pub struct ProgramConfig {
    pub package: Option<String>,
    /// Qualified entry point; when absent, `main` in the package's configured `run.main` module,
    /// or in `Main`.
    pub entry: Option<String>,
    pub quiet: bool,
    pub version: String,
    pub pgo: Pgo,
    /// Runs the program once with these arguments, or with `run.execArgs` when there are none,
    /// while recording a CPU profile, then builds it again optimised for that profile.
    pub profile: Option<Vec<String>>,
    /// Builds the package's tests, `main` in its configured `test.main` module or in
    /// `Test.Main`, with `test.execArgs`, instead of its program.
    pub tests: bool,
}

/// Compiles the package's entry point and runs the executable with `arguments`, or with the
/// package's configured `run.execArgs` when there are none. Returns the program's exit status.
/// With `profile`, the profiled run is the run.
pub fn run_program(config: ProgramConfig, arguments: Vec<String>) -> Result<i32, String> {
    let program = build_program(config)?;
    if let Some(status) = program.profiled_status {
        return Ok(status);
    }
    let arguments = if arguments.is_empty() { &program.configured_arguments } else { &arguments };
    let mut child = Command::new(&program.executable)
        .args(arguments)
        .current_dir(&program.workspace_root)
        .spawn()
        .map_err(|error| format!("could not run {}: {error}", program.executable.display()))?;
    drop(program);
    let status = child.wait().map_err(|error| format!("could not run the program: {error}"))?;
    Ok(exit_code(status))
}

pub struct Program {
    pub executable: PathBuf,
    workspace_root: PathBuf,
    configured_arguments: Vec<String>,
    /// The exit status of the run that recorded the profile, when there was one.
    pub profiled_status: Option<i32>,
    _cache_lock: CacheLock,
}

/// Compiles the package's entry point to Go and builds the executable.
pub fn build_program(config: ProgramConfig) -> Result<Program, String> {
    require_go()?;
    let current_directory = env::current_dir().map_err(|error| error.to_string())?;
    let workspace = Workspace::discover(&current_directory, config.package.as_deref())
        .map_err(|error| error.to_string())?
        .select_root_package_by_default();
    let package = workspace.require_selected().map_err(|error| error.to_string())?;
    let name = workspace.selected.clone().expect("invariant violated: a package is selected");
    let execution = if config.tests { tests(package)? } else { program(package) };
    let entry = config.entry.unwrap_or_else(|| format!("{}.main", execution.main));

    let cache = workspace.root.join(".spago").join("go").join(&name);
    // The tests get their own module and executable, so switching between running the program
    // and its tests does not build either again.
    let cache = if config.tests { cache.join("test") } else { cache };
    let cache_lock = CacheLock::acquire(&cache)?;
    let module = cache.join("module");
    let previous_requirements = previous_requirements(&module)?;
    clear_generated(&module)?;
    let fresh = go_mod(&name)?;
    let declaration = requirements::with_requirements(&fresh, &previous_requirements);
    write(&module.join("go.mod"), &declaration.unwrap_or(fresh))?;
    crate::run(GoConfig {
        package: Some(name.clone()),
        entry,
        destination: PathBuf::clone(&module),
        version: config.version,
        quiet: true,
        verbose: false,
        line_directives: Some(crate::LineCoverage::Sparse),
    })?;

    let recorded_profile = cache.join(RECORDED_PROFILE);
    let profiled_status = match config.profile {
        Some(arguments) => {
            let arguments = if arguments.is_empty() { &execution.exec_args } else { &arguments };
            let run =
                ProfiledRun { module: &module, cache: &cache, arguments, root: &workspace.root };
            Some(record_profile(run, &recorded_profile)?)
        }
        None => None,
    };
    let profile = match config.pgo {
        Pgo::Recorded => recorded_profile.is_file().then_some(recorded_profile),
        Pgo::Off => None,
        Pgo::File(profile) => Some(dunce::canonicalize(&profile).map_err(|error| {
            format!("could not read the profile {}: {error}", profile.display())
        })?),
    };

    let executable = cache.join("bin").join(format!("{name}{}", env::consts::EXE_SUFFIX));
    let fingerprint = fingerprint(&module, profile.as_deref())?;
    let recorded = cache.join("fingerprint");
    let unchanged = fs::read_to_string(&recorded).is_ok_and(|recorded| recorded == fingerprint);
    if !(unchanged && executable.is_file()) {
        go_build(&module, &executable, profile.as_deref())?;
        write(&recorded, &fingerprint)?;
    }
    Ok(Program {
        executable,
        workspace_root: workspace.root.clone(),
        configured_arguments: execution.exec_args,
        profiled_status,
        _cache_lock: cache_lock,
    })
}

/// The module whose `main` a build runs, and the arguments it runs with when it is given none.
struct Execution {
    main: String,
    exec_args: Vec<String>,
}

/// The package's program, from its `run` configuration.
fn program(package: &WorkspacePackage) -> Execution {
    let run = package.manifest.run.clone().unwrap_or_default();
    Execution { main: run.main.unwrap_or_else(|| "Main".to_string()), exec_args: run.exec_args }
}

/// The package's tests, from its `test` configuration, as `googoo test --js` finds them.
fn tests(package: &WorkspacePackage) -> Result<Execution, String> {
    if !package.has_tests {
        return Err("no selected packages contain tests".to_string());
    }
    Ok(match package.manifest.test.clone() {
        Some(test) => Execution { main: test.main, exec_args: test.exec_args },
        None => Execution { main: "Test.Main".to_string(), exec_args: vec![] },
    })
}

/// A run of the program that records where it spends its time.
struct ProfiledRun<'a> {
    module: &'a Path,
    cache: &'a Path,
    arguments: &'a [String],
    root: &'a Path,
}

/// Builds the program with a `main` that records a CPU profile around the generated one, runs
/// it, and keeps the profile at `destination`. Returns the run's exit status. The generated
/// functions keep their names, so `go build -pgo` finds them in the profile.
fn record_profile(run: ProfiledRun, destination: &Path) -> Result<i32, String> {
    let main = run.module.join("main.go");
    let generated = fs::read_to_string(&main)
        .map_err(|error| format!("could not read {}: {error}", main.display()))?;
    let renamed = generated.replacen("\nfunc main() {\n", "\nfunc irisProfiledMain() {\n", 1);
    if renamed == generated {
        return Err(format!("{} has no main function to profile", main.display()));
    }
    let wrapper = run.module.join("iris_profile.go");
    let profiler = run.cache.join("profiling").join(format!("program{}", env::consts::EXE_SUFFIX));
    write(&main, &renamed)?;
    write(&wrapper, PROFILING_MAIN)?;
    let built = go_build(run.module, &profiler, None);
    write(&main, &generated)?;
    fs::remove_file(&wrapper)
        .map_err(|error| format!("could not remove {}: {error}", wrapper.display()))?;
    built?;

    let profile = run.cache.join("profiling").join(RECORDED_PROFILE);
    let _ = fs::remove_file(&profile);
    let status = Command::new(&profiler)
        .args(run.arguments)
        .env(PROFILE_VARIABLE, &profile)
        .current_dir(run.root)
        .status()
        .map_err(|error| format!("could not run {}: {error}", profiler.display()))?;
    if !fs::metadata(&profile).is_ok_and(|metadata| metadata.len() > 0) {
        return Err(format!(
            "the profiled run exited with status {} before returning from main, so it left no \
             profile",
            exit_code(status)
        ));
    }
    fs::rename(&profile, destination)
        .map_err(|error| format!("could not write {}: {error}", destination.display()))?;
    Ok(exit_code(status))
}

/// Where the profiling `main` writes the profile.
const PROFILE_VARIABLE: &str = "IRIS_GO_CPU_PROFILE";

const PROFILING_MAIN: &str = r#"package main

import (
	"os"
	"runtime/pprof"
)

var irisProfiling bool

func main() {
	if irisProfiling {
		irisProfiledMain()
		return
	}
	irisProfiling = true
	profile, err := os.Create(os.Getenv("IRIS_GO_CPU_PROFILE"))
	if err != nil {
		panic(err)
	}
	if err := pprof.StartCPUProfile(profile); err != nil {
		panic(err)
	}
	irisProfiledMain()
	pprof.StopCPUProfile()
	if err := profile.Close(); err != nil {
		panic(err)
	}
}
"#;

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

struct CacheLock {
    _file: fs::File,
}

impl CacheLock {
    fn acquire(cache: &Path) -> Result<CacheLock, String> {
        fs::create_dir_all(cache)
            .map_err(|error| format!("could not create {}: {error}", cache.display()))?;
        let path = cache.join("lock");
        let file = fs::OpenOptions::new()
            .create(true)
            .truncate(false)
            .write(true)
            .open(&path)
            .map_err(|error| format!("could not open {}: {error}", path.display()))?;
        file.lock().map_err(|error| format!("could not lock {}: {error}", path.display()))?;
        Ok(CacheLock { _file: file })
    }
}

fn previous_requirements(module: &Path) -> Result<Vec<requirements::Requirement>, String> {
    let go_mod = module.join("go.mod");
    let declaration = match fs::read_to_string(&go_mod) {
        Ok(declaration) => declaration,
        Err(error) if error.kind() == ErrorKind::NotFound => return Ok(vec![]),
        Err(error) => return Err(format!("could not read {}: {error}", go_mod.display())),
    };
    let requirements = requirements::requirements(&declaration).into_iter();
    Ok(requirements.filter(|requirement| requirement.module != RUNTIME_MODULE).collect())
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
fn go_build(module: &Path, executable: &Path, profile: Option<&Path>) -> Result<(), String> {
    let status = Command::new("go")
        .arg("build")
        .args(build_flags())
        .args(profile.map(|profile| format!("-pgo={}", profile.display())))
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

/// A digest of every file in the module, `go.sum` excepted, and of the build settings and
/// profile.
fn fingerprint(module: &Path, profile: Option<&Path>) -> Result<String, String> {
    let mut files = vec![];
    collect_files(module, &mut files)?;
    files.sort();
    let mut digest = Sha256::new();
    for setting in build_flags() {
        digest.update(setting.as_bytes());
        digest.update([0]);
    }
    digest.update(experiment().as_bytes());
    if let Some(profile) = profile {
        let contents = fs::read(profile)
            .map_err(|error| format!("could not read {}: {error}", profile.display()))?;
        digest.update(b"\0pgo\0");
        digest.update((contents.len() as u64).to_le_bytes());
        digest.update(&contents);
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_build_waits_for_the_build_that_holds_its_cache() {
        let cache = tempfile::tempdir().unwrap();
        let held = CacheLock::acquire(cache.path()).unwrap();
        let other = fs::OpenOptions::new().write(true).open(cache.path().join("lock")).unwrap();
        assert!(matches!(other.try_lock(), Err(fs::TryLockError::WouldBlock)));
        drop(held);
        assert!(other.try_lock().is_ok());
    }
}
