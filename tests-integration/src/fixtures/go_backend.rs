use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;
use std::{env, io};

use itertools::Itertools;
use process_control::{ChildExt, Control};
use url::Url;

use super::{
    FixtureFailure, FixtureResult, check_source_errors, fixture_folder, invalid_data, module_name,
    snapshot_path, updates_snapshots,
};

pub fn go(path: &Path) -> FixtureResult {
    let folder = fixture_folder(path)?;
    let file = module_name(path)?;
    let (compiled, vendored) = compile_go_fixture(path)?;
    // Built before the snapshot is compared, so that Go that does not build is never accepted.
    if let Ok(program) = &compiled {
        build_go_fixture(&program.files, &vendored)?;
    }
    let output = rendered_go_fixture(compiled)?;
    let mut settings = insta::Settings::clone_current();
    settings.set_snapshot_path(snapshot_path(folder));
    settings.set_prepend_module_to_snapshot(false);
    settings.set_omit_expression(true);
    settings.bind(|| insta::assert_snapshot!(file, output));

    Ok(())
}

pub fn go_output(path: &Path) -> FixtureResult<String> {
    let (compiled, _) = compile_go_fixture(path)?;
    rendered_go_fixture(compiled)
}

fn compile_go_fixture(path: &Path) -> FixtureResult<(go::GoResult<go::GoProgram>, VendoredFiles)> {
    let folder = fixture_folder(path)?;
    let file = module_name(path)?;
    let loaded = crate::load_fixture(folder)?;
    check_source_errors(&loaded.engine, &loaded.files, &loaded.fixture_files)?;

    let (foreign_packages, vendored) = go_foreign_packages(&loaded, folder)?;
    let compiled = go::compile_program(&loaded.engine, &file, "main", &foreign_packages, "fixture");
    Ok((compiled, vendored))
}

fn rendered_go_fixture(compiled: go::GoResult<go::GoProgram>) -> FixtureResult<String> {
    let output = match compiled {
        // Each package's file follows its path, in order of path.
        Ok(program) => program
            .files
            .iter()
            .map(|(path, source)| format!("// {path}\n{source}"))
            .chain(program.notes.iter().map(|note| format!("// note: {note}\n")))
            .collect::<Vec<_>>()
            .join("\n"),
        Err(go::GoError::Blocked(blockers)) => blockers.to_string(),
        Err(
            error @ (go::GoError::SharedRecordStruct { .. } | go::GoError::RepresentationChange(_)),
        ) => error.to_string(),
        Err(error) => return Err(error.into()),
    };
    Ok(output)
}

/// Files copied into a generated Go module, by their path inside it.
type VendoredFiles = Vec<(PathBuf, Vec<u8>)>;

/// The modules whose foreign imports a fixture's Go files next to their sources implement, as the
/// Go backend's CLI finds them, and those files as the CLI copies them into the program's module.
fn go_foreign_packages(
    loaded: &crate::LoadedFixture,
    folder: &Path,
) -> Result<(go::ForeignPackages, VendoredFiles), io::Error> {
    let root = snapshot_path(folder);
    let mut modules = vec![];
    let mut structs = vec![];
    let mut sources = vec![];
    let mut source_paths = vec![];
    let mut vendored = vec![];
    for &file_id in &loaded.fixture_files {
        let uri = loaded.files.path(file_id);
        let Some(path) = Url::parse(&uri).ok().and_then(|url| url.to_file_path().ok()) else {
            continue;
        };
        let shown = path.strip_prefix(&root).unwrap_or(&path);
        source_paths.push((file_id, shown.display().to_string()));
        let foreign_files = go::foreign_files(&path)?;
        if foreign_files.is_empty() {
            continue;
        }
        let Some(module) = go::module_name(&loaded.engine, file_id) else { continue };
        let mut source = go::ForeignSource { module: module.clone(), ..Default::default() };
        let mut texts = vec![];
        for foreign_file in foreign_files {
            let text = std::fs::read_to_string(&foreign_file)?;
            for name in go::foreign_structs(&text) {
                structs.push((module.clone(), name));
            }
            let (values, types) = go::foreign_declarations(&text);
            source.values.extend(values);
            source.types.extend(types);
            source.forwarders.extend(go::foreign_forwarders(&text));
            source.uses_event_loop |= go::uses_event_loop(&text);
            source.recovers |= go::recovers(&text);
            let shown = foreign_file.strip_prefix(&root).unwrap_or(&foreign_file);
            source.files.push(shown.display().to_string());
            vendored.extend(vendored_foreign_file(&module, &foreign_file, &text)?);
            texts.push(text);
        }
        let texts: Vec<&str> = texts.iter().map(String::as_str).collect();
        source.opacity = go::foreign_opacity(&texts);
        modules.push(module);
        sources.push(source);
    }
    modules.sort();
    structs.sort();
    sources.sort_by(|left, right| left.module.cmp(&right.module));
    let module_path = "fixture".to_string();
    // Directives would change every other fixture's Go, so only the fixtures about them have them.
    let name = folder.file_name().map(|name| name.to_string_lossy().into_owned());
    let coverage = match name.as_deref() {
        Some(name) if name.ends_with("_line_directives") => Some(go::LineCoverage::Sparse),
        Some(name) if name.ends_with("_line_directives_every") => Some(go::LineCoverage::Every),
        _ => None,
    };
    let line_directives = coverage.map(|coverage| go::LineDirectives {
        go_directory: String::new(),
        sources: source_paths.clone(),
        coverage,
    });
    let packages = go::ForeignPackages {
        module_path,
        modules,
        structs,
        sources,
        source_paths,
        line_directives,
    };
    Ok((packages, vendored))
}

/// The foreign file renamed into its module's package, and the files it embeds beside it.
fn vendored_foreign_file(
    module: &str,
    foreign_file: &Path,
    text: &str,
) -> Result<Vec<(PathBuf, Vec<u8>)>, io::Error> {
    let package = PathBuf::from(go::ForeignPackages::package_name(module));
    let name = foreign_file.file_name().ok_or_else(|| {
        invalid_data(format!("foreign file has no name: {}", foreign_file.display()))
    })?;
    let mut files = vec![(package.join(name), go::foreign_source(module, text).into_bytes())];
    let directory = foreign_file.parent().unwrap_or(Path::new(""));
    let embedded = go::embedded_files(foreign_file, text);
    let embedded = embedded.map_err(|error| invalid_data(error.to_string()))?;
    for relative in embedded {
        files.push((package.join(&relative), std::fs::read(directory.join(&relative))?));
    }
    Ok(files)
}

/// Whether the Go fixtures build their Go: `require` fails a run that cannot, `skip` never builds,
/// and by default a run without Go warns and only compares snapshots.
const GO_BUILD_VARIABLE: &str = "IRIS_GO_FIXTURE_BUILD";

/// The iris-go checkout the fixtures build against, by default `iris-go` beside this repository.
const GO_RUNTIME_VARIABLE: &str = "IRIS_GO";

/// How many fixtures build their Go at once, across nextest's test processes.
const GO_JOBS_VARIABLE: &str = "IRIS_GO_FIXTURE_JOBS";

const GO_RUNTIME_MODULE: &str = "github.com/i-am-the-slime/iris-go";
const GO_RUNTIME_VERSION: &str = "v0.9.3";

const WASM: (&str, &str) = ("js", "wasm");

/// Writes the program and its foreign files into a Go module that requires the runtime checkout
/// and vets it with `GOEXPERIMENT=simd`, as `iris run --go` builds, and again without the
/// experiment and for WebAssembly when the program has SIMD kernels, so that their scalar fallback
/// and portable vectors build too.
fn build_go_fixture(files: &[(String, String)], vendored: &[(PathBuf, Vec<u8>)]) -> FixtureResult {
    let requirement = env::var(GO_BUILD_VARIABLE).unwrap_or_default();
    if requirement == "skip" {
        return Ok(());
    }
    let runtime = match go_build_prerequisites() {
        Ok(runtime) => runtime,
        Err(reason) if requirement == "require" => {
            return Err(FixtureFailure(format!("{GO_BUILD_VARIABLE}=require, but {reason}")).into());
        }
        Err(reason) => {
            eprintln!(
                "warning: skipped building the fixture's Go: {reason} \
                 (set {GO_BUILD_VARIABLE}=require to fail instead)"
            );
            return Ok(());
        }
    };

    let module = tempfile::Builder::new().prefix("iris-go-fixture-").tempdir()?;
    write_go_module(module.path(), &runtime, files, vendored)?;
    let has_kernels = files.iter().any(|(path, _)| {
        ["_neon.go", "_vector.go", "_scalar.go"].iter().any(|suffix| path.ends_with(suffix))
    });
    let builds = if has_kernels {
        &[(Some("simd"), None), (None, None), (Some("simd"), Some(WASM))][..]
    } else {
        &[(Some("simd"), None)][..]
    };

    let _slot = go_build_slot()?;
    for &(experiment, platform) in builds {
        let output = go_vet(module.path(), experiment, platform)?;
        if !output.status.success() {
            let kept = module.keep();
            let mut shown = experiment.map_or("without GOEXPERIMENT".to_string(), |experiment| {
                format!("with GOEXPERIMENT={experiment}")
            });
            if let Some((system, architecture)) = platform {
                shown.push_str(&format!(" for {system}/{architecture}"));
            }
            return Err(FixtureFailure(format!(
                "the generated Go does not build {shown} (module kept at {}):\n{}{}",
                kept.display(),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            ))
            .into());
        }
    }
    Ok(())
}

/// The runtime checkout, once `go` is known to run.
fn go_build_prerequisites() -> Result<PathBuf, String> {
    match Command::new("go").arg("version").output() {
        Ok(output) if output.status.success() => {}
        Ok(_) => return Err("`go version` failed".to_string()),
        Err(error) => return Err(format!("`go` could not run: {error}")),
    }
    let runtime = env::var_os(GO_RUNTIME_VARIABLE)
        .filter(|path| !path.is_empty())
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../iris-go"));
    let runtime = runtime.canonicalize().map_err(|error| {
        format!(
            "the iris-go checkout {} is missing ({error}); set {GO_RUNTIME_VARIABLE}",
            runtime.display()
        )
    })?;
    if !runtime.join("go.mod").is_file() {
        return Err(format!("{} is not an iris-go checkout: it has no go.mod", runtime.display()));
    }
    Ok(runtime)
}

fn write_go_module(
    module: &Path,
    runtime: &Path,
    files: &[(String, String)],
    vendored: &[(PathBuf, Vec<u8>)],
) -> io::Result<()> {
    let go_mod = format!(
        "module fixture\n\ngo 1.27.0\n\nrequire {GO_RUNTIME_MODULE} {GO_RUNTIME_VERSION}\n\n\
         replace {GO_RUNTIME_MODULE} => {}\n",
        runtime.display()
    );
    let generated = files.iter().map(|(path, source)| (PathBuf::from(path), source.as_bytes()));
    let vendored = vendored.iter().map(|(path, contents)| (path.clone(), contents.as_slice()));
    let go_mod = std::iter::once((PathBuf::from("go.mod"), go_mod.as_bytes()));
    for (path, contents) in go_mod.chain(generated).chain(vendored) {
        let path = module.join(path);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, contents)?;
    }
    Ok(())
}

/// `go vet` type-checks every package as `go build` would, without linking.
fn go_vet(
    module: &Path,
    experiment: Option<&str>,
    platform: Option<(&str, &str)>,
) -> io::Result<std::process::Output> {
    let mut command = Command::new("go");
    command
        .args(["vet", "./..."])
        .current_dir(module)
        .env("GOFLAGS", "-mod=mod -buildvcs=false")
        .stdin(Stdio::null());
    match experiment {
        Some(experiment) => command.env("GOEXPERIMENT", experiment),
        None => command.env_remove("GOEXPERIMENT"),
    };
    if let Some((system, architecture)) = platform {
        command.env("GOOS", system).env("GOARCH", architecture);
    }
    command.output()
}

/// One of a few lock files shared by every test process, held while a fixture builds, so that the
/// builds do not all compete for the machine at once.
fn go_build_slot() -> io::Result<std::fs::File> {
    let jobs = env::var(GO_JOBS_VARIABLE)
        .ok()
        .and_then(|jobs| jobs.parse::<usize>().ok())
        .filter(|&jobs| jobs > 0)
        .unwrap_or(4);
    let directory = env::temp_dir().join("iris-go-fixture-build-slots");
    std::fs::create_dir_all(&directory)?;
    loop {
        for slot in 0..jobs {
            let file = std::fs::File::create(directory.join(slot.to_string()))?;
            match file.try_lock() {
                Ok(()) => return Ok(file),
                Err(std::fs::TryLockError::WouldBlock) => {}
                Err(std::fs::TryLockError::Error(error)) => return Err(error),
            }
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Builds a style-suite program with the Go backend, runs it, and compares what it prints with
/// `Main.stdout`, the output of the same program compiled to JavaScript. A fixture whose program
/// meets a difference that documentation/go-output.md lists, such as an Int sum past 32 bits,
/// compares with `Main.go.stdout` instead, which `INSTA_UPDATE=always` rewrites with what the Go
/// program prints. A fixture with a `crashes` file expects the program to exit unsuccessfully.
pub fn go_style(path: &Path) -> FixtureResult {
    let folder = fixture_folder(path)?;
    let Some(runtime) = go_style_runtime()? else { return Ok(()) };
    let root = snapshot_path(folder);
    let go_stdout = root.join("Main.go.stdout");
    let differs_from_javascript = go_stdout.is_file();
    let javascript_stdout = root.join("Main.stdout");
    let expected = if differs_from_javascript { go_stdout.clone() } else { javascript_stdout };
    let expectation = StyleExpectation {
        stdout: std::fs::read_to_string(expected)?,
        crashes: root.join("crashes").is_file(),
        record: (differs_from_javascript && updates_snapshots()).then_some(go_stdout),
        source: if differs_from_javascript { "expected (Go)" } else { "expected (JavaScript)" },
    };
    compile_style_program(folder.to_path_buf())
        .and_then(|program| run_style_program(&runtime, &program))
        .and_then(|output| expectation.check(&output))
        .map_err(|failure| FixtureFailure(failure).into())
}

/// How long compiling one style program may take; a compiler that loops counts as failing.
const GO_STYLE_COMPILE_TIMEOUT: Duration = Duration::from_secs(20);

/// How long a built style program may run.
const GO_STYLE_RUN_TIMEOUT: Duration = Duration::from_secs(60);

struct StyleExpectation {
    stdout: String,
    crashes: bool,
    /// Where to write what the Go program prints, when it is recorded rather than compared.
    record: Option<PathBuf>,
    /// Which output `stdout` is: JavaScript's, or Go's where the two differ as documented.
    source: &'static str,
}

struct StyleProgram {
    files: Vec<(String, String)>,
    vendored: VendoredFiles,
}

struct StyleOutput {
    succeeded: bool,
    stdout: String,
    stderr: String,
}

impl StyleExpectation {
    fn check(&self, output: &StyleOutput) -> Result<(), String> {
        let stderr = output.stderr.lines().take(20).join("\n");
        if output.succeeded == self.crashes {
            let expected = if self.crashes { "fail" } else { "succeed" };
            return Err(format!("the program should {expected}; its error output:\n{stderr}"));
        }
        if output.stdout == self.stdout {
            return Ok(());
        }
        if let Some(record) = &self.record {
            return std::fs::write(record, &output.stdout)
                .map_err(|error| format!("could not record {}: {error}", record.display()));
        }
        let diff = similar::TextDiff::from_lines(&self.stdout, &output.stdout);
        let mut unified = diff.unified_diff();
        unified.context_radius(2);
        unified.header(self.source, "Go");
        Err(format!("the program prints something else:\n{unified}{stderr}"))
    }
}

/// The runtime checkout to build against, or `None` when the suite is skipped.
fn go_style_runtime() -> FixtureResult<Option<PathBuf>> {
    let requirement = env::var(GO_BUILD_VARIABLE).unwrap_or_default();
    if requirement == "skip" {
        return Ok(None);
    }
    match go_build_prerequisites() {
        Ok(runtime) => Ok(Some(runtime)),
        Err(reason) if requirement == "require" => {
            Err(FixtureFailure(format!("{GO_BUILD_VARIABLE}=require, but {reason}")).into())
        }
        Err(reason) => {
            eprintln!(
                "warning: skipped the style program: {reason} \
                 (set {GO_BUILD_VARIABLE}=require to fail instead)"
            );
            Ok(None)
        }
    }
}

/// Compiles on its own thread, so that a compiler that loops is reported rather than waited for.
fn compile_style_program(folder: PathBuf) -> Result<StyleProgram, String> {
    let (sender, receiver) = std::sync::mpsc::channel();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let _ = sender.send(compile_style_program_here(&folder));
        })
        .map_err(|error| format!("could not start the compiler thread: {error}"))?;
    receiver.recv_timeout(GO_STYLE_COMPILE_TIMEOUT).unwrap_or_else(|_| {
        Err(format!(
            "compiling did not finish within {} seconds",
            GO_STYLE_COMPILE_TIMEOUT.as_secs()
        ))
    })
}

fn compile_style_program_here(folder: &Path) -> Result<StyleProgram, String> {
    let loaded = crate::load_fixture(folder).map_err(|error| error.to_string())?;
    check_source_errors(&loaded.engine, &loaded.files, &loaded.fixture_files)
        .map_err(|error| error.to_string())?;
    let packages = go_foreign_packages(&loaded, folder).map_err(|error| error.to_string())?;
    let (foreign_packages, vendored) = packages;
    let entry = entry_module(&loaded, folder)?;
    let program = go::compile_program(&loaded.engine, &entry, "main", &foreign_packages, "fixture")
        .map_err(|error| format!("the Go backend rejects the program:\n{error}"))?;
    Ok(StyleProgram { files: program.files, vendored })
}

/// The module `Main.purs` declares, which keeps the name it had where the program was written.
fn entry_module(loaded: &crate::LoadedFixture, folder: &Path) -> Result<String, String> {
    let entry = snapshot_path(folder).join("Main.purs");
    loaded
        .fixture_files
        .iter()
        .find(|&&file_id| {
            Url::parse(&loaded.files.path(file_id))
                .ok()
                .and_then(|url| url.to_file_path().ok())
                .is_some_and(|path| path == entry)
        })
        .and_then(|&file_id| go::module_name(&loaded.engine, file_id))
        .ok_or_else(|| format!("no module is declared in {}", entry.display()))
}

fn run_style_program(runtime: &Path, program: &StyleProgram) -> Result<StyleOutput, String> {
    let module = tempfile::Builder::new()
        .prefix("iris-go-style-")
        .tempdir()
        .map_err(|error| error.to_string())?;
    write_go_module(module.path(), runtime, &program.files, &program.vendored)
        .map_err(|error| error.to_string())?;
    let built = {
        let _slot = go_build_slot().map_err(|error| error.to_string())?;
        Command::new("go")
            .args(["build", "-o", "program", "."])
            .current_dir(module.path())
            .env("GOFLAGS", "-mod=mod -buildvcs=false")
            .env("GOEXPERIMENT", "simd")
            .stdin(Stdio::null())
            .output()
            .map_err(|error| format!("`go build` could not run: {error}"))?
    };
    if !built.status.success() {
        let kept = module.keep();
        return Err(format!(
            "the generated Go does not build (module kept at {}):\n{}",
            kept.display(),
            String::from_utf8_lossy(&built.stderr)
        ));
    }
    let running = Command::new(module.path().join("program"))
        .current_dir(module.path())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("the built program could not start: {error}"))?;
    let output = running
        .controlled_with_output()
        .time_limit(GO_STYLE_RUN_TIMEOUT)
        .terminate_for_timeout()
        .wait()
        .map_err(|error| error.to_string())?
        .ok_or_else(|| {
            format!("the program did not finish within {} seconds", GO_STYLE_RUN_TIMEOUT.as_secs())
        })?;
    Ok(StyleOutput {
        succeeded: output.status.success(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    })
}
