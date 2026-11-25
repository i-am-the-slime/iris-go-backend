//! Runs the Go backend over every package of a registry package set.
//!
//! The Go backend compiles a whole program from one entry value, so the sweep compiles one
//! program per exported value of every module whose type is monomorphic, and, with
//! `--instantiate`, one per polymorphic value that a generated module instantiates at simple
//! types (Int, Array, the empty row) where its constraints then resolve. Every program that
//! compiles is written as a Go module and built by `go-sweep build`.
//!
//!   go-sweep drive    --cache <compat cache> --out <dir> [--packages a,b | --shard k/n] [--instantiate]
//!   go-sweep build    --out <dir> [--jobs 3]
//!   go-sweep classify --out <dir>... [--report <dir>] [--write-baseline <file>]
//!   go-sweep compare  --out <dir>... --baseline <file> [--report <dir>]
//!
//! `drive` reruns its worker after a hang or a crash, recording the entry that caused it.
//! `compare` exits with 1 when a package or entry that passed in the baseline does not now.

mod report;

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use anyhow::{Context as _, Result};
use building::{QueryEngine, prim};
use checking::core::Type;
use checking::core::pretty::{Pretty, PrettyQueries};
use clap::{Parser, Subcommand};
use files::{FileId, Files, ForeignFiles, ForeignSourceKind};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use url::Url;
use walkdir::WalkDir;

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Drive(WorkerArgs),
    Worker(WorkerArgs),
    Build(BuildArgs),
    Classify(ClassifyArgs),
    Compare(CompareArgs),
}

#[derive(clap::Args)]
struct ResultsArgs {
    /// Sweep output directories, one per shard.
    #[arg(long, required = true)]
    out: Vec<PathBuf>,
    /// Where to write `classified.tsv` and `package-status.tsv`.
    #[arg(long)]
    report: Option<PathBuf>,
}

#[derive(clap::Args)]
struct ClassifyArgs {
    #[command(flatten)]
    results: ResultsArgs,
    #[arg(long)]
    write_baseline: Option<PathBuf>,
}

#[derive(clap::Args)]
struct CompareArgs {
    #[command(flatten)]
    results: ResultsArgs,
    #[arg(long)]
    baseline: PathBuf,
}

#[derive(clap::Args, Clone)]
struct WorkerArgs {
    #[arg(long)]
    cache: PathBuf,
    #[arg(long, default_value = "82.1.1")]
    package_set: String,
    #[arg(long)]
    out: PathBuf,
    /// Comma-separated packages whose modules are swept; all by default.
    #[arg(long)]
    packages: Option<String>,
    /// `k/n`: only every n-th batch of 25 packages, starting at the k-th.
    #[arg(long, conflicts_with = "packages", value_parser = parse_shard)]
    shard: Option<(usize, usize)>,
    #[arg(long, default_value_t = 4)]
    jobs: usize,
    #[arg(long, default_value_t = 120)]
    timeout: u64,
    /// Seconds one module may take to check before its instantiations are skipped.
    #[arg(long, default_value_t = 60)]
    check_timeout: u64,
    /// Also instantiate polymorphic values at simple types in generated modules.
    #[arg(long)]
    instantiate: bool,
    /// Only these entries (one `package module name` per line), one at a time.
    #[arg(long)]
    only: Option<PathBuf>,
}

#[derive(clap::Args)]
struct BuildArgs {
    #[arg(long)]
    out: PathBuf,
    #[arg(long, default_value_t = 3)]
    jobs: usize,
}

#[derive(Serialize, Deserialize, Clone)]
struct Outcome {
    package: String,
    module: String,
    name: String,
    /// The type it was compiled at.
    signature: String,
    /// Whether the entry is an instantiation in a generated module.
    instantiated: bool,
    status: String,
    #[serde(default)]
    blockers: Vec<BlockerRecord>,
    #[serde(default)]
    message: String,
    #[serde(default)]
    functions: usize,
    #[serde(default)]
    program: String,
}

#[derive(Serialize, Deserialize, Clone)]
struct BlockerRecord {
    kind: String,
    definition: String,
    state: String,
}

fn main() -> Result<()> {
    match Cli::parse().command {
        Commands::Drive(args) => drive(args),
        Commands::Worker(args) => worker(args),
        Commands::Build(args) => build(args),
        Commands::Classify(args) => classify(args),
        Commands::Compare(args) => compare(args),
    }
}

fn parse_shard(value: &str) -> Result<(usize, usize), String> {
    let parsed = value.split_once('/').and_then(|(index, count)| {
        Some((index.parse::<usize>().ok()?, count.parse::<usize>().ok()?))
    });
    match parsed {
        Some((index, count)) if 1 <= index && index <= count => Ok((index, count)),
        _ => Err(format!("expected k/n with 1 <= k <= n, got {value}")),
    }
}

fn classify(args: ClassifyArgs) -> Result<()> {
    let results = classified_results(&args.results)?;
    if let Some(path) = &args.write_baseline {
        report::Baseline::of(&results).write(path)?;
    }
    for (status, count) in package_counts(&results) {
        println!("{status}\t{count}");
    }
    Ok(())
}

fn compare(args: CompareArgs) -> Result<()> {
    let results = classified_results(&args.results)?;
    let baseline = report::Baseline::read(&args.baseline)?;
    let comparison = report::compare(&baseline, &results);
    print!("{}", comparison.text);
    if comparison.regressed {
        std::process::exit(1);
    }
    Ok(())
}

fn classified_results(args: &ResultsArgs) -> Result<report::Results> {
    let results = report::load_results(&args.out)?;
    if let Some(directory) = &args.report {
        report::write_report(&results, directory)?;
    }
    Ok(results)
}

fn package_counts(results: &report::Results) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for status in results.packages.values() {
        *counts.entry(status.label().to_string()).or_default() += 1;
    }
    counts
}

/// Runs the worker until every entry has an outcome, isolating the entry that hangs or crashes it.
fn drive(args: WorkerArgs) -> Result<()> {
    fs::create_dir_all(&args.out)?;
    if args.packages.is_some() {
        return drive_batch(&args);
    }
    let set_path =
        args.cache.join("registry/package-sets").join(format!("{}.json", args.package_set));
    let set: serde_json::Value = serde_json::from_str(&fs::read_to_string(&set_path)?)?;
    let mut packages: Vec<String> = set["packages"]
        .as_object()
        .context("package set has no packages")?
        .iter()
        .filter(|(package, version)| {
            args.cache
                .join("sources")
                .join(package)
                .join(version.as_str().unwrap_or_default())
                .join("src")
                .is_dir()
        })
        .map(|(package, _)| package.clone())
        .collect();
    packages.sort();
    let done: HashSet<String> = fs::read_to_string(args.out.join("batches.txt"))
        .unwrap_or_default()
        .lines()
        .map(str::to_string)
        .collect();
    let (shard, shards) = args.shard.unwrap_or((1, 1));
    let batches = packages.chunks(25).enumerate().filter(|(index, _)| index % shards == shard - 1);
    for (_, batch) in batches {
        let batch = batch.join(",");
        if done.contains(&batch) {
            continue;
        }
        eprintln!("go-sweep: batch {batch}");
        let mut batch_args = args.clone();
        batch_args.packages = Some(batch.clone());
        drive_batch(&batch_args)?;
        let mut file =
            fs::OpenOptions::new().create(true).append(true).open(args.out.join("batches.txt"))?;
        writeln!(file, "{batch}")?;
    }
    Ok(())
}

fn drive_batch(args: &WorkerArgs) -> Result<()> {
    let args = args.clone();
    let exe = std::env::current_exe()?;
    loop {
        let mut command = Command::new(&exe);
        command
            .arg("worker")
            .args(worker_arguments(&args))
            .env("RAYON_NUM_THREADS", args.jobs.to_string());
        let status = command.status()?;
        if status.success() {
            return Ok(());
        }
        let started = unfinished_entries(&args.out)?;
        eprintln!("go-sweep: worker exited with {status}; {} unfinished entries", started.len());
        let stuck = fs::read_to_string(args.out.join("stuck.txt")).unwrap_or_default();
        if status.code() == Some(4) && !stuck.is_empty() {
            let mut file =
                fs::OpenOptions::new().create(true).append(true).open(args.out.join("skip.txt"))?;
            write!(file, "{stuck}")?;
            for line in stuck.lines() {
                if let Some(rest) = line.strip_prefix("check ") {
                    let module = rest.split(' ').next().unwrap_or_default();
                    writeln!(file, "checkmodule {module}")?;
                }
            }
            fs::remove_file(args.out.join("stuck.txt"))?;
            eprintln!("go-sweep: skipping {}", stuck.trim());
            continue;
        }
        if started.is_empty() {
            eprintln!("go-sweep: batch failed outside compilation: {:?}", args.packages);
            return Ok(());
        }
        // Each unfinished entry alone: the one that dies again is recorded as the crash.
        for entry in started {
            let only = args.out.join("only.txt");
            fs::write(&only, format!("{entry}\n"))?;
            let mut command = Command::new(&exe);
            command
                .arg("worker")
                .args(worker_arguments(&args))
                .env("RAYON_NUM_THREADS", "2")
                .arg("--only")
                .arg(&only);
            command.args(["--jobs", "1"]);
            let status = command.status()?;
            if !status.success() && unfinished_entries(&args.out)?.contains(&entry) {
                let (package, rest) = entry.split_once(' ').unwrap_or((&entry, ""));
                let (module, name) = rest.split_once(' ').unwrap_or((rest, ""));
                let outcome = Outcome {
                    package: package.into(),
                    module: module.into(),
                    name: name.into(),
                    signature: String::new(),
                    instantiated: false,
                    status: if status.code() == Some(3) { "hang" } else { "crash" }.into(),
                    blockers: vec![],
                    message: format!("worker exited with {status}"),
                    functions: 0,
                    program: String::new(),
                };
                append_outcome(&args.out, &outcome)?;
            }
        }
    }
}

fn worker_arguments(args: &WorkerArgs) -> Vec<String> {
    let mut arguments = vec![
        "--cache".into(),
        args.cache.display().to_string(),
        "--package-set".into(),
        args.package_set.clone(),
        "--out".into(),
        args.out.display().to_string(),
        "--jobs".into(),
        args.jobs.to_string(),
        "--timeout".into(),
        args.timeout.to_string(),
        "--check-timeout".into(),
        args.check_timeout.to_string(),
    ];
    if let Some(packages) = &args.packages {
        arguments.extend(["--packages".into(), packages.clone()]);
    }
    if args.instantiate {
        arguments.push("--instantiate".into());
    }
    arguments
}

/// Entries the journal says were started and have no outcome.
fn unfinished_entries(out: &Path) -> Result<Vec<String>> {
    let journal = fs::read_to_string(out.join("journal.txt")).unwrap_or_default();
    let done = finished_entries(out)?;
    let mut started = BTreeSet::new();
    for line in journal.lines() {
        if let Some(entry) = line.strip_prefix("start ") {
            started.insert(entry.to_string());
        }
        if let Some(entry) = line.strip_prefix("end ") {
            started.remove(entry);
        }
    }
    Ok(started.into_iter().filter(|entry| !done.contains(entry)).collect())
}

fn finished_entries(out: &Path) -> Result<HashSet<String>> {
    let text = fs::read_to_string(out.join("outcomes.jsonl")).unwrap_or_default();
    let mut done = HashSet::new();
    for line in text.lines() {
        let outcome: Outcome = serde_json::from_str(line)?;
        done.insert(entry_key(&outcome.package, &outcome.module, &outcome.name));
    }
    Ok(done)
}

fn entry_key(package: &str, module: &str, name: &str) -> String {
    format!("{package} {module} {name}")
}

static OUTPUT_LOCK: Mutex<()> = Mutex::new(());

fn append_outcome(out: &Path, outcome: &Outcome) -> Result<()> {
    let _lock = OUTPUT_LOCK.lock().unwrap();
    let mut file =
        fs::OpenOptions::new().create(true).append(true).open(out.join("outcomes.jsonl"))?;
    writeln!(file, "{}", serde_json::to_string(outcome)?)?;
    Ok(())
}

fn journal(out: &Path, line: &str) {
    let _lock = OUTPUT_LOCK.lock().unwrap();
    if let Ok(mut file) =
        fs::OpenOptions::new().create(true).append(true).open(out.join("journal.txt"))
    {
        let _ = writeln!(file, "{line}");
    }
}

struct Loaded {
    engine: QueryEngine,
    files: Files,
    /// Each project file with its package and module name.
    modules: Vec<(String, FileId, String)>,
}

/// One program to compile: an entry value and the source of the generated module it is in, if any.
#[derive(Clone)]
struct Entry {
    package: String,
    module: String,
    name: String,
    signature: String,
    file_id: FileId,
    term_name: String,
    instantiated: bool,
}

fn worker(args: WorkerArgs) -> Result<()> {
    fs::create_dir_all(args.out.join("go"))?;
    let loaded = load(&args.cache, &args.package_set)?;
    let selected: Option<HashSet<String>> =
        args.packages.as_ref().map(|packages| packages.split(',').map(str::to_string).collect());
    let only: Option<HashSet<String>> = match &args.only {
        Some(path) => Some(fs::read_to_string(path)?.lines().map(str::to_string).collect()),
        None => None,
    };
    let done = finished_entries(&args.out)?;
    let skipped = if only.is_some() {
        HashSet::new()
    } else {
        unfinished_entries(&args.out)?.into_iter().collect()
    };

    *SKIPPED.lock().unwrap() = Some(
        fs::read_to_string(args.out.join("skip.txt"))
            .unwrap_or_default()
            .lines()
            .map(str::to_string)
            .collect(),
    );
    watch_phases(args.out.clone(), Duration::from_secs(args.check_timeout));
    let mut loaded = loaded;
    let entries = entries(&mut loaded, selected.as_ref(), args.instantiate)?;
    let entries: Vec<Entry> = entries
        .into_iter()
        .filter(|entry| {
            let key = entry_key(&entry.package, &entry.module, &entry.name);
            match &only {
                Some(only) => only.contains(&key),
                None => !done.contains(&key) && !skipped.contains(&key),
            }
        })
        .collect();
    eprintln!("go-sweep: {} entries to compile", entries.len());

    let running: Arc<Mutex<HashMap<String, Instant>>> = Arc::default();
    let finished = Arc::new(AtomicBool::new(false));
    {
        let running = Arc::clone(&running);
        let finished = Arc::clone(&finished);
        let timeout = Duration::from_secs(args.timeout);
        std::thread::spawn(move || {
            while !finished.load(Ordering::Relaxed) {
                std::thread::sleep(Duration::from_secs(2));
                let running = running.lock().unwrap();
                if let Some((entry, _)) =
                    running.iter().find(|(_, started)| started.elapsed() > timeout)
                {
                    eprintln!("go-sweep: {entry} exceeded {timeout:?}");
                    std::process::exit(3);
                }
            }
        });
    }

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(args.jobs)
        .stack_size(512 * 1024 * 1024)
        .build()?;
    let engine = &loaded.engine;
    let count = std::sync::atomic::AtomicUsize::new(0);
    let total = entries.len();
    pool.install(|| {
        entries.par_iter().for_each(|entry| {
            let key = entry_key(&entry.package, &entry.module, &entry.name);
            journal(&args.out, &format!("start {key}"));
            running.lock().unwrap().insert(key.clone(), Instant::now());
            let snapshot = engine.snapshot();
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                compile_entry(&snapshot, entry, &args.out)
            }));
            let outcome = match outcome {
                Ok(outcome) => outcome,
                Err(panic) => {
                    let message = panic
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
                        .unwrap_or_default();
                    outcome_for(entry, "panic", message)
                }
            };
            drop(snapshot);
            let _ = append_outcome(&args.out, &outcome);
            running.lock().unwrap().remove(&key);
            journal(&args.out, &format!("end {key}"));
            let n = count.fetch_add(1, Ordering::Relaxed) + 1;
            if n.is_multiple_of(500) {
                eprintln!("go-sweep: {n}/{total}");
            }
        });
    });
    finished.store(true, Ordering::Relaxed);
    Ok(())
}

fn outcome_for(entry: &Entry, status: &str, message: String) -> Outcome {
    Outcome {
        package: entry.package.clone(),
        module: entry.module.clone(),
        name: entry.name.clone(),
        signature: entry.signature.clone(),
        instantiated: entry.instantiated,
        status: status.into(),
        blockers: vec![],
        message,
        functions: 0,
        program: String::new(),
    }
}

const GO_MODULE: &str = "sweep.example/program";

fn compile_entry(engine: &QueryEngine, entry: &Entry, out: &Path) -> Outcome {
    let module = go::module_name(engine, entry.file_id).unwrap_or_default();
    let foreign_packages =
        go::ForeignPackages { module_path: GO_MODULE.into(), ..Default::default() };
    let compiled =
        go::compile_program(engine, &module, &entry.term_name, &foreign_packages, GO_MODULE);
    match compiled {
        Ok(program) => {
            let directory = out.join("go").join(&entry.package).join(format!(
                "{}.{}.{}",
                entry.module,
                sanitize(&entry.name),
                go::module_name(engine, entry.file_id).unwrap_or_default().replace("Sweep.", "")
            ));
            let written = write_program(&directory, &program.files);
            let mut outcome = outcome_for(entry, "ok", program.notes.join("\n"));
            outcome.functions = program.functions;
            outcome.program = directory.display().to_string();
            if let Err(error) = written {
                outcome.status = "write-error".into();
                outcome.message = error.to_string();
            }
            outcome
        }
        Err(go::GoError::Blocked(blockers)) => {
            let mut outcome = outcome_for(entry, "blocked", String::new());
            outcome.blockers = blockers
                .blockers
                .iter()
                .map(|blocker| BlockerRecord {
                    kind: format!("{:?}", blocker.state.kind()),
                    definition: blocker.definition.clone(),
                    state: blocker.state.to_string(),
                })
                .collect();
            outcome
        }
        Err(error @ go::GoError::SourceErrors { .. }) => {
            outcome_for(entry, "source-errors", error.to_string())
        }
        Err(error) => {
            let status = match &error {
                go::GoError::Unsupported { .. } => "unsupported",
                go::GoError::Query(_) => "query-error",
                go::GoError::MissingEntry(_) => "missing-entry",
                go::GoError::EntryImported { .. } => "entry-imported",
                go::GoError::SharedRecordStruct { .. } => "shared-record-struct",
                go::GoError::RepresentationChange(_) => "representation-change",
                go::GoError::Blocked(_) | go::GoError::SourceErrors { .. } => unreachable!(),
            };
            outcome_for(entry, status, error.to_string())
        }
    }
}

fn sanitize(name: &str) -> String {
    name.chars().map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' }).collect()
}

fn write_program(directory: &Path, files: &[(String, String)]) -> Result<()> {
    if directory.exists() {
        fs::remove_dir_all(directory)?;
    }
    fs::create_dir_all(directory)?;
    let runtime =
        std::env::var("IRIS_GO").unwrap_or_else(|_| "/Users/mark/Developer/iris-go".into());
    fs::write(
        directory.join("go.mod"),
        format!(
            "module {GO_MODULE}\n\ngo 1.27.0\n\nrequire github.com/i-am-the-slime/iris-go v0.0.0\n\nreplace github.com/i-am-the-slime/iris-go => {runtime}\n"
        ),
    )?;
    for (path, source) in files {
        let path = directory.join(path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, source)?;
    }
    Ok(())
}

/// Loads every package of the package set that the cache holds.
fn load(cache: &Path, package_set: &str) -> Result<Loaded> {
    let set_path = cache.join("registry/package-sets").join(format!("{package_set}.json"));
    let set: serde_json::Value = serde_json::from_str(&fs::read_to_string(&set_path)?)?;
    let versions = set["packages"].as_object().context("package set has no packages")?;

    let mut engine = QueryEngine::default();
    let mut files = Files::default();
    let mut foreign_files = ForeignFiles::default();
    prim::configure(&mut engine, &mut files);

    let mut project = vec![];
    for (package, version) in versions {
        let version = version.as_str().unwrap_or_default();
        let root = cache.join("sources").join(package).join(version);
        let src = root.join("src");
        if !src.is_dir() {
            continue;
        }
        let mut paths: Vec<PathBuf> = WalkDir::new(&src)
            .into_iter()
            .filter_map(Result::ok)
            .filter(|entry| entry.file_type().is_file())
            .map(|entry| entry.into_path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "purs"))
            .collect();
        paths.sort();
        for path in paths {
            let content = fs::read_to_string(&path)?;
            let absolute = fs::canonicalize(&path)?;
            let uri = Url::from_file_path(&absolute).unwrap().to_string();
            let file_id = files.insert(uri, content.clone());
            engine.set_content(file_id, content);
            for kind in ForeignSourceKind::ALL {
                let foreign = path.with_extension(kind.extension());
                if !foreign.is_file() {
                    continue;
                }
                let content = fs::read_to_string(&foreign)?;
                let uri = Url::from_file_path(fs::canonicalize(&foreign)?).unwrap().to_string();
                let foreign_id = foreign_files.insert(kind, uri, content.clone());
                engine.set_foreign_content(foreign_id, content);
                engine.set_foreign_file(file_id, foreign_id);
            }
            project.push((package.clone(), file_id));
        }
    }

    project.par_iter().for_each(|(_, file_id)| {
        let _ = engine.snapshot().parsed(*file_id);
    });
    let mut modules = vec![];
    let mut seen = HashSet::new();
    for (package, file_id) in project {
        let Some(name) = go::module_name(&engine, file_id) else { continue };
        if !seen.insert(name.clone()) {
            eprintln!("go-sweep: duplicate module {name} in {package}, skipped");
            continue;
        }
        engine.insert_module_file(&name, file_id);
        modules.push((package, file_id, name));
    }
    eprintln!("go-sweep: loaded {} modules", modules.len());
    Ok(Loaded { engine, files, modules })
}

/// The entries of the selected packages. Each is a generated module `Sweep.G<n>` whose `sweep`
/// is an exported value of a package module: as it is when monomorphic, and with `instantiate`
/// annotated at an instantiation of its type at simple types where that type checks.
static SKIPPED: Mutex<Option<HashSet<String>>> = Mutex::new(None);
static PHASES: Mutex<Option<HashMap<String, Instant>>> = Mutex::new(None);

fn phase_start(key: &str) {
    PHASES.lock().unwrap().get_or_insert_default().insert(key.to_string(), Instant::now());
}

fn phase_end(key: &str) {
    PHASES.lock().unwrap().get_or_insert_default().remove(key);
}

/// Exits with 4 when checking one module takes longer than `limit`, naming it in `stuck.txt`.
fn watch_phases(out: PathBuf, limit: Duration) {
    std::thread::spawn(move || {
        loop {
            std::thread::sleep(Duration::from_secs(2));
            let phases = PHASES.lock().unwrap();
            let stuck: Vec<&String> = phases
                .iter()
                .flatten()
                .filter(|(_, started)| started.elapsed() > limit)
                .map(|(key, _)| key)
                .collect();
            if !stuck.is_empty() {
                let text: String = stuck.iter().map(|key| format!("{key}\n")).collect();
                let _ = fs::write(out.join("stuck.txt"), text);
                std::process::exit(4);
            }
        }
    });
}

fn entries(
    loaded: &mut Loaded,
    selected: Option<&HashSet<String>>,
    instantiate: bool,
) -> Result<Vec<Entry>> {
    let modules: Vec<(String, FileId, String)> = loaded
        .modules
        .iter()
        .filter(|(package, _, _)| selected.is_none_or(|selected| selected.contains(package)))
        .cloned()
        .collect();
    let candidates: Vec<Candidate> = {
        let engine = &loaded.engine;
        let per_module: Vec<Vec<Candidate>> = modules
            .par_iter()
            .map(|(package, file_id, module)| {
                let engine = engine.snapshot();
                let key = format!("module {module}");
                if SKIPPED.lock().unwrap().as_ref().is_some_and(|skipped| skipped.contains(&key)) {
                    return vec![];
                }
                phase_start(&key);
                let found = module_candidates(&engine, package, *file_id, module, instantiate)
                    .unwrap_or_else(|error| {
                        eprintln!("go-sweep: {module}: {error}");
                        vec![]
                    });
                phase_end(&key);
                found
            })
            .collect();
        per_module.into_iter().flatten().collect()
    };

    // One generated module per variant of each candidate.
    let mut generated: Vec<(usize, usize, FileId)> = vec![];
    for (index, candidate) in candidates.iter().enumerate() {
        for (variant, (annotation, imports)) in candidate.variants.iter().enumerate() {
            let name = format!("Sweep.G{index}V{variant}");
            let mut source = format!("module {name} where\n\n");
            source.push_str(&format!("import {} as {}\n", candidate.module, candidate.module));
            for import in imports {
                if import != &candidate.module {
                    source.push_str(&format!("import {import} as {import}\n"));
                }
            }
            let reference = format!("{}.{}", candidate.module, identifier(&candidate.name));
            match annotation {
                Some(annotation) => {
                    source.push_str(&format!("\nsweep :: {annotation}\nsweep = {reference}\n"))
                }
                None => source.push_str(&format!("\nsweep = {reference}\n")),
            }
            let uri = format!("file:///sweep/{}.purs", name.replace('.', "/"));
            let file_id = loaded.files.insert(uri, source.clone());
            loaded.engine.set_content(file_id, source);
            loaded.engine.insert_module_file(&name, file_id);
            generated.push((index, variant, file_id));
        }
    }

    let engine = &loaded.engine;
    let accepted: Vec<(usize, usize, FileId, bool)> = generated
        .par_iter()
        .map(|&(index, variant, file_id)| {
            let candidate = &candidates[index];
            let key = format!("check {} {} {variant}", candidate.module, candidate.name);
            if SKIPPED.lock().unwrap().as_ref().is_some_and(|skipped| skipped.contains(&key))
                || SKIPPED.lock().unwrap().as_ref().is_some_and(|skipped| {
                    skipped.contains(&format!("checkmodule {}", candidate.module))
                })
            {
                return (index, variant, file_id, false);
            }
            let engine = engine.snapshot();
            phase_start(&key);
            let fine = !checking::has_frontend_errors(&engine, file_id).unwrap_or(true);
            phase_end(&key);
            (index, variant, file_id, fine)
        })
        .collect();
    let mut chosen: BTreeMap<usize, (usize, FileId)> = BTreeMap::new();
    let mut rejected = vec![];
    for (index, variant, file_id, fine) in accepted {
        if fine {
            let best = chosen.entry(index).or_insert((variant, file_id));
            if variant < best.0 {
                *best = (variant, file_id);
            }
        } else if candidates[index].variants[variant].0.is_none() {
            rejected.push(index);
        }
    }
    for index in rejected {
        let candidate = &candidates[index];
        eprintln!(
            "go-sweep: monomorphic {}.{} does not check when referenced",
            candidate.module, candidate.name
        );
    }
    let entries = chosen
        .into_iter()
        .map(|(index, (variant, file_id))| {
            let candidate = &candidates[index];
            let (annotation, _) = &candidate.variants[variant];
            Entry {
                package: candidate.package.clone(),
                module: candidate.module.clone(),
                name: candidate.name.clone(),
                signature: annotation.clone().unwrap_or_else(|| candidate.signature.clone()),
                file_id,
                term_name: "sweep".into(),
                instantiated: annotation.is_some(),
            }
        })
        .collect();
    let instantiable =
        candidates.iter().filter(|c| c.variants.iter().any(|v| v.0.is_some())).count();
    eprintln!(
        "go-sweep: {} exported values, {} instantiable, {} uninstantiable",
        candidates.len(),
        instantiable,
        loaded_uninstantiable()
    );
    Ok(entries)
}

static UNINSTANTIABLE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn loaded_uninstantiable() -> usize {
    UNINSTANTIABLE.load(Ordering::Relaxed)
}

fn identifier(name: &str) -> String {
    name.to_string()
}

/// An exported value and the annotations to compile it at: `None` for a monomorphic value.
struct Candidate {
    package: String,
    module: String,
    name: String,
    signature: String,
    variants: Vec<(Option<String>, BTreeSet<String>)>,
}

/// The simple types a variant instantiates variables at, by kind.
const VARIANTS: [[(&str, &str); 4]; 2] = [
    [("Type", "Int"), ("Type -> Type", "Array"), ("Row Type", "()"), ("Symbol", "\"a\"")],
    [
        ("Type", "String"),
        ("Type -> Type", "Effect.Effect"),
        ("Row Type", "()"),
        ("Symbol", "\"a\""),
    ],
];

fn module_candidates(
    engine: &QueryEngine,
    package: &str,
    file_id: FileId,
    module: &str,
    instantiate: bool,
) -> Result<Vec<Candidate>> {
    if checking::has_frontend_errors(engine, file_id)? {
        eprintln!("go-sweep: {module} has frontend errors");
        return Ok(vec![]);
    }
    let resolved = engine.resolved(file_id)?;
    let checked = engine.checked(file_id)?;
    let indexed = engine.indexed(file_id)?;
    let pretty = Pretty::new(engine, &checked);
    let mut candidates = vec![];
    let mut exported: Vec<_> = resolved
        .exports
        .iter_terms()
        .filter(|(_, owner, _)| *owner == file_id)
        .map(|(name, _, term)| (name.clone(), term))
        .collect();
    exported.sort_by(|a, b| a.0.cmp(&b.0));
    for (name, term) in exported {
        if matches!(
            indexed.items[term].kind,
            indexing::IndexedTermItemKind::ClassMember { .. }
                | indexing::IndexedTermItemKind::Operator { .. }
        ) {
            continue;
        }
        let Some(&type_id) = checked.term_item_types.get(&term) else { continue };
        let signature = pretty.render(type_id).map(|s| s.to_string()).unwrap_or_default();
        let mut renderer = Renderer::new(engine, 0);
        let monomorphic = renderer.is_monomorphic(type_id, &HashSet::new());
        let variants = if monomorphic {
            vec![(None, BTreeSet::new())]
        } else if instantiate {
            let mut variants = vec![];
            for variant in 0..VARIANTS.len() {
                let mut renderer = Renderer::new(engine, variant);
                if let Some(rendered) = renderer.render(type_id, 0, true)
                    && rendered.len() < 2000
                {
                    variants.push((Some(rendered), renderer.imports));
                }
            }
            if variants.is_empty() {
                UNINSTANTIABLE.fetch_add(1, Ordering::Relaxed);
            }
            variants
        } else {
            vec![]
        };
        if variants.is_empty() {
            continue;
        }
        candidates.push(Candidate {
            package: package.into(),
            module: module.into(),
            name: name.to_string(),
            signature,
            variants,
        });
    }
    Ok(candidates)
}

/// Renders a checked type as source in a module that imports each module it names `as` its
/// full name, with synonyms expanded, and quantifiers in instantiable positions (the whole
/// type and function results) instantiated at a variant's simple types, their constraints left
/// for the checker to solve.
struct Renderer<'a> {
    engine: &'a QueryEngine,
    variant: usize,
    substitution: HashMap<checking::core::Name, String>,
    imports: BTreeSet<String>,
    depth: usize,
}

impl<'a> Renderer<'a> {
    fn new(engine: &'a QueryEngine, variant: usize) -> Renderer<'a> {
        Renderer {
            engine,
            variant,
            substitution: HashMap::new(),
            imports: BTreeSet::new(),
            depth: 0,
        }
    }

    /// Whether a type has no quantifier, constraint or variable once its synonyms are expanded.
    fn is_monomorphic(
        &mut self,
        type_id: checking::TypeId,
        parameters: &HashSet<checking::core::Name>,
    ) -> bool {
        let engine = self.engine;
        match engine.lookup_type(type_id).clone() {
            Type::Application(function, argument) | Type::Function(function, argument) => {
                self.is_monomorphic(function, parameters)
                    && self.is_monomorphic(argument, parameters)
            }
            Type::KindApplication(function, _) | Type::Kinded(function, _) => {
                self.is_monomorphic(function, parameters)
            }
            Type::Rigid(name, _, _) => parameters.contains(&name),
            Type::Forall(..)
            | Type::Constrained(..)
            | Type::ConstraintOrigin(..)
            | Type::Unification(_)
            | Type::Free(_)
            | Type::Unknown(_) => false,
            Type::Synonym(file_id, item) => {
                let Some(synonym) = synonym(engine, file_id, item) else { return false };
                let parameters: HashSet<_> =
                    synonym.parameters.iter().map(|binder| binder.name).collect();
                self.is_monomorphic(synonym.expansion, &parameters)
            }
            Type::Constructor(..) | Type::Integer(_) | Type::String(..) => true,
            Type::Row(row) => {
                let row = engine.lookup_row_type(row).clone();
                row.fields.iter().all(|field| self.is_monomorphic(field.id, parameters))
                    && row.tail.is_none_or(|tail| self.is_monomorphic(tail, parameters))
            }
        }
    }

    fn simple_type(&mut self, kind: checking::TypeId) -> Option<String> {
        let rendered = render_kind(self.engine, kind)?;
        let (_, simple) = VARIANTS[self.variant].iter().find(|(k, _)| *k == rendered)?;
        if let Some((module, _)) = simple.rsplit_once('.') {
            self.imports.insert(module.to_string());
        }
        Some(simple.to_string())
    }

    /// `precedence` 0 is a function's result or the whole type, 1 a function's argument, 2 an
    /// application's argument. `instantiable` says whether quantifiers here are instantiated.
    fn render(
        &mut self,
        type_id: checking::TypeId,
        precedence: u8,
        instantiable: bool,
    ) -> Option<String> {
        self.depth += 1;
        if self.depth > 200 {
            return None;
        }
        let rendered = self.render_inner(type_id, precedence, instantiable);
        self.depth -= 1;
        rendered
    }

    fn render_inner(
        &mut self,
        type_id: checking::TypeId,
        precedence: u8,
        instantiable: bool,
    ) -> Option<String> {
        let engine = self.engine;
        let parenthesise =
            |text: String, needed: bool| if needed { format!("({text})") } else { text };
        match engine.lookup_type(type_id).clone() {
            Type::Application(..) | Type::Synonym(..) => {
                let (head, arguments) = spine(engine, type_id);
                if let Type::Synonym(file_id, item) = engine.lookup_type(head).clone()
                    && !hides_quantifier(engine, synonym(engine, file_id, item)?.expansion)
                {
                    let indexed = engine.indexed(file_id).ok()?;
                    let name = indexed.items[item].name.clone()?;
                    let module = go::module_name(engine, file_id)?;
                    self.imports.insert(module.clone());
                    let mut text = format!("{module}.{name}");
                    for argument in arguments {
                        text.push(' ');
                        text.push_str(&self.render(argument, 2, false)?);
                    }
                    return Some(parenthesise(text, precedence >= 2));
                }
                if let Type::Synonym(file_id, item) = engine.lookup_type(head).clone() {
                    let synonym = synonym(engine, file_id, item)?;
                    if synonym.parameters.len() != arguments.len() {
                        return None;
                    }
                    let mut saved = vec![];
                    for (binder, argument) in synonym.parameters.iter().zip(&arguments) {
                        let rendered = self.render(*argument, 2, false)?;
                        saved.push((binder.name, self.substitution.insert(binder.name, rendered)));
                    }
                    let expanded = self.render(synonym.expansion, precedence, instantiable);
                    for (name, previous) in saved {
                        match previous {
                            Some(previous) => self.substitution.insert(name, previous),
                            None => self.substitution.remove(&name),
                        };
                    }
                    return expanded;
                }
                if let Some(rendered) = self.record(head, &arguments) {
                    return Some(rendered);
                }
                let mut text = self.render(head, 2, false)?;
                for argument in arguments {
                    text.push(' ');
                    text.push_str(&self.render(argument, 2, false)?);
                }
                Some(parenthesise(text, precedence >= 2))
            }
            Type::KindApplication(function, _) => self.render(function, precedence, instantiable),
            Type::Function(argument, result) => {
                let argument = self.render(argument, 1, false)?;
                let result = self.render(result, 0, instantiable)?;
                Some(parenthesise(format!("{argument} -> {result}"), precedence >= 1))
            }
            Type::Kinded(inner, _) => self.render(inner, precedence, instantiable),
            Type::Forall(binder, body) => {
                let binder = engine.lookup_forall_binder(binder);
                if instantiable {
                    let simple = self.simple_type(binder.kind)?;
                    self.substitution.insert(binder.name, simple);
                    return self.render(body, precedence, true);
                }
                let variable = format!("t{}", binder.name.unique);
                self.substitution.insert(binder.name, variable.clone());
                let body = self.render(body, 0, false)?;
                Some(format!("(forall {variable}. {body})"))
            }
            Type::Constrained(constraint, body) | Type::ConstraintOrigin(constraint, body) => {
                if instantiable {
                    return self.render(body, precedence, true);
                }
                let constraint = self.render(constraint, 1, false)?;
                let body = self.render(body, 0, false)?;
                Some(format!("({constraint} => {body})"))
            }
            Type::Constructor(file_id, item) => {
                let indexed = engine.indexed(file_id).ok()?;
                let name = indexed.items[item].name.clone()?;
                if !name.chars().next()?.is_alphabetic() {
                    return None;
                }
                if file_id == engine.prim_id() {
                    return Some(name.to_string());
                }
                let module = go::module_name(engine, file_id)?;
                self.imports.insert(module.clone());
                Some(format!("{module}.{name}"))
            }
            Type::Integer(value) => {
                Some(if value < 0 { format!("({value})") } else { value.to_string() })
            }
            Type::String(_, literal) => {
                let literal = engine.lookup_string_literal(literal);
                Some(format!("{:?}", literal.to_utf8().ok()?))
            }
            Type::Row(row) => {
                let row = engine.lookup_row_type(row).clone();
                let mut fields = vec![];
                for field in row.fields.iter() {
                    fields.push(format!(
                        "{} :: {}",
                        label(&field.label),
                        self.render(field.id, 0, false)?
                    ));
                }
                let tail = match row.tail {
                    Some(tail) => format!(" | {}", self.render(tail, 0, false)?),
                    None => String::new(),
                };
                Some(format!("({}{tail})", fields.join(", ")))
            }
            Type::Rigid(name, _, _) => self.substitution.get(&name).cloned(),
            Type::Unification(_) | Type::Free(_) | Type::Unknown(_) => None,
        }
    }

    fn record(&mut self, head: checking::TypeId, arguments: &[checking::TypeId]) -> Option<String> {
        let engine = self.engine;
        let Type::Constructor(file_id, item) = engine.lookup_type(head).clone() else {
            return None;
        };
        if file_id != engine.prim_id() || arguments.len() != 1 {
            return None;
        }
        let indexed = engine.indexed(file_id).ok()?;
        if indexed.items[item].name.as_deref() != Some("Record") {
            return None;
        }
        let row = self.render(arguments[0], 0, false)?;
        if !row.starts_with('(') {
            return Some(format!("Record {row}"));
        }
        let inner = &row[1..row.len() - 1];
        Some(format!("{{ {inner} }}"))
    }
}

fn hides_quantifier(engine: &QueryEngine, type_id: checking::TypeId) -> bool {
    match engine.lookup_type(type_id).clone() {
        Type::Forall(..) | Type::Constrained(..) | Type::ConstraintOrigin(..) => true,
        Type::Application(f, a) | Type::Function(f, a) => {
            hides_quantifier(engine, f) || hides_quantifier(engine, a)
        }
        Type::KindApplication(f, _) | Type::Kinded(f, _) => hides_quantifier(engine, f),
        Type::Row(row) => {
            let row = engine.lookup_row_type(row).clone();
            row.fields.iter().any(|field| hides_quantifier(engine, field.id))
        }
        _ => false,
    }
}

fn spine(
    engine: &QueryEngine,
    type_id: checking::TypeId,
) -> (checking::TypeId, Vec<checking::TypeId>) {
    let mut arguments = vec![];
    let mut current = type_id;
    loop {
        match engine.lookup_type(current).clone() {
            Type::Application(function, argument) => {
                arguments.push(argument);
                current = function;
            }
            Type::KindApplication(function, _) => current = function,
            _ => break,
        }
    }
    arguments.reverse();
    (current, arguments)
}

fn synonym(
    engine: &QueryEngine,
    file_id: FileId,
    item: indexing::TypeItemId,
) -> Option<checking::core::CheckedSynonym> {
    let checked = engine.checked(file_id).ok()?;
    checked.synonyms.get(&item).cloned()
}

fn render_kind(engine: &QueryEngine, kind: checking::TypeId) -> Option<String> {
    match engine.lookup_type(kind).clone() {
        Type::Constructor(file_id, item) => {
            let indexed = engine.indexed(file_id).ok()?;
            Some(indexed.items[item].name.clone()?.to_string())
        }
        Type::Function(argument, result) => {
            Some(format!("{} -> {}", render_kind(engine, argument)?, render_kind(engine, result)?))
        }
        Type::Application(function, argument) => {
            Some(format!("{} {}", render_kind(engine, function)?, render_kind(engine, argument)?))
        }
        _ => None,
    }
}

fn label(label: &str) -> String {
    let plain = label.chars().next().is_some_and(|c| c.is_lowercase() || c == '_')
        && label.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '\'');
    if plain { label.to_string() } else { format!("{label:?}") }
}

/// Builds every compiled program with `go build`, many programs per Go module: each program goes
/// into its own directory `p<n>` with its imports renamed, so that one `go build ./...` compiles
/// a chunk of programs at once. A program fails when a package of its directory reports errors.
fn build(args: BuildArgs) -> Result<()> {
    let text = fs::read_to_string(args.out.join("outcomes.jsonl"))?;
    let built = fs::read_to_string(args.out.join("builds.jsonl")).unwrap_or_default();
    let built: HashSet<String> = built
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter_map(|value| value["program"].as_str().map(str::to_string))
        .collect();
    let programs: Vec<String> = text
        .lines()
        .filter_map(|line| serde_json::from_str::<Outcome>(line).ok())
        .filter(|outcome| outcome.status == "ok" && !built.contains(&outcome.program))
        .map(|outcome| outcome.program)
        .filter(|program| Path::new(program).join("go.mod").is_file())
        .collect();
    eprintln!("go-sweep: {} programs to build", programs.len());
    let runtime =
        std::env::var("IRIS_GO").unwrap_or_else(|_| "/Users/mark/Developer/iris-go".into());
    let chunks: Vec<&[String]> = programs.chunks(150).collect();
    let pool = rayon::ThreadPoolBuilder::new().num_threads(args.jobs).build()?;
    let count = std::sync::atomic::AtomicUsize::new(0);
    pool.install(|| {
        chunks.par_iter().enumerate().for_each(|(index, chunk)| {
            let records = build_chunk(&args.out, index, chunk, &runtime).unwrap_or_else(|error| {
                chunk
                    .iter()
                    .map(|program| serde_json::json!({"program": program, "status": "error", "log": error.to_string()}))
                    .collect()
            });
            let _lock = OUTPUT_LOCK.lock().unwrap();
            if let Ok(mut file) =
                fs::OpenOptions::new().create(true).append(true).open(args.out.join("builds.jsonl"))
            {
                for record in records {
                    let _ = writeln!(file, "{record}");
                }
            }
            let n = count.fetch_add(chunk.len(), Ordering::Relaxed) + chunk.len();
            eprintln!("go-sweep: built {n}/{}", programs.len());
        });
    });
    Ok(())
}

fn build_chunk(
    out: &Path,
    index: usize,
    chunk: &[String],
    runtime: &str,
) -> Result<Vec<serde_json::Value>> {
    let module = out.join("chunks").join(format!("c{index}"));
    if module.exists() {
        fs::remove_dir_all(&module)?;
    }
    fs::create_dir_all(&module)?;
    fs::write(
        module.join("go.mod"),
        format!(
            "module sweep.example/all\n\ngo 1.27.0\n\nrequire github.com/i-am-the-slime/iris-go v0.0.0\n\nreplace github.com/i-am-the-slime/iris-go => {runtime}\n"
        ),
    )?;
    for (position, program) in chunk.iter().enumerate() {
        let target = module.join(format!("p{position}"));
        for entry in WalkDir::new(program).into_iter().filter_map(Result::ok) {
            let relative = entry.path().strip_prefix(program)?;
            if entry.file_type().is_dir() || relative == Path::new("go.mod") {
                continue;
            }
            let destination = target.join(relative);
            fs::create_dir_all(destination.parent().unwrap())?;
            let bytes = fs::read(entry.path())?;
            if entry.path().extension().is_some_and(|ext| ext == "go") {
                let source = String::from_utf8_lossy(&bytes).replace(
                    &format!("\"{GO_MODULE}/"),
                    &format!("\"sweep.example/all/p{position}/"),
                );
                fs::write(destination, source)?;
            } else {
                fs::write(destination, bytes)?;
            }
        }
    }
    let started = Instant::now();
    let output = Command::new("timeout")
        .args(["1800", "go", "build", "./..."])
        .current_dir(&module)
        .output()?;
    let log = String::from_utf8_lossy(&output.stderr).to_string();
    // Error lines name files relative to the module: `p12/Data_Maybe/Data_Maybe.go:3:1: ...`,
    // `./p12/main.go:...`, under headers `# sweep.example/all/p12/...`.
    let mut failures: HashMap<usize, String> = HashMap::new();
    let mut current: Option<usize> = None;
    for line in log.lines() {
        if let Some(rest) = line.strip_prefix("# sweep.example/all/p") {
            current = rest.split(|c: char| !c.is_ascii_digit()).next().and_then(|n| n.parse().ok());
        }
        let trimmed = line.trim_start_matches("./");
        let named = trimmed
            .strip_prefix('p')
            .and_then(|rest| rest.split(|c: char| !c.is_ascii_digit()).next())
            .and_then(|n| n.parse::<usize>().ok())
            .filter(|_| trimmed.contains(".go:"));
        let mentioned = line
            .split("sweep.example/all/p")
            .nth(1)
            .and_then(|rest| rest.split(|c: char| !c.is_ascii_digit()).next())
            .and_then(|n| n.parse::<usize>().ok())
            .filter(|_| !line.starts_with("# "));
        if let Some(position) = named.or(mentioned).or(current) {
            let entry = failures.entry(position).or_default();
            if entry.len() < 3000 {
                entry.push_str(line);
                entry.push('\n');
            }
        }
    }
    let unattributed = !output.status.success() && failures.is_empty();
    let seconds = started.elapsed().as_secs_f64();
    let records = chunk
        .iter()
        .enumerate()
        .map(|(position, program)| match failures.get(&position) {
            Some(log) => serde_json::json!({"program": program, "status": "failed", "log": log, "seconds": seconds}),
            None if unattributed => serde_json::json!({"program": program, "status": "chunk-failed", "log": log.chars().take(3000).collect::<String>(), "seconds": seconds}),
            None => serde_json::json!({"program": program, "status": "ok", "seconds": seconds}),
        })
        .collect();
    if !unattributed {
        for (position, program) in chunk.iter().enumerate() {
            if !failures.contains_key(&position) {
                let _ = fs::remove_dir_all(program);
            }
        }
        let _ = fs::remove_dir_all(&module);
    }
    Ok(records)
}
