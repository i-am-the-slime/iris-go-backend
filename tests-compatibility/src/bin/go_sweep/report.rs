//! Classifies a sweep's outcomes into entry classes and package statuses, and compares them
//! against a checked-in baseline.
//!
//! An entry is `ok` when it compiled and its program built. Otherwise its blockers say why:
//! a missing Go FFI (`ffi`), an artifact of the harness's generated module (`harness`), a
//! documented limit (`bydesign`), or a Go backend failure (`backend`). A package's status is its
//! worst entry: `backend`, then `ffi-only`, then `harness-only`, else `pass`.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context as _, Result, bail};

use crate::{BlockerRecord, Outcome};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum EntryClass {
    Backend,
    Ffi,
    Harness,
    ByDesign,
    Ok,
}

impl EntryClass {
    pub fn label(self) -> &'static str {
        match self {
            EntryClass::Backend => "backend",
            EntryClass::Ffi => "ffi",
            EntryClass::Harness => "harness",
            EntryClass::ByDesign => "bydesign",
            EntryClass::Ok => "ok",
        }
    }

    fn package_status(self) -> PackageStatus {
        match self {
            EntryClass::Backend => PackageStatus::Backend,
            EntryClass::Ffi => PackageStatus::FfiOnly,
            EntryClass::Harness | EntryClass::ByDesign => PackageStatus::HarnessOnly,
            EntryClass::Ok => PackageStatus::Pass,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum PackageStatus {
    Backend,
    FfiOnly,
    HarnessOnly,
    Pass,
}

impl PackageStatus {
    const ALL: [PackageStatus; 4] = [
        PackageStatus::Pass,
        PackageStatus::FfiOnly,
        PackageStatus::HarnessOnly,
        PackageStatus::Backend,
    ];

    pub fn label(self) -> &'static str {
        match self {
            PackageStatus::Backend => "backend",
            PackageStatus::FfiOnly => "ffi-only",
            PackageStatus::HarnessOnly => "harness-only",
            PackageStatus::Pass => "pass",
        }
    }

    fn parse(label: &str) -> Option<PackageStatus> {
        PackageStatus::ALL.into_iter().find(|status| status.label() == label)
    }
}

/// Why one blocker stops an entry.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Cause {
    BackendLimit,
    MissingGoFfi,
    OpenType,
    HarnessArtifact,
    ByDesign,
}

pub struct Classified {
    pub package: String,
    pub entry: String,
    pub class: EntryClass,
    pub status: String,
    pub detail: String,
}

pub struct Results {
    pub entries: Vec<Classified>,
    pub packages: BTreeMap<String, PackageStatus>,
}

/// Reads and classifies the outcomes and builds of every sweep output directory.
pub fn load_results(outs: &[PathBuf]) -> Result<Results> {
    let mut entries = vec![];
    let mut seen = BTreeSet::new();
    for out in outs {
        let builds = read_builds(out)?;
        let outcomes = fs::read_to_string(out.join("outcomes.jsonl"))
            .with_context(|| format!("reading {}", out.join("outcomes.jsonl").display()))?;
        for line in outcomes.lines().filter(|line| !line.trim().is_empty()) {
            let outcome: Outcome = serde_json::from_str(line)?;
            let classified = classify(&outcome, builds.get(&outcome.program).map(String::as_str));
            if seen.insert((classified.package.clone(), classified.entry.clone())) {
                entries.push(classified);
            }
        }
    }
    let packages = package_statuses(&entries);
    Ok(Results { entries, packages })
}

fn read_builds(out: &Path) -> Result<HashMap<String, String>> {
    let text = fs::read_to_string(out.join("builds.jsonl")).unwrap_or_default();
    let mut builds = HashMap::new();
    for line in text.lines().filter(|line| !line.trim().is_empty()) {
        let record: serde_json::Value = serde_json::from_str(line)?;
        if let (Some(program), Some(status)) =
            (record["program"].as_str(), record["status"].as_str())
        {
            builds.insert(program.to_string(), status.to_string());
        }
    }
    Ok(builds)
}

pub fn classify(outcome: &Outcome, build: Option<&str>) -> Classified {
    let (class, status) = match outcome.status.as_str() {
        "ok" => match build {
            Some("ok") => (EntryClass::Ok, "ok".to_string()),
            Some(_) => (EntryClass::Backend, "build-failed".to_string()),
            None => (EntryClass::Backend, "unbuilt".to_string()),
        },
        "blocked" => (blocked_class(outcome), outcome.status.clone()),
        "unsupported" => (unsupported_class(outcome), outcome.status.clone()),
        _ => (EntryClass::Backend, outcome.status.clone()),
    };
    Classified {
        package: outcome.package.clone(),
        entry: format!("{}.{}", outcome.module, outcome.name),
        class,
        status,
        detail: detail(outcome),
    }
}

/// A blocker of the backend itself outweighs a missing FFI, which outweighs an open type the
/// missing FFI may explain; artifacts of the harness count only when nothing else blocks.
fn blocked_class(outcome: &Outcome) -> EntryClass {
    let causes: BTreeSet<Cause> = outcome.blockers.iter().map(cause).collect();
    match causes.first() {
        Some(Cause::BackendLimit) | None => EntryClass::Backend,
        Some(Cause::MissingGoFfi) => EntryClass::Ffi,
        Some(Cause::OpenType) => EntryClass::Backend,
        Some(Cause::HarnessArtifact) => EntryClass::Harness,
        Some(Cause::ByDesign) => EntryClass::ByDesign,
    }
}

fn cause(blocker: &BlockerRecord) -> Cause {
    let in_generated_module = blocker.definition.starts_with("Sweep.");
    match blocker.kind.as_str() {
        "ForeignData" | "MissingForeign" => Cause::MissingGoFfi,
        "Declaration" | "UninstantiatedVariable" if in_generated_module => Cause::HarnessArtifact,
        "OpenType" if blocker.state.contains("neither Int64's nor UInt64's") => Cause::ByDesign,
        "OpenType" => Cause::OpenType,
        _ => Cause::BackendLimit,
    }
}

/// Foreign data without a Go type is a missing FFI; `Record.Unsafe` at the empty record the
/// harness instantiates it at has no field for its run-time label.
fn unsupported_class(outcome: &Outcome) -> EntryClass {
    let message = &outcome.message;
    if message.contains("foreign data type") && message.contains("has no Go representation") {
        EntryClass::Ffi
    } else if outcome.instantiated
        && outcome.signature.contains("{  }")
        && message.contains("label")
    {
        EntryClass::Harness
    } else {
        EntryClass::Backend
    }
}

fn detail(outcome: &Outcome) -> String {
    let text = match outcome.blockers.first() {
        Some(blocker) => format!("{} {}: {}", blocker.kind, blocker.definition, blocker.state),
        None => outcome.message.clone(),
    };
    let line = text.lines().next().unwrap_or_default();
    match line.char_indices().nth(240) {
        Some((cut, _)) => format!("{}…", &line[..cut]),
        None => line.to_string(),
    }
}

fn package_statuses(entries: &[Classified]) -> BTreeMap<String, PackageStatus> {
    let mut packages: BTreeMap<String, PackageStatus> = BTreeMap::new();
    for entry in entries {
        let status = entry.class.package_status();
        packages
            .entry(entry.package.clone())
            .and_modify(|worst| *worst = (*worst).min(status))
            .or_insert(status);
    }
    packages
}

/// Writes `classified.tsv` (package, entry, class, status) and `package-status.tsv`
/// (status, package).
pub fn write_report(results: &Results, directory: &Path) -> Result<()> {
    fs::create_dir_all(directory)?;
    let mut classified = String::new();
    for entry in &results.entries {
        writeln!(
            classified,
            "{}\t{}\t{}\t{}",
            entry.package,
            entry.entry,
            entry.class.label(),
            entry.status
        )?;
    }
    fs::write(directory.join("classified.tsv"), classified)?;
    let mut rows: Vec<(&str, &str)> = results
        .packages
        .iter()
        .map(|(package, status)| (status.label(), package.as_str()))
        .collect();
    rows.sort();
    let statuses: String =
        rows.iter().map(|(status, package)| format!("{status}\t{package}\n")).collect();
    fs::write(directory.join("package-status.tsv"), statuses)?;
    Ok(())
}

/// Package statuses, and every entry that compiled and built.
pub struct Baseline {
    pub packages: BTreeMap<String, PackageStatus>,
    pub entries: BTreeSet<(String, String)>,
}

impl Baseline {
    pub fn of(results: &Results) -> Baseline {
        Baseline {
            packages: results.packages.clone(),
            entries: results
                .entries
                .iter()
                .filter(|entry| entry.class == EntryClass::Ok)
                .map(|entry| (entry.package.clone(), entry.entry.clone()))
                .collect(),
        }
    }

    pub fn read(path: &Path) -> Result<Baseline> {
        let text =
            fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
        let mut baseline = Baseline { packages: BTreeMap::new(), entries: BTreeSet::new() };
        for (number, line) in text.lines().enumerate().filter(|(_, line)| !line.trim().is_empty()) {
            match line.split('\t').collect::<Vec<_>>().as_slice() {
                ["package", package, status] => {
                    let status = PackageStatus::parse(status).with_context(|| {
                        format!("{}:{}: unknown status {status}", path.display(), number + 1)
                    })?;
                    baseline.packages.insert(package.to_string(), status);
                }
                ["ok", package, module, names] => {
                    for name in names.split(' ') {
                        baseline.entries.insert((package.to_string(), format!("{module}.{name}")));
                    }
                }
                _ => bail!(
                    "{}:{}: expected `package <name> <status>` or `ok <package> <module> <names>`",
                    path.display(),
                    number + 1
                ),
            }
        }
        Ok(baseline)
    }

    /// One line per package with its status, then one per module with the names of its ok
    /// entries.
    pub fn write(&self, path: &Path) -> Result<()> {
        let mut text = String::new();
        for (package, status) in &self.packages {
            writeln!(text, "package\t{package}\t{}", status.label())?;
        }
        let mut modules: BTreeMap<(&str, &str), Vec<&str>> = BTreeMap::new();
        for (package, entry) in &self.entries {
            let (module, name) = entry.rsplit_once('.').unwrap_or(("", entry));
            modules.entry((package, module)).or_default().push(name);
        }
        for ((package, module), names) in modules {
            writeln!(text, "ok\t{package}\t{module}\t{}", names.join(" "))?;
        }
        fs::write(path, text)?;
        Ok(())
    }
}

pub struct Comparison {
    pub text: String,
    pub regressed: bool,
}

/// A regression is a package that passed in the baseline and does not now, or an entry that was
/// ok in the baseline and is not now. Improvements and other changes are reported only.
pub fn compare(baseline: &Baseline, results: &Results) -> Comparison {
    let current: HashMap<(&str, &str), &Classified> = results
        .entries
        .iter()
        .map(|entry| ((entry.package.as_str(), entry.entry.as_str()), entry))
        .collect();
    let package_now = |package: &str| results.packages.get(package).copied();

    let regressed_packages: Vec<(&String, Option<PackageStatus>)> = baseline
        .packages
        .iter()
        .filter(|(package, was)| {
            **was == PackageStatus::Pass && package_now(package) != Some(PackageStatus::Pass)
        })
        .map(|(package, _)| (package, package_now(package)))
        .collect();
    let mut regressed_entries: BTreeMap<&str, Vec<String>> = BTreeMap::new();
    for (package, entry) in &baseline.entries {
        let now = current.get(&(package.as_str(), entry.as_str()));
        if now.is_some_and(|now| now.class == EntryClass::Ok) {
            continue;
        }
        let line = match now {
            Some(now) => {
                format!("`{entry}`: {} ({}) {}", now.class.label(), now.status, now.detail)
            }
            None => format!("`{entry}`: missing"),
        };
        regressed_entries.entry(package.as_str()).or_default().push(line);
    }

    let mut improved_packages = vec![];
    let mut worse_packages = vec![];
    for (package, now) in &results.packages {
        match baseline.packages.get(package) {
            None => improved_packages.push(format!("`{package}`: new, {}", now.label())),
            Some(was) if now > was => {
                improved_packages.push(format!("`{package}`: {} → {}", was.label(), now.label()))
            }
            Some(was) if now < was && *was != PackageStatus::Pass => {
                worse_packages.push(format!("`{package}`: {} → {}", was.label(), now.label()))
            }
            Some(_) => {}
        }
    }
    let mut newly_ok: BTreeMap<&str, usize> = BTreeMap::new();
    for entry in results.entries.iter().filter(|entry| entry.class == EntryClass::Ok) {
        if !baseline.entries.contains(&(entry.package.clone(), entry.entry.clone())) {
            *newly_ok.entry(entry.package.as_str()).or_default() += 1;
        }
    }

    let mut text = String::new();
    let _ = writeln!(text, "## Go registry sweep against the baseline\n");
    let _ = writeln!(text, "| packages | baseline | now |\n|---|---|---|");
    for status in PackageStatus::ALL {
        let count = |packages: &BTreeMap<String, PackageStatus>| {
            packages.values().filter(|s| **s == status).count()
        };
        let _ = writeln!(
            text,
            "| {} | {} | {} |",
            status.label(),
            count(&baseline.packages),
            count(&results.packages)
        );
    }
    let ok_now = results.entries.iter().filter(|entry| entry.class == EntryClass::Ok).count();
    let _ = writeln!(text, "| entries ok | {} | {} |\n", baseline.entries.len(), ok_now);

    let regressed = !regressed_packages.is_empty() || !regressed_entries.is_empty();
    if regressed {
        let _ = writeln!(text, "### Regressions\n");
        for (package, now) in &regressed_packages {
            let now = now.map_or("missing", PackageStatus::label);
            let _ = writeln!(text, "- `{package}`: pass → {now}");
        }
        for (package, lines) in &regressed_entries {
            let _ = writeln!(
                text,
                "- `{package}`: {} entries ok in the baseline are not ok now",
                lines.len()
            );
            for line in lines.iter().take(50) {
                let _ = writeln!(text, "  - {line}");
            }
            if lines.len() > 50 {
                let _ = writeln!(text, "  - … and {} more", lines.len() - 50);
            }
        }
        let _ = writeln!(text);
    } else {
        let _ = writeln!(text, "No regressions.\n");
    }
    if !improved_packages.is_empty() || !newly_ok.is_empty() {
        let _ = writeln!(text, "### Improvements (update the baseline to keep them)\n");
        for line in &improved_packages {
            let _ = writeln!(text, "- {line}");
        }
        for (package, count) in &newly_ok {
            let _ = writeln!(text, "- `{package}`: {count} entries newly ok");
        }
        let _ = writeln!(text);
    }
    if !worse_packages.is_empty() {
        let _ = writeln!(text, "### Worse, but not gated\n");
        for line in &worse_packages {
            let _ = writeln!(text, "- {line}");
        }
        let _ = writeln!(text);
    }
    Comparison { text, regressed }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn outcome(status: &str, blockers: &[(&str, &str, &str)]) -> Outcome {
        Outcome {
            package: "p".into(),
            module: "M".into(),
            name: "x".into(),
            signature: "Int".into(),
            instantiated: false,
            status: status.into(),
            blockers: blockers
                .iter()
                .map(|(kind, definition, state)| BlockerRecord {
                    kind: kind.to_string(),
                    definition: definition.to_string(),
                    state: state.to_string(),
                })
                .collect(),
            message: String::new(),
            functions: 0,
            program: "prog".into(),
        }
    }

    fn class_of(outcome: &Outcome, build: Option<&str>) -> EntryClass {
        classify(outcome, build).class
    }

    #[test]
    fn a_compiled_entry_is_ok_only_once_its_program_builds() {
        assert_eq!(class_of(&outcome("ok", &[]), Some("ok")), EntryClass::Ok);
        assert_eq!(class_of(&outcome("ok", &[]), Some("failed")), EntryClass::Backend);
        assert_eq!(class_of(&outcome("ok", &[]), None), EntryClass::Backend);
    }

    #[test]
    fn missing_go_ffi_outweighs_an_open_type_but_not_a_backend_limit() {
        let ffi_and_open = [
            ("ForeignData", "Sweep.G1V0.sweep", ""),
            ("OpenType", "Sweep.G1V0.sweep", "type ?3 has no closed representation"),
        ];
        assert_eq!(class_of(&outcome("blocked", &ffi_and_open), None), EntryClass::Ffi);
        let ffi_and_variable =
            [("MissingForeign", "Lib.f", ""), ("UninstantiatedVariable", "Lib.g", "")];
        assert_eq!(class_of(&outcome("blocked", &ffi_and_variable), None), EntryClass::Backend);
        assert_eq!(
            class_of(&outcome("blocked", &[("OpenType", "Lib.f", "")]), None),
            EntryClass::Backend
        );
        assert_eq!(
            class_of(&outcome("blocked", &[("SpecializationLimit", "Lib.f", "")]), None),
            EntryClass::Backend
        );
    }

    #[test]
    fn blockers_in_the_generated_module_are_harness_artifacts() {
        assert_eq!(
            class_of(&outcome("blocked", &[("Declaration", "Sweep.G1V0.sweep", "")]), None),
            EntryClass::Harness
        );
        assert_eq!(
            class_of(
                &outcome("blocked", &[("UninstantiatedVariable", "Sweep.G1V0.sweep", "")]),
                None
            ),
            EntryClass::Harness
        );
        assert_eq!(
            class_of(&outcome("blocked", &[("UninstantiatedVariable", "Lib.f", "")]), None),
            EntryClass::Backend
        );
    }

    #[test]
    fn a_long_of_no_single_signedness_is_by_design() {
        let blocker = [(
            "OpenType",
            "Sweep.G1V0.sweep",
            "a Data.Int64.Internal Long here is neither Int64's nor UInt64's",
        )];
        assert_eq!(class_of(&outcome("blocked", &blocker), None), EntryClass::ByDesign);
    }

    #[test]
    fn unsupported_entries_split_into_ffi_harness_and_backend() {
        let mut foreign = outcome("unsupported", &[]);
        foreign.message =
            "cannot specialize: foreign data type Web.Event.Event has no Go representation".into();
        assert_eq!(class_of(&foreign, None), EntryClass::Ffi);
        let mut empty_record = outcome("unsupported", &[]);
        empty_record.instantiated = true;
        empty_record.signature = "String -> {  } -> Int".into();
        empty_record.message =
            "record access through a run-time label where no field has the requested type".into();
        assert_eq!(class_of(&empty_record, None), EntryClass::Harness);
        let mut other = outcome("unsupported", &[]);
        other.message = "representation changes between unrelated types".into();
        assert_eq!(class_of(&other, None), EntryClass::Backend);
        assert_eq!(class_of(&outcome("hang", &[]), None), EntryClass::Backend);
    }

    fn results(entries: &[(&str, &str, EntryClass)]) -> Results {
        let entries: Vec<Classified> = entries
            .iter()
            .map(|(package, entry, class)| Classified {
                package: package.to_string(),
                entry: entry.to_string(),
                class: *class,
                status: String::new(),
                detail: String::new(),
            })
            .collect();
        let packages = package_statuses(&entries);
        Results { entries, packages }
    }

    #[test]
    fn a_package_takes_its_worst_entry() {
        let results = results(&[
            ("a", "A.x", EntryClass::Ok),
            ("b", "B.x", EntryClass::Ok),
            ("b", "B.y", EntryClass::ByDesign),
            ("c", "C.x", EntryClass::Harness),
            ("c", "C.y", EntryClass::Ffi),
            ("d", "D.x", EntryClass::Ffi),
            ("d", "D.y", EntryClass::Backend),
        ]);
        let statuses: Vec<_> = results.packages.values().copied().collect();
        assert_eq!(
            statuses,
            [
                PackageStatus::Pass,
                PackageStatus::HarnessOnly,
                PackageStatus::FfiOnly,
                PackageStatus::Backend
            ]
        );
    }

    #[test]
    fn a_passing_package_or_ok_entry_that_fails_now_is_a_regression() {
        let baseline = Baseline::of(&results(&[
            ("a", "A.x", EntryClass::Ok),
            ("b", "B.x", EntryClass::Ok),
            ("b", "B.y", EntryClass::Ffi),
        ]));
        assert!(
            !compare(
                &baseline,
                &results(&[
                    ("a", "A.x", EntryClass::Ok),
                    ("b", "B.x", EntryClass::Ok),
                    ("b", "B.y", EntryClass::Ffi)
                ])
            )
            .regressed
        );
        let package_broke = compare(
            &baseline,
            &results(&[
                ("a", "A.x", EntryClass::Backend),
                ("b", "B.x", EntryClass::Ok),
                ("b", "B.y", EntryClass::Ffi),
            ]),
        );
        assert!(package_broke.regressed);
        assert!(package_broke.text.contains("- `a`: pass → backend"));
        let entry_broke = compare(
            &baseline,
            &results(&[
                ("a", "A.x", EntryClass::Ok),
                ("b", "B.x", EntryClass::Ffi),
                ("b", "B.y", EntryClass::Ffi),
            ]),
        );
        assert!(entry_broke.regressed);
        assert!(entry_broke.text.contains("`B.x`: ffi"));
        let entry_vanished = compare(
            &baseline,
            &results(&[("a", "A.x", EntryClass::Ok), ("b", "B.y", EntryClass::Ffi)]),
        );
        assert!(entry_vanished.text.contains("`B.x`: missing"));
    }

    #[test]
    fn an_improvement_is_reported_without_failing() {
        let baseline = Baseline::of(&results(&[
            ("b", "B.x", EntryClass::Ok),
            ("b", "B.y", EntryClass::Backend),
        ]));
        let comparison = compare(
            &baseline,
            &results(&[
                ("b", "B.x", EntryClass::Ok),
                ("b", "B.y", EntryClass::Ok),
                ("c", "C.x", EntryClass::Ok),
            ]),
        );
        assert!(!comparison.regressed);
        assert!(comparison.text.contains("- `b`: backend → pass"));
        assert!(comparison.text.contains("- `c`: new, pass"));
        assert!(comparison.text.contains("- `b`: 1 entries newly ok"));
    }

    #[test]
    fn a_baseline_reads_back_as_written() {
        let baseline = Baseline::of(&results(&[
            ("a", "A.x", EntryClass::Ok),
            ("a", "A.y'", EntryClass::Ok),
            ("a", "A.B.z", EntryClass::Ok),
            ("b", "B.y", EntryClass::Ffi),
        ]));
        let path =
            std::env::temp_dir().join(format!("go-sweep-baseline-{}.tsv", std::process::id()));
        baseline.write(&path).unwrap();
        let read = Baseline::read(&path).unwrap();
        let _ = fs::remove_file(&path);
        assert_eq!(read.packages, baseline.packages);
        assert_eq!(read.entries, baseline.entries);
    }
}
