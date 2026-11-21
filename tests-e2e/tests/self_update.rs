use std::env::consts::EXE_SUFFIX;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

#[path = "support.rs"]
mod support;

use support::{TestWorkspace, assert_success};

/// Copies the Iris under test into the workspace, so that updating it leaves the build untouched.
fn install_iris(workspace: &TestWorkspace) -> PathBuf {
    let directory = workspace.path().join("bin");
    fs::create_dir_all(&directory).unwrap();
    let executable = directory.join(format!("iris{EXE_SUFFIX}"));
    fs::copy(env!("CARGO_BIN_EXE_iris-e2e"), &executable).unwrap();
    dunce::canonicalize(executable).unwrap()
}

fn run(executable: &Path, arguments: &[&str]) -> Output {
    Command::new(executable).args(arguments).env("NO_COLOR", "1").output().unwrap()
}

fn version(executable: &Path) -> String {
    let output = run(executable, &["--version"]);
    assert_success(&output);
    let output = String::from_utf8(output.stdout).unwrap();
    output.trim_end().strip_prefix("iris ").unwrap().to_owned()
}

fn update_report(arguments: &[&str]) -> String {
    let workspace = TestWorkspace::empty();
    let executable = install_iris(&workspace);
    let current = version(&executable);

    let arguments = ["self", "update"].iter().chain(arguments).copied().collect::<Vec<_>>();
    let output = run(&executable, &arguments);
    assert_eq!(version(&executable), current);
    workspace.report(&output).replace(&current, "[CURRENT]")
}

#[test]
fn refers_the_go_backend_fork_to_homebrew_instead_of_installing_a_release() {
    insta::assert_snapshot!(update_report(&["v0.1.5"]), @"
    status: 1
    --- stdout
    --- stderr
    Iris [CURRENT] is the Go backend fork, which `iris self update` cannot update; run `brew upgrade i-am-the-slime/tap/iris` to update it
    ");
}

#[test]
fn refers_the_go_backend_fork_to_homebrew_instead_of_installing_the_latest_release() {
    insta::assert_snapshot!(update_report(&[]), @"
    status: 1
    --- stdout
    --- stderr
    Iris [CURRENT] is the Go backend fork, which `iris self update` cannot update; run `brew upgrade i-am-the-slime/tap/iris` to update it
    ");
}

#[test]
fn refers_the_go_backend_fork_to_homebrew_instead_of_checking_for_a_canary() {
    insta::assert_snapshot!(update_report(&["--check", "--canary"]), @"
    status: 1
    --- stdout
    --- stderr
    Iris [CURRENT] is the Go backend fork, which `iris self update` cannot update; run `brew upgrade i-am-the-slime/tap/iris` to update it
    ");
}
