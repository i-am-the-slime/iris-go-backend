use std::ffi::OsString;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn googoo_reports_its_own_name_and_version() {
    let output = Command::new(googoo()).arg("--version").output().unwrap();

    assert!(output.status.success());
    let expected = format!("googoo {}\n", env!("CARGO_PKG_VERSION"));
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
}

#[test]
fn the_old_iris_name_warns_and_runs_googoo_with_the_same_arguments() {
    let output = Command::new(iris()).arg("--version").output().unwrap();

    assert!(output.status.success());
    let expected = format!("googoo {}\n", env!("CARGO_PKG_VERSION"));
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
    let warning = "iris is now called googoo; this alias will go away\n";
    assert_eq!(String::from_utf8(output.stderr).unwrap(), warning);
}

#[test]
fn the_old_iris_name_passes_on_googoos_exit_status() {
    let output = Command::new(iris()).arg("no-such-command").output().unwrap();

    assert_eq!(output.status.code(), Some(2));
}

fn googoo() -> PathBuf {
    binary(std::env::var_os("NEXTEST_BIN_EXE_googoo"), env!("CARGO_BIN_EXE_googoo"))
}

fn iris() -> PathBuf {
    binary(std::env::var_os("NEXTEST_BIN_EXE_iris"), env!("CARGO_BIN_EXE_iris"))
}

/// Where the binary is when the test runs: nextest says so when it runs the tests from an archive
/// unpacked somewhere other than where they were built.
fn binary(at_run_time: Option<OsString>, at_build_time: &str) -> PathBuf {
    at_run_time.map_or_else(|| PathBuf::from(at_build_time), PathBuf::from)
}
