//! The command's old name, kept for a while after the rename to `googoo`. It says so on standard
//! error and runs the `googoo` installed next to it with the same arguments, so it stays small
//! instead of being a second copy of the compiler.

use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

fn main() -> ExitCode {
    eprintln!("iris is now called googoo; this alias will go away");
    let googoo = googoo_next_to_this_executable();
    let mut command = Command::new(&googoo);
    command.args(env::args_os().skip(1));
    hand_over_to(command, &googoo)
}

/// The `googoo` beside this executable, after following symlinks such as Homebrew's, or else
/// whichever `googoo` is on the PATH.
fn googoo_next_to_this_executable() -> PathBuf {
    let name = format!("googoo{}", env::consts::EXE_SUFFIX);
    env::current_exe()
        .and_then(|executable| executable.canonicalize())
        .ok()
        .and_then(|executable| executable.parent().map(|directory| directory.join(&name)))
        .filter(|googoo| googoo.is_file())
        .unwrap_or_else(|| PathBuf::from(name))
}

#[cfg(unix)]
fn hand_over_to(mut command: Command, googoo: &Path) -> ExitCode {
    use std::os::unix::process::CommandExt;
    let error = command.exec();
    eprintln!("iris: could not run {}: {error}", googoo.display());
    ExitCode::from(127)
}

#[cfg(not(unix))]
fn hand_over_to(mut command: Command, googoo: &Path) -> ExitCode {
    match command.status() {
        Ok(status) => ExitCode::from(status.code().map_or(1, |code| code.clamp(0, 255) as u8)),
        Err(error) => {
            eprintln!("iris: could not run {}: {error}", googoo.display());
            ExitCode::from(127)
        }
    }
}
