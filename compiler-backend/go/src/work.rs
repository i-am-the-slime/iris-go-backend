use std::fmt;
use std::time::Duration;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    instructions: Option<u64>,
    cpu_time: Option<Duration>,
}

impl Work {
    pub fn so_far() -> Work {
        Work { instructions: instructions_retired(), cpu_time: cpu_time() }
    }

    pub fn since(self, earlier: Work) -> Work {
        let instructions = self.instructions.zip(earlier.instructions);
        let cpu_time = self.cpu_time.zip(earlier.cpu_time);
        Work {
            instructions: instructions.map(|(now, then)| now.saturating_sub(then)),
            cpu_time: cpu_time.map(|(now, then)| now.saturating_sub(then)),
        }
    }

    pub fn instructions(self) -> Option<u64> {
        self.instructions
    }
}

impl fmt::Display for Work {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.instructions, self.cpu_time) {
            (Some(instructions), _) => {
                write!(formatter, "{:.2} G instructions", instructions as f64 / 1e9)
            }
            (None, Some(cpu_time)) => write!(formatter, "{:.2} s CPU", cpu_time.as_secs_f64()),
            (None, None) => formatter.write_str("unmeasured"),
        }
    }
}

#[cfg(target_os = "macos")]
fn instructions_retired() -> Option<u64> {
    let mut usage = std::mem::MaybeUninit::<libc::rusage_info_v4>::uninit();
    let process = std::process::id() as libc::c_int;
    let status =
        unsafe { libc::proc_pid_rusage(process, libc::RUSAGE_INFO_V4, usage.as_mut_ptr().cast()) };
    if status != 0 {
        return None;
    }
    let usage = unsafe { usage.assume_init() };
    Some(usage.ri_instructions)
}

#[cfg(not(target_os = "macos"))]
fn instructions_retired() -> Option<u64> {
    None
}

#[cfg(unix)]
fn cpu_time() -> Option<Duration> {
    let mut usage = std::mem::MaybeUninit::<libc::rusage>::uninit();
    let status = unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) };
    if status != 0 {
        return None;
    }
    let usage = unsafe { usage.assume_init() };
    Some(seconds(usage.ru_utime) + seconds(usage.ru_stime))
}

#[cfg(unix)]
fn seconds(time: libc::timeval) -> Duration {
    Duration::from_secs(time.tv_sec as u64) + Duration::from_micros(time.tv_usec as u64)
}

#[cfg(not(unix))]
fn cpu_time() -> Option<Duration> {
    None
}
