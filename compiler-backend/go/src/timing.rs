//! Per-phase timings of the backend, reported on standard error when
//! `IRIS_GO_TIMINGS` is set. Nested phases are indented under their parent and
//! reported when they finish.

use std::cell::Cell;
use std::sync::OnceLock;
use std::time::Instant;

thread_local! {
    static DEPTH: Cell<usize> = const { Cell::new(0) };
}

pub(crate) fn timed<T>(phase: &str, run: impl FnOnce() -> T) -> T {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    if !*ENABLED.get_or_init(|| std::env::var_os("IRIS_GO_TIMINGS").is_some()) {
        return run();
    }
    let depth = DEPTH.get();
    DEPTH.set(depth + 1);
    let started = Instant::now();
    let result = run();
    let elapsed = started.elapsed();
    DEPTH.set(depth);
    eprintln!("go timing: {:indent$}{phase} {elapsed:.1?}", "", indent = depth * 2);
    result
}
