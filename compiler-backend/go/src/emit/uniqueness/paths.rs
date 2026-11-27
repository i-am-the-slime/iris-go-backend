//! The ways a function body may use a local, as the set of orders its uses can happen in.
//!
//! A [`Path`] is one order of uses, summarised: how often the local is consumed (stored, passed
//! on, returned), whether a local that shares cells with it is used too, and whether it is
//! peeked at (only read, as a `case` or an inspecting function reads it) before or after its
//! first consumption. [`Paths`] is the set of all orders a body can take, one bit per summary,
//! so that branches add orders and sequencing combines them.
//!
//! A local is *linear* in a body when on every path it is consumed at most once, never next to
//! a consumption of a relative, and never peeked at after it was consumed: the consumer may
//! then overwrite its cells, as no one else can see them.

#[derive(Clone, Copy)]
pub(in crate::emit) enum Event {
    Consume,
    Conflict,
    Peek,
    Shared,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Path {
    consumed: u8,
    conflicted: bool,
    peeked_first: bool,
    peeked_late: bool,
}

impl Path {
    const START: Path =
        Path { consumed: 0, conflicted: false, peeked_first: false, peeked_late: false };

    fn index(self) -> u32 {
        u32::from(self.consumed) * 8
            + u32::from(self.conflicted) * 4
            + u32::from(self.peeked_first) * 2
            + u32::from(self.peeked_late)
    }

    fn from_index(index: u32) -> Path {
        Path {
            consumed: (index / 8) as u8,
            conflicted: index & 4 != 0,
            peeked_first: index & 2 != 0,
            peeked_late: index & 1 != 0,
        }
    }

    fn touched(self) -> bool {
        self.consumed > 0 || self.conflicted
    }

    fn then(self, next: Path) -> Path {
        Path {
            consumed: (self.consumed + next.consumed).min(2),
            conflicted: self.conflicted || next.conflicted,
            peeked_first: self.peeked_first || (!self.touched() && next.peeked_first),
            peeked_late: self.peeked_late
                || next.peeked_late
                || (next.peeked_first && self.touched()),
        }
    }

    fn is_linear(self) -> bool {
        !self.peeked_late && self.consumed < 2 && !(self.consumed == 1 && self.conflicted)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::emit) struct Paths(u32);

impl Paths {
    pub(in crate::emit) fn nothing() -> Paths {
        Paths(0)
    }

    pub(in crate::emit) fn empty() -> Paths {
        Paths(1 << Path::START.index())
    }

    pub(in crate::emit) fn event(event: Event) -> Paths {
        let path = match event {
            Event::Consume => Path { consumed: 1, ..Path::START },
            Event::Conflict => Path { conflicted: true, ..Path::START },
            Event::Peek => Path { peeked_first: true, ..Path::START },
            Event::Shared => Path { consumed: 2, ..Path::START },
        };
        Paths(1 << path.index())
    }

    fn paths(self) -> impl Iterator<Item = Path> {
        (0..24).filter(move |index| self.0 & (1 << index) != 0).map(Path::from_index)
    }

    pub(in crate::emit) fn then(self, next: Paths) -> Paths {
        let mut combined = 0;
        for first in self.paths() {
            for second in next.paths() {
                combined |= 1 << first.then(second).index();
            }
        }
        Paths(combined)
    }

    pub(in crate::emit) fn unordered(self, other: Paths) -> Paths {
        Paths(self.then(other).0 | other.then(self).0)
    }

    pub(in crate::emit) fn or(self, other: Paths) -> Paths {
        Paths(self.0 | other.0)
    }

    /// The orders of a body that runs any number of times: one that consumes or conflicts
    /// shares, one that only peeks peeks.
    pub(in crate::emit) fn repeated(self) -> Paths {
        let paths: Vec<Path> = self.paths().collect();
        if paths.iter().any(|path| path.touched()) {
            Paths::event(Event::Shared)
        } else if paths.iter().any(|path| path.peeked_first || path.peeked_late) {
            Paths::event(Event::Peek)
        } else {
            Paths::empty()
        }
    }

    /// Whether no order of the body consumes the local or a relative of it.
    pub(in crate::emit) fn never_consumed(self) -> bool {
        self.paths().all(|path| !path.touched())
    }

    pub(in crate::emit) fn all_linear(self) -> bool {
        self.paths().all(Path::is_linear)
    }
}

#[cfg(test)]
mod tests {
    use super::{Event, Paths};

    fn consume() -> Paths {
        Paths::event(Event::Consume)
    }

    fn peek() -> Paths {
        Paths::event(Event::Peek)
    }

    #[test]
    fn a_single_consumption_is_linear() {
        assert!(consume().all_linear());
        assert!(Paths::empty().all_linear());
        assert!(Paths::nothing().all_linear());
    }

    #[test]
    fn two_consumptions_in_a_row_are_not() {
        assert!(!consume().then(consume()).all_linear());
        assert!(!consume().unordered(consume()).all_linear());
    }

    #[test]
    fn one_consumption_in_each_branch_is_linear() {
        assert!(consume().or(consume()).all_linear());
        assert!(!consume().or(consume().then(consume())).all_linear());
    }

    #[test]
    fn a_peek_is_linear_only_before_the_consumption() {
        assert!(peek().then(consume()).all_linear());
        assert!(peek().then(peek()).then(consume()).all_linear());
        assert!(!consume().then(peek()).all_linear());
        assert!(!peek().unordered(consume()).all_linear());
    }

    #[test]
    fn a_relative_used_next_to_a_consumption_is_not() {
        let conflict = Paths::event(Event::Conflict);
        assert!(conflict.all_linear());
        assert!(!conflict.then(consume()).all_linear());
        assert!(!consume().then(conflict).all_linear());
        assert!(conflict.or(consume()).all_linear());
    }

    #[test]
    fn a_capture_shares_the_local() {
        assert!(!Paths::event(Event::Shared).all_linear());
    }
}
