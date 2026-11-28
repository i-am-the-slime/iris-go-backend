use rustc_hash::{FxHashMap, FxHashSet};

use crate::syntax::GoType;

pub(super) type Symbol = u32;

/// The constant zero, against which a symbol's own bounds are kept.
pub(super) const ZERO: Symbol = 0;

/// More symbols than this in one state are not given new constraints.
pub(super) const MOST_SYMBOLS: usize = 64;

/// Difference constraints `a - b <= c`, closed under adding paths: every constraint that two
/// others imply is present.
#[derive(Clone, Default, PartialEq, Debug)]
pub(super) struct State {
    pub(super) unreachable: bool,
    pub(super) bounds: FxHashMap<Symbol, FxHashMap<Symbol, i64>>,
    /// When each symbol was last assigned, for the conditions bound to names; 0 when the paths
    /// that meet disagree.
    pub(super) generations: FxHashMap<Symbol, u32>,
    /// When the lengths behind pointers last changed.
    pub(super) heap: u32,
}

impl State {
    pub(super) fn unreachable() -> State {
        State { unreachable: true, ..State::default() }
    }

    pub(super) fn get(&self, a: Symbol, b: Symbol) -> Option<i64> {
        if a == b {
            return Some(0);
        }
        self.bounds.get(&a)?.get(&b).copied()
    }

    pub(super) fn mentions(&self, symbol: Symbol) -> bool {
        self.bounds.contains_key(&symbol)
            || self.bounds.values().any(|row| row.contains_key(&symbol))
    }

    fn symbols(&self) -> FxHashSet<Symbol> {
        let mut symbols = FxHashSet::default();
        for (a, row) in &self.bounds {
            symbols.insert(*a);
            symbols.extend(row.keys().copied());
        }
        symbols
    }

    /// Adds `a - b <= c` and every constraint it implies with the others.
    pub(super) fn add(&mut self, a: Symbol, b: Symbol, c: i128) {
        if self.unreachable || c > i64::MAX as i128 {
            return;
        }
        if a == b {
            if c < 0 {
                *self = State::unreachable();
            }
            return;
        }
        if c < i64::MIN as i128 {
            return;
        }
        if let Some(reverse) = self.get(b, a)
            && reverse as i128 + c < 0
        {
            *self = State::unreachable();
            return;
        }
        if self.get(a, b).is_some_and(|old| old as i128 <= c) {
            return;
        }
        if self.bounds.len() >= MOST_SYMBOLS
            && (!self.bounds.contains_key(&a) || !self.bounds.contains_key(&b))
        {
            return;
        }
        let mut before: Vec<(Symbol, i128)> = vec![(a, 0)];
        for (x, row) in &self.bounds {
            if *x != a
                && let Some(to_a) = row.get(&a)
            {
                before.push((*x, *to_a as i128));
            }
        }
        let mut after: Vec<(Symbol, i128)> = vec![(b, 0)];
        if let Some(row) = self.bounds.get(&b) {
            after.extend(row.iter().filter(|(y, _)| **y != b).map(|(y, c)| (*y, *c as i128)));
        }
        for (x, to_a) in &before {
            for (y, from_b) in &after {
                let bound = to_a + c + from_b;
                if x == y {
                    if bound < 0 {
                        *self = State::unreachable();
                        return;
                    }
                    continue;
                }
                if bound > i64::MAX as i128 || bound < i64::MIN as i128 {
                    continue;
                }
                let row = self.bounds.entry(*x).or_default();
                let entry = row.entry(*y).or_insert(i64::MAX);
                *entry = (*entry).min(bound as i64);
            }
        }
    }

    pub(super) fn forget(&mut self, symbol: Symbol) {
        self.bounds.remove(&symbol);
        self.bounds.retain(|_, row| {
            row.remove(&symbol);
            !row.is_empty()
        });
    }

    /// The constraints both states hold, each as loose as the looser of the two.
    pub(super) fn join(&self, other: &State) -> State {
        if self.unreachable {
            return other.clone();
        }
        if other.unreachable {
            return self.clone();
        }
        let mut bounds: FxHashMap<Symbol, FxHashMap<Symbol, i64>> = FxHashMap::default();
        for (a, row) in &self.bounds {
            let Some(other_row) = other.bounds.get(a) else { continue };
            let joined: FxHashMap<Symbol, i64> = row
                .iter()
                .filter_map(|(b, c)| other_row.get(b).map(|d| (*b, (*c).max(*d))))
                .collect();
            if !joined.is_empty() {
                bounds.insert(*a, joined);
            }
        }
        let mut generations = FxHashMap::default();
        for symbol in self.generations.keys().chain(other.generations.keys()) {
            let (left, right) = (self.generations.get(symbol), other.generations.get(symbol));
            generations.insert(*symbol, if left == right { *left.unwrap() } else { 0 });
        }
        let heap = if self.heap == other.heap { self.heap } else { 0 };
        State { unreachable: false, bounds, generations, heap }
    }

    /// `self`'s constraints that `joined`, its join with a later iteration, keeps as they
    /// were; then closed again.
    pub(super) fn widen(&self, joined: &State) -> State {
        if self.unreachable {
            return joined.clone();
        }
        let mut widened = joined.clone();
        widened.bounds = FxHashMap::default();
        for (a, row) in &self.bounds {
            let kept: FxHashMap<Symbol, i64> = row
                .iter()
                .filter(|(b, c)| joined.get(*a, **b) == Some(**c))
                .map(|(b, c)| (*b, *c))
                .collect();
            if !kept.is_empty() {
                widened.bounds.insert(*a, kept);
            }
        }
        widened.close();
        widened
    }

    /// Floyd–Warshall over the symbols present.
    fn close(&mut self) {
        let symbols: Vec<Symbol> = self.symbols().into_iter().collect();
        for k in &symbols {
            for i in &symbols {
                let Some(to_k) = self.get(*i, *k) else { continue };
                for j in &symbols {
                    if i == j {
                        continue;
                    }
                    let Some(from_k) = self.get(*k, *j) else { continue };
                    let bound = to_k as i128 + from_k as i128;
                    if bound > i64::MAX as i128 || bound < i64::MIN as i128 {
                        continue;
                    }
                    if self.get(*i, *j).is_none_or(|old| bound < old as i128) {
                        self.bounds.entry(*i).or_default().insert(*j, bound as i64);
                    }
                }
            }
        }
        for i in &symbols {
            for j in &symbols {
                if let (Some(there), Some(back)) = (self.get(*i, *j), self.get(*j, *i))
                    && i != j
                    && (there as i128 + back as i128) < 0
                {
                    *self = State::unreachable();
                    return;
                }
            }
        }
    }

    /// `a <= b + c`.
    pub(super) fn assume_at_most(&mut self, a: Value, b: Value, c: i128) {
        self.add(a.symbol, b.symbol, b.offset as i128 - a.offset as i128 + c);
    }
}

/// `symbol + offset`.
#[derive(Clone, Copy, PartialEq, Debug)]
pub(super) struct Value {
    pub(super) symbol: Symbol,
    pub(super) offset: i64,
}

impl Value {
    pub(super) fn constant(offset: i64) -> Value {
        Value { symbol: ZERO, offset }
    }

    pub(super) fn of(symbol: Symbol) -> Value {
        Value { symbol, offset: 0 }
    }

    pub(super) fn shifted(self, by: i128) -> Option<Value> {
        let offset = self.offset as i128 + by;
        (offset.abs() < 1 << 62).then_some(Value { symbol: self.symbol, offset: offset as i64 })
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub(super) enum Kind {
    Int32,
    Int,
}

impl Kind {
    pub(super) fn range(self) -> (i128, i128) {
        match self {
            Kind::Int32 => (i32::MIN as i128, i32::MAX as i128),
            Kind::Int => (i64::MIN as i128, i64::MAX as i128),
        }
    }
}

/// The integer type of an expression: a Go integer kind, or an untyped constant.
#[derive(Clone, Copy, PartialEq, Debug)]
pub(super) enum Typing {
    Typed(Kind),
    Untyped,
}

pub(super) fn kind_of_type(type_: &GoType) -> Option<Kind> {
    match type_ {
        GoType::Int => Some(Kind::Int),
        GoType::Rune => Some(Kind::Int32),
        GoType::Named(name) if matches!(name.as_str(), "int32" | "rune") => Some(Kind::Int32),
        _ => None,
    }
}
