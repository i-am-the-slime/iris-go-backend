mod conditions;
mod loops;
mod rewrites;
mod statements;
mod values;
mod visits;

use rustc_hash::{FxHashMap, FxHashSet};

use super::constraints::{Kind, State, Symbol, Value, ZERO, kind_of_type};
use super::names::{Names, Shape, shape_of_type};
use super::program::{Entry, FunctionTable, Place};
use crate::emit::headers::Keeping;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

struct SymbolBinding {
    kind: Option<Kind>,
    /// The symbol of `len(name)`, or of `len(*name)` for a pointer.
    length: Option<Symbol>,
    through_pointer: bool,
    tracked: bool,
}

/// A boolean local bound to a test, as the test read when it was bound.
#[derive(Clone)]
struct BoundTest {
    test: GoExpression,
    scope: FxHashMap<String, Symbol>,
    generations: Vec<(Symbol, Option<u32>)>,
    heap: Option<u32>,
}

/// The states that leave a loop or a switch other than at its end.
struct Frame {
    label: Option<String>,
    switch: bool,
    breaks: State,
    continues: State,
}

pub(super) struct Analysis<'p, 'k, 'e> {
    program: &'p FunctionTable,
    keeping: &'k Keeping<'e>,
    rewrite: bool,
    /// Above zero inside a loop iteration that may not be the last: no rewrites, no calls.
    quiet: usize,
    next: Symbol,
    generation: u32,
    names: Names,
    bindings: FxHashMap<Symbol, SymbolBinding>,
    scopes: Vec<FxHashMap<String, Symbol>>,
    /// The Go integer type of each symbol that has one, whose range bounds it.
    kinds: FxHashMap<Symbol, Kind>,
    lengths_through_pointers: FxHashSet<Symbol>,
    temporaries: Vec<Symbol>,
    frames: Vec<Frame>,
    conditions: FxHashMap<Symbol, BoundTest>,
    pub(super) calls: FxHashMap<String, Entry>,
    pub(super) observations: Option<FxHashMap<usize, bool>>,
}

impl<'p, 'k, 'e> Analysis<'p, 'k, 'e> {
    pub(super) fn new(
        program: &'p FunctionTable,
        keeping: &'k Keeping<'e>,
        rewrite: bool,
    ) -> Analysis<'p, 'k, 'e> {
        Analysis {
            program,
            keeping,
            rewrite,
            quiet: 0,
            next: ZERO + 1,
            generation: 1,
            names: Names::default(),
            bindings: FxHashMap::default(),
            scopes: vec![],
            kinds: FxHashMap::default(),
            lengths_through_pointers: FxHashSet::default(),
            temporaries: vec![],
            frames: vec![],
            conditions: FxHashMap::default(),
            calls: FxHashMap::default(),
            observations: None,
        }
    }

    pub(super) fn declaration(&mut self, declaration: &mut GoDeclaration, entry: Option<Entry>) {
        match declaration {
            GoDeclaration::Function { parameters, body, .. } => {
                self.names = Names::of(parameters, body, self.program);
                let mut state = State::default();
                self.scopes.push(FxHashMap::default());
                let symbols = parameters.iter().map(|(name, type_)| {
                    self.bind(name, kind_of_type(type_), shape_of_type(type_), &mut state)
                });
                let symbols: Vec<Symbol> = symbols.collect();
                if let Some(entry) = entry {
                    let place = |place: Place, analysis: &Analysis<'_, '_, '_>| match place {
                        Place::Zero => Some(ZERO),
                        Place::Parameter(position) => {
                            let symbol = symbols[position];
                            analysis.bindings[&symbol].tracked.then_some(symbol)
                        }
                        Place::Length(position) => analysis.bindings[&symbols[position]].length,
                    };
                    for ((a, b), c) in &entry.0 {
                        let (Some(left), Some(right)) = (place(*a, self), place(*b, self)) else {
                            continue;
                        };
                        state.add(left, right, *c as i128);
                    }
                }
                self.block(body, &mut state);
                self.scopes.pop();
            }
            GoDeclaration::Variable { value, .. } => {
                let mut body = vec![GoStatement::Expression(value.clone())];
                self.names = Names::of(&[], &mut body, self.program);
                self.scopes.push(FxHashMap::default());
                let mut state = State::default();
                self.visit(value, &mut state);
                self.scopes.pop();
            }
            _ => {}
        }
    }

    /// The largest the value can be: its own bound, or its distance to a symbol of a Go
    /// integer type plus that type's largest value.
    fn upper(&self, state: &State, value: Value) -> Option<i128> {
        if value.symbol == ZERO {
            return Some(value.offset as i128);
        }
        let mut best = state.get(value.symbol, ZERO).map(|bound| bound as i128);
        let mut consider = |bound: i128| best = Some(best.map_or(bound, |best| best.min(bound)));
        if let Some(kind) = self.kinds.get(&value.symbol) {
            consider(kind.range().1);
        }
        if let Some(row) = state.bounds.get(&value.symbol) {
            for (other, distance) in row {
                if let Some(kind) = self.kinds.get(other) {
                    consider(*distance as i128 + kind.range().1);
                }
            }
        }
        best.map(|best| best + value.offset as i128)
    }

    /// The smallest the value can be, as [`Self::upper`].
    fn lower(&self, state: &State, value: Value) -> Option<i128> {
        if value.symbol == ZERO {
            return Some(value.offset as i128);
        }
        let mut best = state.get(ZERO, value.symbol).map(|bound| -(bound as i128));
        let mut consider = |bound: i128| best = Some(best.map_or(bound, |best| best.max(bound)));
        if let Some(kind) = self.kinds.get(&value.symbol) {
            consider(kind.range().0);
        }
        for (other, row) in &state.bounds {
            if let (Some(distance), Some(kind)) = (row.get(&value.symbol), self.kinds.get(other)) {
                consider(kind.range().0 - *distance as i128);
            }
        }
        best.map(|best| best + value.offset as i128)
    }

    fn rewriting(&self) -> bool {
        self.rewrite && self.quiet == 0
    }

    fn symbol(&mut self) -> Symbol {
        let symbol = self.next;
        self.next += 1;
        symbol
    }

    fn fresh_generation(&mut self) -> u32 {
        self.generation += 1;
        self.generation
    }

    fn lookup(&self, name: &str) -> Option<Symbol> {
        self.scopes.iter().rev().find_map(|scope| scope.get(name).copied())
    }

    /// A new binding of `name` in the innermost scope.
    fn bind(
        &mut self,
        name: &str,
        kind: Option<Kind>,
        shape: Option<Shape>,
        state: &mut State,
    ) -> Symbol {
        let symbol = self.symbol();
        let tracked = !self.names.untracked.contains(name) && self.names.relevant.contains(name);
        let shape = shape.or_else(|| self.names.shapes.get(name).copied()).filter(|_| tracked);
        let length = shape.map(|_| self.symbol());
        let through_pointer = shape == Some(Shape::Pointer);
        if let Some(length) = length {
            state.add(ZERO, length, 0);
            // An array holds at most the largest Int's number of elements.
            self.kinds.insert(length, Kind::Int);
            if through_pointer {
                self.lengths_through_pointers.insert(length);
            }
        }
        self.bindings.insert(symbol, SymbolBinding { kind, length, through_pointer, tracked });
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), symbol);
        }
        if tracked && let Some(kind) = kind {
            self.kinds.insert(symbol, kind);
        }
        symbol
    }

    fn temporary(&mut self, _state: &mut State, kind: Option<Kind>) -> Symbol {
        let symbol = self.symbol();
        self.temporaries.push(symbol);
        if let Some(kind) = kind {
            self.kinds.insert(symbol, kind);
        }
        symbol
    }

    fn forget_temporaries(&mut self, state: &mut State, from: usize) {
        for symbol in self.temporaries.split_off(from) {
            state.forget(symbol);
        }
    }

    /// Forgets a length.
    fn forget_length(&mut self, state: &mut State, length: Symbol) {
        state.forget(length);
        let generation = self.fresh_generation();
        state.generations.insert(length, generation);
    }

    /// The lengths behind pointers may have changed.
    fn forget_heap(&mut self, state: &mut State) {
        let lengths: Vec<Symbol> = self.lengths_through_pointers.iter().copied().collect();
        for length in lengths {
            if state.mentions(length) {
                self.forget_length(state, length);
                state.add(ZERO, length, 0);
            }
        }
        state.heap = self.fresh_generation();
    }
}

/// Forgets the symbols bound since `watermark`, keeping what they implied about the others.
fn restrict(state: &mut State, watermark: Symbol) {
    let local = |symbol: Symbol| symbol >= watermark;
    state.bounds.retain(|symbol, row| {
        row.retain(|other, _| !local(*other));
        !local(*symbol) && !row.is_empty()
    });
    state.generations.retain(|symbol, _| !local(*symbol));
}
