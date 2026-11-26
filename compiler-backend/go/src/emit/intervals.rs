//! Bounds tests that the ranges of the indices prove.
//!
//! A peek, a poke and `Array.index` test their index, `i >= 0 && i < len(array)`, and
//! Euclidean `div` and `mod` correct Go's truncating `/` and `%` for negative operands. In a
//! loop over an array the test is often implied by the loop itself:
//!
//! ```go
//! for i := 1; i < size; i++ {      // size := len(elements)
//!     if i >= 0 && i < len(elements) { x = elements[i] } else { x = 0 }
//! }
//! ```
//!
//! Each function is interpreted over difference constraints `a - b <= c` between its Int
//! locals, the lengths of its arrays (`len(xs)`, `len(*xs)`) and zero. Facts come from
//! definitions (`j := i - 1`), from the conditions that dominate a statement (`if i < n`),
//! from loop headers (`for i := lo; i < hi; i++`, `range xs`), and from the arguments of every
//! call of a function that nothing else can call. Loops are iterated to a fixpoint, widening
//! the constraints that keep changing.
//!
//! A conjunct that the constraints prove true is dropped, and a test proven true or false
//! keeps only the branch that runs. `prim.IntMod` and `prim.IntDiv` become `%` and `/` when the
//! dividend is proven non-negative and the divisor positive. Go still checks every index
//! itself; only our own tests go.
//!
//! The analysis assumes nothing it cannot show:
//!
//! - Int arithmetic wraps, so `i + 1` has a range only when `i` is proven below the largest
//!   Int. An Int is Go's `int`, and no slice holds more elements than an `int` counts, so an
//!   index below a length can be incremented.
//! - A length is a fact only while the array cannot change it: a local slice until it is
//!   assigned, `*xs` until a push, a write through a pointer or a call that may change a
//!   header (the rule of `headers`).
//! - A local that a closure assigns or whose address is taken has no facts.

use rustc_hash::{FxHashMap, FxHashSet};

use super::headers::{Effects, Keeping};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

pub(super) fn prove_bounds(
    declarations: &mut [GoDeclaration],
    effects: &Effects,
    helpers: &FxHashSet<String>,
) {
    let keeping = Keeping::of(declarations, effects, helpers);
    let program = Program::of(declarations, FxHashSet::default());
    let plans: Vec<Plan> =
        declarations.iter_mut().map(|declaration| program.plan(declaration)).collect();
    let (entries, mut rewritten) = program.entries(declarations, &plans, &keeping);
    for (position, (declaration, plan)) in declarations.iter_mut().zip(&plans).enumerate() {
        if plan.rewrites
            && let Some(entry) = program.entry_of(declaration, &entries)
        {
            match rewritten.remove(&position) {
                Some((used, copy)) if used == entry => *declaration = copy,
                _ => Analysis::new(&program, &keeping, true).declaration(declaration, entry),
            }
        }
    }
}

pub(super) fn fields_that_fit(
    declarations: &mut [GoDeclaration],
    effects: &Effects,
    helpers: &FxHashSet<String>,
    candidates: &FxHashSet<String>,
) -> FxHashSet<String> {
    let keeping = Keeping::of(declarations, effects, helpers);
    let mut assumed = candidates.clone();
    while !assumed.is_empty() {
        let program = Program::of(declarations, assumed.clone());
        let plans: Vec<Plan> =
            declarations.iter_mut().map(|declaration| program.plan(declaration)).collect();
        let (entries, _) = program.entries(declarations, &plans, &keeping);
        let mut proven: FxHashMap<usize, bool> = FxHashMap::default();
        let mut unfit: FxHashSet<String> = FxHashSet::default();
        for (declaration, plan) in declarations.iter_mut().zip(&plans) {
            let entry = program.entry_of(declaration, &entries).unwrap_or(None);
            if plan.interpret {
                let mut analysis = Analysis::new(&program, &keeping, false);
                analysis.observations = Some(FxHashMap::default());
                analysis.declaration(declaration, entry);
                proven.extend(analysis.observations.unwrap_or_default());
            }
            each_field_write(declaration, &assumed, &mut |site, field| {
                if proven.get(&site) != Some(&true) {
                    unfit.insert(field.to_string());
                }
            });
        }
        if unfit.is_empty() {
            break;
        }
        assumed.retain(|field| !unfit.contains(field));
    }
    assumed
}

fn each_field_write(
    declaration: &mut GoDeclaration,
    fields: &FxHashSet<String>,
    visit: &mut dyn FnMut(usize, &str),
) {
    struct Writes<'f, 'v> {
        fields: &'f FxHashSet<String>,
        visit: &'v mut dyn FnMut(usize, &str),
    }
    impl Walk for Writes<'_, '_> {
        fn statement(&mut self, statement: &mut GoStatement) {
            if let GoStatement::Assign { targets, .. } = statement {
                for target in targets.iter() {
                    if let Some(field) = written_field(target, self.fields) {
                        (self.visit)(site_of(target), field);
                    }
                }
            }
            go_traversal::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            if let GoExpression::Composite { fields, .. } = value {
                for (label, field_value) in fields.iter() {
                    if let Some(label) =
                        label.as_deref().filter(|label| self.fields.contains(*label))
                    {
                        (self.visit)(site_of(field_value), label);
                    }
                }
            }
            go_traversal::expression(self, value);
        }
    }
    go_traversal::declaration(&mut Writes { fields, visit }, declaration);
}

fn written_field<'v>(target: &'v GoExpression, fields: &FxHashSet<String>) -> Option<&'v str> {
    match target.unattributed() {
        GoExpression::Field { name, .. } if fields.contains(name) => Some(name),
        _ => None,
    }
}

fn site_of(value: &GoExpression) -> usize {
    value as *const GoExpression as usize
}

/// Declarations rewritten while the entries were found, with the entry each was rewritten
/// under: the rewrite stands if that entry is the final one.
type Rewritten = FxHashMap<usize, (Option<Entry>, GoDeclaration)>;

/// Whether a declaration is worth interpreting: it has a test or a division to prove, or it
/// calls an internal function whose parameters facts can bound. One that is not still calls
/// its internal callees with nothing known.
struct Plan {
    interpret: bool,
    /// Whether it has a test or a division to rewrite, rather than only calls to give facts.
    rewrites: bool,
    callees: Vec<String>,
}

/// The functions of the program, and those whose every call it can see.
struct Program {
    signatures: FxHashMap<String, Signature>,
    internal: FxHashSet<String>,
    fields: FxHashSet<String>,
}

struct Signature {
    parameters: Vec<GoType>,
    result: Option<GoType>,
}

/// What every call of a function gives its parameters, as constraints between places.
#[derive(Clone, PartialEq, Debug, Default)]
struct Entry(FxHashMap<(Place, Place), i64>);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Place {
    Zero,
    Parameter(usize),
    /// The length of an array parameter: `len(xs)`, or `len(*xs)` for a pointer.
    Length(usize),
}

/// How often a function's entry may grow before its changing constraints are dropped.
const WIDEN_ENTRY_AFTER: usize = 3;

impl Program {
    fn of(declarations: &mut [GoDeclaration], fields: FxHashSet<String>) -> Program {
        let mut signatures = FxHashMap::default();
        let mut mentioned_in_text = FxHashSet::default();
        let names: Vec<String> = declarations
            .iter()
            .filter_map(|declaration| match declaration {
                GoDeclaration::Function { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect();
        for declaration in declarations.iter() {
            match declaration {
                GoDeclaration::Function { name, parameters, result, .. } => {
                    let parameters = parameters.iter().map(|(_, type_)| type_.clone()).collect();
                    signatures
                        .insert(name.clone(), Signature { parameters, result: result.clone() });
                }
                GoDeclaration::Source { template: text, .. } => {
                    names.iter().filter(|name| text.contains(name.as_str())).for_each(|name| {
                        mentioned_in_text.insert(name.clone());
                    });
                }
                GoDeclaration::Written { source: text, .. } => {
                    names.iter().filter(|name| text.contains(name.as_str())).for_each(|name| {
                        mentioned_in_text.insert(name.clone());
                    });
                }
                _ => {}
            }
        }
        let values = used_as_values(declarations);
        let mut counts: FxHashMap<&str, usize> = FxHashMap::default();
        names.iter().for_each(|name| *counts.entry(name).or_default() += 1);
        let internal = names
            .iter()
            .filter(|name| {
                let unexported = name.chars().next().is_some_and(|first| !first.is_uppercase());
                (unexported || !fields.is_empty())
                    && !matches!(name.as_str(), "main" | "init")
                    && counts[name.as_str()] == 1
                    && !values.contains(name.as_str())
                    && !mentioned_in_text.contains(name.as_str())
            })
            .cloned()
            .collect();
        Program { signatures, internal, fields }
    }

    fn plan(&self, declaration: &mut GoDeclaration) -> Plan {
        struct Scan<'p> {
            program: &'p Program,
            rewrites: bool,
            calls_bounded: bool,
            callees: Vec<String>,
        }
        impl Walk for Scan<'_> {
            fn statement(&mut self, statement: &mut GoStatement) {
                match statement {
                    GoStatement::If { condition, .. } => self.rewrites |= is_bounds_test(condition),
                    GoStatement::Define { values, .. } => {
                        self.rewrites |= values.iter().any(is_bounds_test)
                    }
                    _ => {}
                }
                go_traversal::statement(self, statement);
            }

            fn expression(&mut self, value: &mut GoExpression) {
                if let GoExpression::Call { function, .. } = value {
                    match &**function {
                        GoExpression::Qualified { package, name } => {
                            self.rewrites |=
                                package == "prim" && matches!(name.as_str(), "IntMod" | "IntDiv")
                        }
                        GoExpression::Identifier(callee)
                            if self.program.internal.contains(callee) =>
                        {
                            let bounded =
                                self.program.signatures[callee].parameters.iter().any(|type_| {
                                    kind_of_type(type_).is_some() || shape_of_type(type_).is_some()
                                });
                            self.calls_bounded |= bounded;
                            self.callees.push(callee.clone());
                        }
                        _ => {}
                    }
                }
                go_traversal::expression(self, value);
            }
        }
        let mut scan =
            Scan { program: self, rewrites: false, calls_bounded: false, callees: vec![] };
        go_traversal::declaration(&mut scan, declaration);
        if !self.fields.is_empty() {
            let mut writes = false;
            each_field_write(declaration, &self.fields, &mut |_, _| writes = true);
            let interpret = scan.calls_bounded || writes;
            return Plan { interpret, rewrites: false, callees: scan.callees };
        }
        let interpret = scan.rewrites || scan.calls_bounded;
        Plan { interpret, rewrites: scan.rewrites, callees: scan.callees }
    }

    /// The facts every call gives each internal function's parameters: a fixpoint over the
    /// calls, starting from the functions anything may call.
    fn entries(
        &self,
        declarations: &mut [GoDeclaration],
        plans: &[Plan],
        keeping: &Keeping<'_>,
    ) -> (FxHashMap<String, Entry>, Rewritten) {
        let positions: FxHashMap<String, usize> = declarations
            .iter()
            .enumerate()
            .filter_map(|(position, declaration)| match declaration {
                GoDeclaration::Function { name, .. } => Some((name.clone(), position)),
                _ => None,
            })
            .collect();
        let mut entries: FxHashMap<String, Entry> = FxHashMap::default();
        // A call from code not interpreted gives nothing: the entry knows nothing either.
        for plan in plans {
            if !plan.interpret {
                for callee in &plan.callees {
                    entries.insert(callee.clone(), Entry::default());
                }
            }
        }
        let mut updates: FxHashMap<String, usize> = FxHashMap::default();
        // Callers first, so that most functions are interpreted once, under their final entry.
        let mut pending: std::collections::VecDeque<usize> =
            (0..declarations.len()).filter(|position| plans[*position].interpret).collect();
        pending.make_contiguous().sort_by_key(|position| {
            matches!(&declarations[*position], GoDeclaration::Function { name, .. }
                if self.internal.contains(name.as_str()))
        });
        let mut rewritten = Rewritten::default();
        let mut queued: Vec<bool> = plans.iter().map(|plan| plan.interpret).collect();
        while let Some(position) = pending.pop_front() {
            queued[position] = false;
            let declaration = &mut declarations[position];
            let Some(entry) = self.entry_of(declaration, &entries) else { continue };
            let rewrites = plans[position].rewrites;
            let mut analysis = Analysis::new(self, keeping, rewrites);
            if rewrites {
                let mut copy = declaration.clone();
                analysis.declaration(&mut copy, entry.clone());
                rewritten.insert(position, (entry, copy));
            } else {
                analysis.declaration(declaration, entry);
            }
            for (callee, facts) in analysis.calls {
                let merged = match entries.get(&callee) {
                    None => facts,
                    Some(old) => {
                        let joined = old.join(&facts);
                        if updates.get(&callee).copied().unwrap_or(0) >= WIDEN_ENTRY_AFTER {
                            old.widen(&joined)
                        } else {
                            joined
                        }
                    }
                };
                if entries.get(&callee) == Some(&merged) {
                    continue;
                }
                *updates.entry(callee.clone()).or_default() += 1;
                entries.insert(callee.clone(), merged);
                if let Some(&callee_position) = positions.get(&callee)
                    && plans[callee_position].interpret
                    && !queued[callee_position]
                {
                    queued[callee_position] = true;
                    pending.push_back(callee_position);
                }
            }
        }
        (entries, rewritten)
    }

    /// The facts to analyse a declaration under: none for code anything may run, the calls'
    /// for an internal function, and nothing at all for one no call reaches.
    fn entry_of(
        &self,
        declaration: &GoDeclaration,
        entries: &FxHashMap<String, Entry>,
    ) -> Option<Option<Entry>> {
        match declaration {
            GoDeclaration::Function { name, .. } if self.internal.contains(name.as_str()) => {
                entries.get(name).map(|entry| Some(entry.clone()))
            }
            GoDeclaration::Function { .. } | GoDeclaration::Variable { .. } => Some(None),
            _ => None,
        }
    }
}

impl Entry {
    fn join(&self, other: &Entry) -> Entry {
        let mut joined = FxHashMap::default();
        for (key, value) in &self.0 {
            if let Some(other) = other.0.get(key) {
                joined.insert(*key, (*value).max(*other));
            }
        }
        Entry(joined)
    }

    /// The constraints of `self` that `joined` keeps as they were.
    fn widen(&self, joined: &Entry) -> Entry {
        let kept = self.0.iter().filter(|(key, value)| joined.0.get(key) == Some(value));
        Entry(kept.map(|(key, value)| (*key, *value)).collect())
    }
}

/// The functions some code refers to other than by calling them.
fn used_as_values(declarations: &mut [GoDeclaration]) -> FxHashSet<String> {
    struct Values(FxHashSet<String>);
    impl Walk for Values {
        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Call { function, arguments } => {
                    if !matches!(&**function, GoExpression::Identifier(_)) {
                        self.expression(function);
                    }
                    arguments.iter_mut().for_each(|argument| self.expression(argument));
                }
                GoExpression::Identifier(name) => {
                    self.0.insert(name.clone());
                }
                _ => go_traversal::expression(self, value),
            }
        }
    }
    let mut values = Values(FxHashSet::default());
    for declaration in declarations.iter_mut() {
        go_traversal::declaration(&mut values, declaration);
    }
    values.0
}

// ---------------------------------------------------------------------------------------------
// Constraints

type Symbol = u32;

/// The constant zero, against which a symbol's own bounds are kept.
const ZERO: Symbol = 0;

/// More symbols than this in one state are not given new constraints.
const MOST_SYMBOLS: usize = 64;

/// Difference constraints `a - b <= c`, closed under adding paths: every constraint that two
/// others imply is present.
#[derive(Clone, Default, PartialEq, Debug)]
struct State {
    unreachable: bool,
    bounds: FxHashMap<Symbol, FxHashMap<Symbol, i64>>,
    /// When each symbol was last assigned, for the conditions bound to names; 0 when the paths
    /// that meet disagree.
    generations: FxHashMap<Symbol, u32>,
    /// When the lengths behind pointers last changed.
    heap: u32,
}

impl State {
    fn unreachable() -> State {
        State { unreachable: true, ..State::default() }
    }

    fn get(&self, a: Symbol, b: Symbol) -> Option<i64> {
        if a == b {
            return Some(0);
        }
        self.bounds.get(&a)?.get(&b).copied()
    }

    fn mentions(&self, symbol: Symbol) -> bool {
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
    fn add(&mut self, a: Symbol, b: Symbol, c: i128) {
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

    fn forget(&mut self, symbol: Symbol) {
        self.bounds.remove(&symbol);
        self.bounds.retain(|_, row| {
            row.remove(&symbol);
            !row.is_empty()
        });
    }

    /// The constraints both states hold, each as loose as the looser of the two.
    fn join(&self, other: &State) -> State {
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
    fn widen(&self, joined: &State) -> State {
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
    fn assume_at_most(&mut self, a: Value, b: Value, c: i128) {
        self.add(a.symbol, b.symbol, b.offset as i128 - a.offset as i128 + c);
    }
}

/// `symbol + offset`.
#[derive(Clone, Copy, PartialEq, Debug)]
struct Value {
    symbol: Symbol,
    offset: i64,
}

impl Value {
    fn constant(offset: i64) -> Value {
        Value { symbol: ZERO, offset }
    }

    fn of(symbol: Symbol) -> Value {
        Value { symbol, offset: 0 }
    }

    fn shifted(self, by: i128) -> Option<Value> {
        let offset = self.offset as i128 + by;
        (offset.abs() < 1 << 62).then_some(Value { symbol: self.symbol, offset: offset as i64 })
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Kind {
    Int32,
    Int,
}

impl Kind {
    fn range(self) -> (i128, i128) {
        match self {
            Kind::Int32 => (i32::MIN as i128, i32::MAX as i128),
            Kind::Int => (i64::MIN as i128, i64::MAX as i128),
        }
    }
}

/// The integer type of an expression: a Go integer kind, or an untyped constant.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Typing {
    Typed(Kind),
    Untyped,
}

fn kind_of_type(type_: &GoType) -> Option<Kind> {
    match type_ {
        GoType::Int => Some(Kind::Int),
        GoType::Rune => Some(Kind::Int32),
        GoType::Named(name) if matches!(name.as_str(), "int32" | "rune") => Some(Kind::Int32),
        _ => None,
    }
}

fn zero_filling_shift(value: &GoExpression) -> Option<i64> {
    let GoExpression::Binary { operator: ">>", left, right } = value else { return None };
    let GoExpression::Conversion { type_: GoType::Named(source), .. } = left.as_ref() else {
        return None;
    };
    let GoExpression::Integer(shift) = right.as_ref() else { return None };
    (source == "uint" && (1..64).contains(shift)).then_some(*shift)
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Shape {
    /// A slice or a string: its length changes only when the local is assigned.
    Fixed,
    /// A pointer to a slice, whose length a push changes.
    Pointer,
}

fn shape_of_type(type_: &GoType) -> Option<Shape> {
    match type_ {
        GoType::Slice(_) | GoType::String => Some(Shape::Fixed),
        GoType::Pointer(inner) if matches!(**inner, GoType::Slice(_)) => Some(Shape::Pointer),
        _ => None,
    }
}

// ---------------------------------------------------------------------------------------------
// What a function's names are, before its statements are interpreted

/// Facts about a function's names that hold wherever they are bound.
#[derive(Default)]
struct Names {
    /// Assigned by a closure or addressed: no constraints.
    untracked: FxHashSet<String>,
    /// Assigned somewhere: a condition bound to such a name is not remembered.
    assigned: FxHashSet<String>,
    /// The array shape of names bound exactly once.
    shapes: FxHashMap<String, Shape>,
    relevant: FxHashSet<String>,
}

impl Names {
    fn of(
        parameters: &[(String, GoType)],
        body: &mut Vec<GoStatement>,
        program: &Program,
    ) -> Names {
        let mut collect = Collect { program: Some(program), ..Collect::default() };
        for (name, type_) in parameters {
            collect.bind(name, shape_of_type(type_));
        }
        collect.block(body);
        let mut shapes: FxHashMap<String, Shape> = FxHashMap::default();
        for (name, shape) in collect.declared.iter().chain(&collect.evidence) {
            if collect.binders.get(name) == Some(&1)
                && let Some(shape) = shape
            {
                shapes.entry(name.clone()).or_insert(*shape);
            }
        }
        for name in &collect.measured_through_pointers {
            if collect.binders.get(name) == Some(&1) {
                shapes.entry(name.clone()).or_insert(Shape::Pointer);
            }
        }
        // Shapes flow through definitions and from the parameters of the functions called.
        loop {
            let before = shapes.len();
            // `name := source` and `name := *source` share their array.
            for (name, source, through_pointer) in &collect.copies {
                if collect.binders.get(name) != Some(&1) || collect.binders.get(source) != Some(&1)
                {
                    continue;
                }
                let (from, to) = if *through_pointer {
                    (Shape::Pointer, Shape::Fixed)
                } else {
                    (Shape::Fixed, Shape::Fixed)
                };
                if shapes.get(source) == Some(&from) {
                    shapes.entry(name.clone()).or_insert(to);
                }
                if shapes.get(name) == Some(&to) {
                    shapes.entry(source.clone()).or_insert(from);
                }
            }
            if shapes.len() == before {
                break;
            }
        }
        let relevant = relevant_names(body, &program.fields);
        Names { untracked: collect.untracked, assigned: collect.assigned, shapes, relevant }
    }
}

/// The names whose constraints can reach a proof: those that bounds tests, divisions and
/// internal calls read, and those that the definitions and tests of relevant names read.
/// Tracking only these keeps the states of large functions small.
fn relevant_names(body: &mut Vec<GoStatement>, fields: &FxHashSet<String>) -> FxHashSet<String> {
    struct Relevance<'f> {
        fields: &'f FxHashSet<String>,
        relevant: FxHashSet<String>,
        /// When any of the first names is relevant, so are the second.
        edges: Vec<(Vec<String>, Vec<String>)>,
    }
    impl Relevance<'_> {
        fn related(&mut self, names: Vec<String>) {
            self.edges.push((names.clone(), names));
        }
    }
    impl Walk for Relevance<'_> {
        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Define { names, values } => {
                    for (position, value) in values.iter().enumerate() {
                        let targets = if names.len() == values.len() {
                            vec![names[position].clone()]
                        } else {
                            names.clone()
                        };
                        if is_bounds_test(value) {
                            self.relevant.extend(targets.iter().cloned());
                            self.relevant.extend(identifiers(value));
                        } else if is_test(value) {
                            self.related(targets.into_iter().chain(identifiers(value)).collect());
                        } else {
                            self.edges.push((targets, identifiers(value)));
                        }
                    }
                }
                GoStatement::Variable { name, value: Some(value), .. } => {
                    self.edges.push((vec![name.clone()], identifiers(value)))
                }
                GoStatement::Assign { targets, values } => {
                    for (target, value) in targets.iter().zip(values.iter()) {
                        let target = match target {
                            GoExpression::Unary { operator: "*", operand } => &**operand,
                            target => target,
                        };
                        if let GoExpression::Identifier(name) = target {
                            self.edges.push((vec![name.clone()], identifiers(value)));
                        }
                        if written_field(target, self.fields).is_some() {
                            self.relevant.extend(identifiers(value));
                        }
                    }
                }
                GoStatement::If { condition, .. } => {
                    if is_bounds_test(condition) || matches!(condition, GoExpression::Identifier(_))
                    {
                        self.relevant.extend(identifiers(condition));
                    }
                    self.related(identifiers(condition));
                }
                GoStatement::Switch { value: None, cases, .. } => {
                    for case in cases.iter() {
                        case.values.iter().for_each(|test| self.related(identifiers(test)));
                    }
                }
                GoStatement::Counting { variable, start, end, .. } => {
                    let mut names = identifiers(start);
                    names.extend(identifiers(end));
                    names.push(variable.clone());
                    self.related(names);
                }
                GoStatement::CountingDown { variable, start, .. } => {
                    self.edges.push((vec![variable.clone()], identifiers(start)))
                }
                GoStatement::Range { index: Some(index), iterable, .. } => {
                    self.edges.push((vec![index.clone()], identifiers(iterable)))
                }
                _ => {}
            }
            go_traversal::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            if let GoExpression::Call { function, arguments } = value
                && matches!(
                    &**function,
                    GoExpression::Identifier(_) | GoExpression::Qualified { .. }
                )
            {
                arguments.iter().for_each(|argument| self.relevant.extend(identifiers(argument)));
            }
            if let GoExpression::Composite { fields, .. } = value {
                for (label, field) in fields.iter() {
                    if label.as_ref().is_some_and(|label| self.fields.contains(label)) {
                        self.relevant.extend(identifiers(field));
                    }
                }
            }
            go_traversal::expression(self, value);
        }
    }
    let mut relevance = Relevance { fields, relevant: FxHashSet::default(), edges: vec![] };
    relevance.block(body);
    loop {
        let before = relevance.relevant.len();
        for (from, to) in &relevance.edges {
            if from.iter().any(|name| relevance.relevant.contains(name)) {
                relevance.relevant.extend(to.iter().cloned());
            }
        }
        if relevance.relevant.len() == before {
            return relevance.relevant;
        }
    }
}

/// The names an expression reads, function literals' bodies aside.
fn identifiers(value: &GoExpression) -> Vec<String> {
    let mut names = vec![];
    each_subexpression(value, &mut |value| {
        if let GoExpression::Identifier(name) = value {
            names.push(name.clone());
        }
    });
    names
}

fn shape_of_expression(
    value: &GoExpression,
    shapes: &FxHashMap<String, Shape>,
    program: &Program,
) -> Option<Shape> {
    match value {
        GoExpression::Identifier(name) => shapes.get(name).copied(),
        GoExpression::Unary { operator: "*", operand } => match &**operand {
            GoExpression::Identifier(name) if shapes.get(name) == Some(&Shape::Pointer) => {
                Some(Shape::Fixed)
            }
            _ => None,
        },
        GoExpression::String(_) | GoExpression::Utf16(_) => Some(Shape::Fixed),
        GoExpression::Composite { type_: GoType::Slice(_), .. } => Some(Shape::Fixed),
        GoExpression::Address(inner)
            if matches!(&**inner, GoExpression::Composite { type_: GoType::Slice(_), .. }) =>
        {
            Some(Shape::Pointer)
        }
        GoExpression::Conversion { type_, .. } => {
            shape_of_type(type_).filter(|shape| *shape == Shape::Fixed)
        }
        GoExpression::Call { function, arguments } => match &**function {
            GoExpression::Identifier(name) if name == "append" => Some(Shape::Fixed),
            GoExpression::Qualified { package, name }
                if package == "array" && name == "Bounded" =>
            {
                Some(Shape::Fixed)
            }
            GoExpression::Identifier(name) if name == "make" => match arguments.first() {
                Some(GoExpression::Type(GoType::Slice(_))) => Some(Shape::Fixed),
                _ => None,
            },
            GoExpression::Identifier(name) => {
                program.signatures.get(name)?.result.as_ref().and_then(shape_of_type)
            }
            _ => None,
        },
        _ => None,
    }
}

#[derive(Default)]
struct Collect<'p> {
    program: Option<&'p Program>,
    binders: FxHashMap<String, usize>,
    declared: Vec<(String, Option<Shape>)>,
    /// `name := source` or, when true, `name := *source`.
    copies: Vec<(String, String, bool)>,
    /// Arrays passed for a parameter of an array type.
    evidence: Vec<(String, Option<Shape>)>,
    untracked: FxHashSet<String>,
    assigned: FxHashSet<String>,
    /// Names measured or indexed through: `len(*xs)`, `(*xs)[i]`. The backend's only map type
    /// is an object's index, a struct field nothing points to, so such a name points to a
    /// slice, or to a string that only a store through the pointer changes.
    measured_through_pointers: FxHashSet<String>,
    closures: usize,
}

impl Collect<'_> {
    fn bind(&mut self, name: &str, shape: Option<Shape>) {
        *self.binders.entry(name.to_string()).or_default() += 1;
        self.declared.push((name.to_string(), shape));
    }
}

impl Walk for Collect<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values } => {
                for (position, name) in names.iter().enumerate() {
                    let value = (names.len() == values.len()).then(|| &values[position]);
                    let shape = match value {
                        Some(GoExpression::Identifier(source)) => {
                            self.copies.push((name.clone(), source.clone(), false));
                            None
                        }
                        Some(GoExpression::Unary { operator: "*", operand }) => {
                            if let GoExpression::Identifier(source) = &**operand {
                                self.copies.push((name.clone(), source.clone(), true));
                            }
                            None
                        }
                        Some(value) => self.program.and_then(|program| {
                            shape_of_expression(value, &FxHashMap::default(), program)
                        }),
                        None => None,
                    };
                    self.bind(name, shape);
                }
            }
            GoStatement::Variable { name, type_, .. } => self.bind(name, shape_of_type(type_)),
            GoStatement::IfAssert { name, .. } => self.bind(name, None),
            GoStatement::Range { index, element, .. } => {
                index.iter().for_each(|index| self.bind(index, None));
                self.bind(element, None);
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.bind(variable, None)
            }
            GoStatement::Assign { targets, .. } => {
                for target in targets.iter() {
                    if let Some(root) = super::headers::assigned_root(target) {
                        self.assigned.insert(root.to_string());
                        if self.closures > 0 {
                            self.untracked.insert(root.to_string());
                        }
                    }
                }
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Address(inner) => {
                if let Some(root) = super::aliases::target_root(inner) {
                    self.untracked.insert(root.to_string());
                }
            }
            GoExpression::Function { parameters, .. } => {
                parameters.iter().for_each(|(name, type_)| self.bind(name, shape_of_type(type_)));
                self.closures += 1;
                go_traversal::expression(self, value);
                self.closures -= 1;
                return;
            }
            GoExpression::Call { function, arguments } => {
                if let GoExpression::Identifier(callee) = &**function {
                    let parameters = self
                        .program
                        .and_then(|program| program.signatures.get(callee))
                        .map(|signature| signature.parameters.as_slice())
                        .unwrap_or(&[]);
                    for (argument, type_) in arguments.iter().zip(parameters) {
                        let evidence = match (argument, shape_of_type(type_)) {
                            (GoExpression::Identifier(name), Some(shape)) => Some((name, shape)),
                            (
                                GoExpression::Unary { operator: "*", operand },
                                Some(Shape::Fixed),
                            ) => match &**operand {
                                GoExpression::Identifier(name) => Some((name, Shape::Pointer)),
                                _ => None,
                            },
                            _ => None,
                        };
                        if let Some((name, shape)) = evidence {
                            self.evidence.push((name.clone(), Some(shape)));
                        }
                    }
                    if callee == "len"
                        && let [GoExpression::Unary { operator: "*", operand }] =
                            arguments.as_slice()
                        && let GoExpression::Identifier(pointer) = &**operand
                    {
                        self.measured_through_pointers.insert(pointer.clone());
                    }
                }
            }
            GoExpression::Index { value: indexed, .. } => {
                if let GoExpression::Unary { operator: "*", operand } = &**indexed
                    && let GoExpression::Identifier(pointer) = &**operand
                {
                    self.measured_through_pointers.insert(pointer.clone());
                }
            }
            _ => {}
        }
        go_traversal::expression(self, value);
    }
}

// ---------------------------------------------------------------------------------------------
// The interpretation of one declaration

struct Binding {
    kind: Option<Kind>,
    /// The symbol of `len(name)`, or of `len(*name)` for a pointer.
    length: Option<Symbol>,
    through_pointer: bool,
    tracked: bool,
}

/// A boolean local bound to a test, as the test read when it was bound.
#[derive(Clone)]
struct Condition {
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

struct Analysis<'p, 'k, 'e> {
    program: &'p Program,
    keeping: &'k Keeping<'e>,
    rewrite: bool,
    /// Above zero inside a loop iteration that may not be the last: no rewrites, no calls.
    quiet: usize,
    next: Symbol,
    generation: u32,
    names: Names,
    bindings: FxHashMap<Symbol, Binding>,
    scopes: Vec<FxHashMap<String, Symbol>>,
    /// The Go integer type of each symbol that has one, whose range bounds it.
    kinds: FxHashMap<Symbol, Kind>,
    lengths_through_pointers: FxHashSet<Symbol>,
    temporaries: Vec<Symbol>,
    frames: Vec<Frame>,
    conditions: FxHashMap<Symbol, Condition>,
    calls: FxHashMap<String, Entry>,
    observations: Option<FxHashMap<usize, bool>>,
}

impl<'p, 'k, 'e> Analysis<'p, 'k, 'e> {
    fn new(program: &'p Program, keeping: &'k Keeping<'e>, rewrite: bool) -> Self {
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

    fn declaration(&mut self, declaration: &mut GoDeclaration, entry: Option<Entry>) {
        match declaration {
            GoDeclaration::Function { parameters, body, .. } => {
                self.names = Names::of(parameters, body, self.program);
                let mut state = State::default();
                self.scopes.push(FxHashMap::default());
                let symbols: Vec<Symbol> = parameters
                    .iter()
                    .map(|(name, type_)| {
                        self.bind(name, kind_of_type(type_), shape_of_type(type_), &mut state)
                    })
                    .collect();
                if let Some(entry) = entry {
                    let place = |place: Place, analysis: &Self| match place {
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
        self.bindings.insert(symbol, Binding { kind, length, through_pointer, tracked });
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

    /// Forgets the symbols bound since `watermark`, keeping what they implied about the others.
    fn restrict(&self, state: &mut State, watermark: Symbol) {
        let local = |symbol: Symbol| symbol >= watermark;
        state.bounds.retain(|symbol, row| {
            row.retain(|other, _| !local(*other));
            !local(*symbol) && !row.is_empty()
        });
        state.generations.retain(|symbol, _| !local(*symbol));
    }

    // -----------------------------------------------------------------------------------------
    // Statements

    fn block(&mut self, body: &mut Vec<GoStatement>, state: &mut State) {
        let watermark = self.next;
        self.scopes.push(FxHashMap::default());
        let mut position = 0;
        while position < body.len() {
            if state.unreachable {
                break;
            }
            if self.rewriting() && self.rewrite_statement(body, position, state) {
                continue;
            }
            // A bounds test bound to a name is rewritten after it is interpreted, so that the
            // name stands for the test as written.
            let before =
                (self.rewriting() && is_bound_bounds_test(&body[position])).then(|| state.clone());
            let from = self.temporaries.len();
            self.statement(&mut body[position], state);
            self.forget_temporaries(state, from);
            if let Some(before) = before
                && let GoStatement::Define { values, .. } = &mut body[position]
            {
                self.simplify_test(&mut values[0], &before);
            }
            position += 1;
        }
        self.scopes.pop();
        self.restrict(state, watermark);
    }

    fn statement(&mut self, statement: &mut GoStatement, state: &mut State) {
        // A call's arguments are read before it runs, and the values assigned after.
        let keeps = !is_leaf(statement) || self.keeps(statement, state);
        match statement {
            GoStatement::Define { names, values } => {
                values.iter_mut().for_each(|value| self.visit(value, state));
                if !keeps {
                    self.forget_heap(state);
                }
                self.define(names, values, state);
            }
            GoStatement::Variable { name, type_, value } => {
                if let Some(value) = value {
                    self.visit(value, state);
                }
                if !keeps {
                    self.forget_heap(state);
                }
                let zero = GoExpression::Integer(0);
                let value = value.clone();
                let kind = kind_of_type(type_);
                let shape = shape_of_type(type_);
                let computed = match &value {
                    Some(value) => self.computed(value, state),
                    None if kind.is_some() => self.computed(&zero, state),
                    None => Computed {
                        length: shape.map(|_| Value::constant(0)),
                        ..Computed::default()
                    },
                };
                let symbol = self.bind(name, kind, shape, state);
                self.settle(symbol, computed, state);
            }
            GoStatement::Assign { targets, values } => {
                values.iter_mut().for_each(|value| self.visit(value, state));
                targets.iter_mut().for_each(|target| self.visit_target(target, state));
                self.observe_stores(targets, values, state);
                if !keeps {
                    self.forget_heap(state);
                }
                self.assign(targets, values, state);
            }
            GoStatement::Expression(value) => {
                let panics = matches!(value, GoExpression::Call { function, .. }
                    if matches!(&**function, GoExpression::Identifier(name) if name == "panic"));
                self.visit(value, state);
                if !keeps {
                    self.forget_heap(state);
                }
                if panics {
                    *state = State::unreachable();
                }
            }
            GoStatement::Defer(value) => self.visit(value, state),
            GoStatement::Return(value) => {
                if let Some(value) = value {
                    self.visit(value, state);
                }
                *state = State::unreachable();
            }
            GoStatement::If { condition, then, otherwise } => {
                self.visit(condition, state);
                if !self.keeps_expression(condition, state) {
                    self.forget_heap(state);
                }
                let (mut passed, mut failed) = if self.informs(condition) {
                    (self.assume(state, condition, true), self.assume(state, condition, false))
                } else {
                    (state.clone(), std::mem::take(state))
                };
                self.block(then, &mut passed);
                self.block(otherwise, &mut failed);
                *state = passed.join(&failed);
            }
            GoStatement::Switch { value, cases, default } => {
                if let Some(value) = value {
                    self.visit(value, state);
                    if !self.keeps_expression(value, state) {
                        self.forget_heap(state);
                    }
                }
                let tested = value.is_none();
                let mut rest = state.clone();
                let mut ends = State::unreachable();
                self.frames.push(Frame {
                    label: None,
                    switch: true,
                    breaks: State::unreachable(),
                    continues: State::unreachable(),
                });
                for case in cases.iter_mut() {
                    case.values.iter_mut().for_each(|test| self.visit(test, &mut rest));
                    let mut entered = if tested {
                        let mut entered = State::unreachable();
                        for test in &case.values {
                            entered = entered.join(&self.assume(&rest, test, true));
                        }
                        for test in &case.values {
                            rest = self.assume(&rest, test, false);
                        }
                        entered
                    } else {
                        rest.clone()
                    };
                    self.block(&mut case.body, &mut entered);
                    ends = ends.join(&entered);
                }
                match default {
                    Some(default) => {
                        let mut entered = rest;
                        self.block(&mut default.body, &mut entered);
                        ends = ends.join(&entered);
                    }
                    None => ends = ends.join(&rest),
                }
                let frame = self.frames.pop().expect("the switch's frame");
                ends = ends.join(&frame.breaks);
                if let Some(enclosing) = self.frames.last_mut() {
                    enclosing.continues = enclosing.continues.join(&frame.continues);
                }
                *state = ends;
            }
            GoStatement::IfAssert { name, value, then, .. } => {
                self.visit(value, state);
                let mut entered = state.clone();
                self.scopes.push(FxHashMap::default());
                self.bind(name, None, None, &mut entered);
                self.block(then, &mut entered);
                self.scopes.pop();
                *state = state.join(&entered);
            }
            GoStatement::Loop(body) => self.looping(state, None, body, Header::Forever),
            GoStatement::LabeledLoop { label, body } => {
                let label = label.clone();
                self.looping(state, Some(label), body, Header::Forever)
            }
            GoStatement::Counting { variable, start, end, body } => {
                self.visit(start, state);
                let typing =
                    [&*start, &*end].into_iter().find_map(|value| match self.typing(value) {
                        Some(Typing::Typed(kind)) => Some(kind),
                        _ => None,
                    });
                let kind = typing.or(Some(Kind::Int));
                let computed = self.computed(start, state);
                self.scopes.push(FxHashMap::default());
                let symbol = self.bind(variable, kind, None, state);
                self.settle(symbol, computed, state);
                let end = end.clone();
                self.looping(state, None, body, Header::Counting { variable: symbol, end: &end });
                self.scopes.pop();
                state.forget(symbol);
            }
            GoStatement::CountingDown { variable, start, body } => {
                self.visit(start, state);
                let kind = match self.typing(start) {
                    Some(Typing::Typed(kind)) => Some(kind),
                    _ => Some(Kind::Int),
                };
                let computed = self.computed(start, state);
                self.scopes.push(FxHashMap::default());
                let symbol = self.bind(variable, kind, None, state);
                self.settle(symbol, computed, state);
                self.looping(state, None, body, Header::CountingDown { variable: symbol });
                self.scopes.pop();
                state.forget(symbol);
            }
            GoStatement::Range { index, element, iterable, body } => {
                self.visit(iterable, state);
                let (kind, bound) = self.range_bound(iterable, state);
                let length = self.symbol();
                if let Some(bound) = bound {
                    state.assume_at_most(Value::of(length), bound, 0);
                    state.assume_at_most(bound, Value::of(length), 0);
                }
                self.scopes.push(FxHashMap::default());
                let index = index.as_ref().map(|index| self.bind(index, kind, None, state));
                self.bind(element, None, None, state);
                let header = Header::Range { index, length: bound.map(|_| length) };
                self.looping(state, None, body, header);
                self.scopes.pop();
                index.into_iter().for_each(|index| state.forget(index));
                state.forget(length);
            }
            GoStatement::Continue => {
                let state = std::mem::replace(state, State::unreachable());
                if let Some(frame) = self.frames.iter_mut().rev().find(|frame| !frame.switch) {
                    frame.continues = frame.continues.join(&state);
                }
            }
            GoStatement::Break => {
                let state = std::mem::replace(state, State::unreachable());
                if let Some(frame) = self.frames.last_mut() {
                    frame.breaks = frame.breaks.join(&state);
                }
            }
            GoStatement::BreakTo(label) => {
                let state = std::mem::replace(state, State::unreachable());
                if let Some(frame) =
                    self.frames.iter_mut().rev().find(|frame| frame.label.as_ref() == Some(label))
                {
                    frame.breaks = frame.breaks.join(&state);
                }
            }
            GoStatement::Line(_) => {}
        }
    }

    fn keeps(&self, statement: &mut GoStatement, state: &State) -> bool {
        if !self.lengths_through_pointers.iter().any(|length| state.mentions(*length)) {
            return true;
        }
        if let GoStatement::Assign { targets, values } = statement
            && let [GoExpression::Unary { operator: "*", .. }] = targets.as_slice()
        {
            // A store of the slice itself is interpreted by `assign`; its value may still call.
            let mut values: Vec<GoStatement> =
                values.iter().map(|value| GoStatement::Expression(value.clone())).collect();
            return self.keeping.keeps(&mut values);
        }
        self.keeping.keeps(std::slice::from_mut(statement))
    }

    fn keeps_expression(&self, value: &GoExpression, state: &State) -> bool {
        self.keeps(&mut GoStatement::Expression(value.clone()), state)
    }

    fn define(&mut self, names: &[String], values: &[GoExpression], state: &mut State) {
        let computed: Vec<Computed> = if names.len() == values.len() {
            values.iter().map(|value| self.computed(value, state)).collect()
        } else {
            names.iter().map(|_| Computed::default()).collect()
        };
        let kinds: Vec<Option<Kind>> = if names.len() == values.len() {
            values.iter().map(|value| self.kind_of_definition(value)).collect()
        } else {
            names.iter().map(|_| None).collect()
        };
        let condition = match (names, values) {
            ([name], [value]) if is_test(value) && !self.names.assigned.contains(name) => {
                Some(self.condition(value, state))
            }
            _ => None,
        };
        for (position, name) in names.iter().enumerate() {
            if name == "_" {
                continue;
            }
            let existing = self.scopes.last().and_then(|scope| scope.get(name).copied());
            let computed = computed[position];
            let symbol = match existing {
                Some(symbol) => {
                    let computed = self.hold(computed, state);
                    self.forget_binding(symbol, state);
                    self.settle(symbol, computed, state);
                    if let Some(condition) = &condition {
                        self.conditions.insert(symbol, condition.clone());
                    }
                    continue;
                }
                None => self.bind(name, kinds[position], None, state),
            };
            self.settle(symbol, computed, state);
            if let Some(condition) = &condition {
                self.conditions.insert(symbol, condition.clone());
            }
        }
    }

    fn assign(&mut self, targets: &[GoExpression], values: &[GoExpression], state: &mut State) {
        if targets.len() != values.len() {
            for target in targets {
                if let GoExpression::Identifier(name) = target
                    && let Some(symbol) = self.lookup(name)
                {
                    self.forget_binding(symbol, state);
                }
            }
            return;
        }
        let computed: Vec<Computed> = values
            .iter()
            .map(|value| {
                let computed = self.computed(value, state);
                self.hold(computed, state)
            })
            .collect();
        let mut stored = vec![];
        for (target, computed) in targets.iter().zip(computed) {
            match target {
                GoExpression::Identifier(name) => {
                    if let Some(symbol) = self.lookup(name) {
                        stored.push((symbol, computed));
                    }
                }
                GoExpression::Unary { operator: "*", operand } => {
                    let pointer = match &**operand {
                        GoExpression::Identifier(name) => self.lookup(name),
                        _ => None,
                    };
                    let length = pointer.and_then(|pointer| {
                        let binding = &self.bindings[&pointer];
                        binding.through_pointer.then_some(binding.length).flatten()
                    });
                    // The new slice's length goes through a temporary: forgetting every length
                    // behind a pointer forgets the old one, which it may be counted from.
                    let carried = match (length, computed.length) {
                        (Some(_), Some(value)) => {
                            let temporary = self.temporary(state, None);
                            state.assume_at_most(Value::of(temporary), value, 0);
                            state.assume_at_most(value, Value::of(temporary), 0);
                            Some(temporary)
                        }
                        _ => None,
                    };
                    self.forget_heap(state);
                    if let (Some(length), Some(temporary)) = (length, carried) {
                        state.add(length, temporary, 0);
                        state.add(temporary, length, 0);
                    }
                }
                _ => {}
            }
        }
        for (symbol, _) in &stored {
            self.forget_binding(*symbol, state);
        }
        for (symbol, computed) in stored {
            self.settle(symbol, computed, state);
        }
    }

    /// Forgets what is known of a binding's value before it is assigned.
    fn forget_binding(&mut self, symbol: Symbol, state: &mut State) {
        // An untracked binding has no constraints, no length and no generation to change.
        if self.bindings.get(&symbol).is_some_and(|binding| !binding.tracked) {
            return;
        }
        state.forget(symbol);
        let generation = self.fresh_generation();
        state.generations.insert(symbol, generation);
        if let Some(length) = self.bindings.get(&symbol).and_then(|binding| binding.length) {
            self.forget_length(state, length);
            state.add(ZERO, length, 0);
        }
        if let Some(binding) = self.bindings.get(&symbol)
            && binding.tracked
            && let Some(kind) = binding.kind
        {
            self.kinds.insert(symbol, kind);
        }
    }

    /// Gives a binding the value computed for it.
    fn settle(&mut self, symbol: Symbol, computed: Computed, state: &mut State) {
        let Some(binding) = self.bindings.get(&symbol) else { return };
        if !binding.tracked {
            return;
        }
        let length = binding.length;
        if binding.kind.is_some()
            && let Some(value) = computed.value
        {
            state.assume_at_most(Value::of(symbol), value, 0);
            state.assume_at_most(value, Value::of(symbol), 0);
        }
        if let (Some(length), Some(value)) = (length, computed.length) {
            state.assume_at_most(Value::of(length), value, 0);
            state.assume_at_most(value, Value::of(length), 0);
        }
    }

    // -----------------------------------------------------------------------------------------
    // Loops

    fn looping(
        &mut self,
        state: &mut State,
        label: Option<String>,
        body: &mut Vec<GoStatement>,
        header: Header<'_>,
    ) {
        let watermark = self.next;
        let mut head = state.clone();
        self.quiet += 1;
        let mut rounds = 0;
        loop {
            let (back, _) = self.iteration(&head, label.clone(), body, &header, watermark);
            let joined = head.join(&back);
            let next = if rounds >= 2 { head.widen(&joined) } else { joined };
            if next == head {
                break;
            }
            head = next;
            rounds += 1;
            if rounds > 12 {
                head = State { generations: head.generations, ..State::default() };
                head.generations.values_mut().for_each(|generation| *generation = 0);
                head.heap = 0;
            }
        }
        self.quiet -= 1;
        let (_, exit) = self.iteration(&head, label, body, &header, watermark);
        *state = exit;
    }

    /// One pass through the loop from `head`: the state it returns to the head with, and the
    /// state it leaves with.
    fn iteration(
        &mut self,
        head: &State,
        label: Option<String>,
        body: &mut Vec<GoStatement>,
        header: &Header<'_>,
        watermark: Symbol,
    ) -> (State, State) {
        let (mut entered, mut exit) = match header {
            Header::Forever => (head.clone(), State::unreachable()),
            Header::Counting { variable, end } => {
                let mut end = (*end).clone();
                let mut visited = head.clone();
                self.visit(&mut end, &mut visited);
                let test = GoExpression::Binary {
                    operator: "<",
                    left: Box::new(GoExpression::Identifier(String::new())),
                    right: Box::new(end),
                };
                (
                    self.assume_with(head, &test, true, Some(*variable)),
                    self.assume_with(head, &test, false, Some(*variable)),
                )
            }
            Header::CountingDown { variable } => {
                let mut entered = head.clone();
                entered.add(ZERO, *variable, 0);
                let mut exit = head.clone();
                exit.add(*variable, ZERO, -1);
                (entered, exit)
            }
            Header::Range { index, length } => {
                let mut entered = head.clone();
                if let Some(index) = index {
                    entered.forget(*index);
                    entered.add(ZERO, *index, 0);
                    if let Some(length) = length {
                        entered.add(*index, *length, -1);
                    }
                }
                (entered, head.clone())
            }
        };
        self.frames.push(Frame {
            label,
            switch: false,
            breaks: State::unreachable(),
            continues: State::unreachable(),
        });
        self.block(body, &mut entered);
        let frame = self.frames.pop().expect("the loop's frame");
        let mut back = entered.join(&frame.continues);
        self.restrict(&mut back, watermark);
        match header {
            Header::Counting { variable, .. } => self.step(&mut back, *variable, 1),
            Header::CountingDown { variable } => self.step(&mut back, *variable, -1),
            Header::Range { index: Some(index), .. } => back.forget(*index),
            _ => {}
        }
        exit = exit.join(&frame.breaks);
        self.restrict(&mut exit, watermark);
        (back, exit)
    }

    /// `variable += by`, unless the variable may wrap.
    fn step(&mut self, state: &mut State, variable: Symbol, by: i128) {
        if state.unreachable {
            return;
        }
        let kind = self.bindings[&variable].kind.unwrap_or(Kind::Int32);
        let current = Value::of(variable);
        let fits = match by.signum() {
            1 => self.upper(state, current).is_some_and(|upper| upper + by <= kind.range().1),
            _ => self.lower(state, current).is_some_and(|lower| lower + by >= kind.range().0),
        };
        let from = self.temporaries.len();
        let stepped = if fits {
            let temporary = self.temporary(state, Some(kind));
            let value = Value::of(temporary);
            state.assume_at_most(value, current, by);
            state.assume_at_most(current, value, -by);
            Some(value)
        } else {
            None
        };
        self.forget_binding(variable, state);
        if let Some(value) = stepped {
            state.assume_at_most(Value::of(variable), value, 0);
            state.assume_at_most(value, Value::of(variable), 0);
        }
        self.forget_temporaries(state, from);
    }

    /// The kind of a range loop's index and the number of its iterations.
    fn range_bound(
        &mut self,
        iterable: &GoExpression,
        state: &mut State,
    ) -> (Option<Kind>, Option<Value>) {
        if let Some(length) = self.length(iterable, state) {
            return (Some(Kind::Int), Some(length));
        }
        match self.typing(iterable) {
            Some(Typing::Typed(kind)) => (Some(kind), self.value(iterable, state)),
            _ => (None, None),
        }
    }

    // -----------------------------------------------------------------------------------------
    // Conditions

    fn condition(&mut self, test: &GoExpression, state: &mut State) -> Condition {
        // Where paths that assigned differently met, the symbol gets a generation of its own
        // here, so that the test is used only until the next assignment.
        let mut read = vec![];
        each_subexpression(test, &mut |value| {
            if let GoExpression::Identifier(name) = value {
                read.push(name.clone());
            }
        });
        for name in read {
            let Some(symbol) = self.lookup(&name) else { continue };
            let length = self.bindings.get(&symbol).and_then(|binding| binding.length);
            for symbol in [Some(symbol), length].into_iter().flatten() {
                if state.generations.get(&symbol) == Some(&0) {
                    let generation = self.fresh_generation();
                    state.generations.insert(symbol, generation);
                }
            }
        }
        if state.heap == 0 {
            state.heap = self.fresh_generation();
        }
        let mut scope = FxHashMap::default();
        let mut generations = vec![];
        let mut through_pointer = false;
        each_subexpression(test, &mut |value| match value {
            GoExpression::Identifier(name) => {
                if let Some(symbol) = self.lookup(name) {
                    scope.insert(name.clone(), symbol);
                    generations.push((symbol, state.generations.get(&symbol).copied()));
                    if let Some(length) =
                        self.bindings.get(&symbol).and_then(|binding| binding.length)
                    {
                        generations.push((length, state.generations.get(&length).copied()));
                    }
                }
            }
            GoExpression::Unary { operator: "*", .. } => through_pointer = true,
            _ => {}
        });
        let heap = through_pointer.then_some(state.heap);
        Condition { test: test.clone(), scope, generations, heap }
    }

    fn holds(&self, condition: &Condition, state: &State) -> bool {
        let unchanged = condition.generations.iter().all(|(symbol, generation)| {
            let now = state.generations.get(symbol).copied();
            now == *generation && now != Some(0)
        });
        unchanged && condition.heap.is_none_or(|heap| heap == state.heap && heap != 0)
    }

    /// Whether assuming the test can tell anything: it reads a tracked symbol, a name bound to
    /// a test, or a constant.
    fn informs(&self, test: &GoExpression) -> bool {
        let mut informs = false;
        each_subexpression(test, &mut |value| match value {
            GoExpression::Boolean(_) => informs = true,
            GoExpression::Identifier(name) => {
                informs |= self.lookup(name).is_some_and(|symbol| {
                    self.conditions.contains_key(&symbol)
                        || self.bindings.get(&symbol).is_some_and(|binding| binding.tracked)
                })
            }
            _ => {}
        });
        informs
    }

    fn assume(&mut self, state: &State, test: &GoExpression, truth: bool) -> State {
        self.assume_with(state, test, truth, None)
    }

    /// `state` where `test` is `truth`. `blank` stands for the empty name, the loop variable
    /// of a counting loop's test.
    fn assume_with(
        &mut self,
        state: &State,
        test: &GoExpression,
        truth: bool,
        blank: Option<Symbol>,
    ) -> State {
        if state.unreachable {
            return state.clone();
        }
        let from = self.temporaries.len();
        let mut assumed = state.clone();
        self.assume_into(&mut assumed, test, truth, blank);
        self.forget_temporaries(&mut assumed, from);
        assumed
    }

    fn assume_into(
        &mut self,
        state: &mut State,
        test: &GoExpression,
        truth: bool,
        blank: Option<Symbol>,
    ) {
        if state.unreachable {
            return;
        }
        match test {
            GoExpression::Boolean(value) => {
                if *value != truth {
                    *state = State::unreachable();
                }
            }
            GoExpression::Unary { operator: "!", operand } => {
                self.assume_into(state, operand, !truth, blank)
            }
            GoExpression::Binary { operator: "&&", left, right } if truth => {
                self.assume_into(state, left, true, blank);
                self.assume_into(state, right, true, blank);
            }
            GoExpression::Binary { operator: "||", left, right } if !truth => {
                self.assume_into(state, left, false, blank);
                self.assume_into(state, right, false, blank);
            }
            GoExpression::Binary { operator: operator @ ("&&" | "||"), left, right } => {
                // `a && b` false: `a` false, or `a` true and `b` false; `a || b` true dually.
                let first = *operator == "||";
                let mut one = state.clone();
                self.assume_into(&mut one, left, first, blank);
                let mut other = state.clone();
                self.assume_into(&mut other, left, !first, blank);
                self.assume_into(&mut other, right, first, blank);
                *state = one.join(&other);
            }
            GoExpression::Binary { operator, left, right }
                if matches!(*operator, "<" | "<=" | ">" | ">=" | "==" | "!=") =>
            {
                let operator = if truth { *operator } else { negated(operator) };
                let left = self.value_with(left, state, blank);
                let right = self.value_with(right, state, blank);
                let (Some(left), Some(right)) = (left, right) else { return };
                match operator {
                    "<" => state.assume_at_most(left, right, -1),
                    "<=" => state.assume_at_most(left, right, 0),
                    ">" => state.assume_at_most(right, left, -1),
                    ">=" => state.assume_at_most(right, left, 0),
                    "==" => {
                        state.assume_at_most(left, right, 0);
                        state.assume_at_most(right, left, 0);
                    }
                    _ => {}
                }
            }
            GoExpression::Identifier(name) => {
                let Some(symbol) = self.lookup(name) else { return };
                let Some(condition) = self.conditions.get(&symbol).cloned() else { return };
                if !self.holds(&condition, state) {
                    return;
                }
                self.scopes.push(condition.scope);
                self.assume_into(state, &condition.test, truth, blank);
                self.scopes.pop();
            }
            _ => {}
        }
    }

    /// Whether the state proves the test true or false.
    fn decide(&mut self, state: &State, test: &GoExpression) -> Option<bool> {
        if state.unreachable {
            return None;
        }
        if self.assume(state, test, false).unreachable {
            Some(true)
        } else if self.assume(state, test, true).unreachable {
            Some(false)
        } else {
            None
        }
    }

    // -----------------------------------------------------------------------------------------
    // Values

    fn typing(&self, value: &GoExpression) -> Option<Typing> {
        match value {
            GoExpression::Integer(_) => Some(Typing::Untyped),
            GoExpression::Attributed { value, .. } => self.typing(value),
            GoExpression::Field { name, .. } if self.program.fields.contains(name) => {
                Some(Typing::Typed(Kind::Int))
            }
            GoExpression::Identifier(name) => {
                let symbol = self.lookup(name)?;
                self.bindings.get(&symbol)?.kind.map(Typing::Typed)
            }
            GoExpression::Conversion { type_, .. } => kind_of_type(type_).map(Typing::Typed),
            GoExpression::Unary { operator: "-" | "^", operand } => self.typing(operand),
            GoExpression::Binary { operator, left, right }
                if matches!(*operator, "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "&^") =>
            {
                match (self.typing(left)?, self.typing(right)?) {
                    (Typing::Typed(left), Typing::Typed(right)) if left == right => {
                        Some(Typing::Typed(left))
                    }
                    (Typing::Typed(kind), Typing::Untyped)
                    | (Typing::Untyped, Typing::Typed(kind)) => Some(Typing::Typed(kind)),
                    (Typing::Untyped, Typing::Untyped) => Some(Typing::Untyped),
                    _ => None,
                }
            }
            GoExpression::Call { function, arguments } => match &**function {
                GoExpression::Identifier(name) if matches!(name.as_str(), "len" | "cap") => {
                    Some(Typing::Typed(Kind::Int))
                }
                GoExpression::Identifier(name) if matches!(name.as_str(), "min" | "max") => {
                    self.typing_of_extremum(arguments)
                }
                GoExpression::Identifier(name) => {
                    let result = self.program.signatures.get(name)?.result.as_ref()?;
                    kind_of_type(result).map(Typing::Typed)
                }
                GoExpression::Qualified { package, name }
                    if package == "prim"
                        && matches!(name.as_str(), "IntDiv" | "IntMod" | "ToCharCode") =>
                {
                    Some(Typing::Typed(Kind::Int))
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn typing_of_extremum(&self, arguments: &[GoExpression]) -> Option<Typing> {
        let mut typing = Typing::Untyped;
        for argument in arguments {
            let argument = self.typing(argument).unwrap_or(Typing::Typed(Kind::Int));
            typing = match (typing, argument) {
                (Typing::Untyped, other) | (other, Typing::Untyped) => other,
                (Typing::Typed(left), Typing::Typed(right)) if left == right => typing,
                _ => return None,
            };
        }
        Some(typing)
    }

    fn kind_of_definition(&self, value: &GoExpression) -> Option<Kind> {
        match self.typing(value)? {
            Typing::Typed(kind) => Some(kind),
            Typing::Untyped => Some(Kind::Int),
        }
    }

    fn computed(&mut self, value: &GoExpression, state: &mut State) -> Computed {
        Computed { value: self.value(value, state), length: self.length_of(value, state) }
    }

    /// The computed value, held by temporaries so that it survives an assignment of the
    /// symbols it was read from: `j = j - 1`.
    fn hold(&mut self, computed: Computed, state: &mut State) -> Computed {
        Computed {
            value: computed.value.map(|value| self.held(value, state)),
            length: computed.length.map(|length| self.held(length, state)),
        }
    }

    fn held(&mut self, value: Value, state: &mut State) -> Value {
        if value.symbol == ZERO {
            return value;
        }
        let temporary = Value::of(self.temporary(state, None));
        state.assume_at_most(temporary, value, 0);
        state.assume_at_most(value, temporary, 0);
        temporary
    }

    fn value(&mut self, value: &GoExpression, state: &mut State) -> Option<Value> {
        self.value_with(value, state, None)
    }

    /// The value of an Int expression as a symbol plus a constant, when it has one that does
    /// not wrap.
    fn value_with(
        &mut self,
        value: &GoExpression,
        state: &mut State,
        blank: Option<Symbol>,
    ) -> Option<Value> {
        if state.unreachable {
            return None;
        }
        let kind = match self.typing(value) {
            Some(Typing::Typed(kind)) => Some(kind),
            _ => None,
        };
        match value {
            GoExpression::Integer(constant) => Some(Value::constant(*constant)),
            GoExpression::Attributed { value, .. } => self.value_with(value, state, blank),
            GoExpression::Field { name, .. } if self.program.fields.contains(name) => {
                let (low, high) = Kind::Int32.range();
                let temporary = self.temporary(state, Some(Kind::Int32));
                state.add(ZERO, temporary, -low);
                state.add(temporary, ZERO, high);
                Some(Value::of(temporary))
            }
            GoExpression::Identifier(name) if name.is_empty() => blank.map(Value::of),
            GoExpression::Identifier(name) => {
                let symbol = self.lookup(name)?;
                let binding = self.bindings.get(&symbol)?;
                (binding.tracked && binding.kind.is_some()).then_some(Value::of(symbol))
            }
            GoExpression::Conversion { type_: GoType::Int, value: inner }
                if let Some(shift) = zero_filling_shift(inner) =>
            {
                let temporary = self.temporary(state, kind);
                state.add(ZERO, temporary, 0);
                state.add(temporary, ZERO, (1i128 << (64 - shift)) - 1);
                Some(Value::of(temporary))
            }
            GoExpression::Conversion { type_, value: inner } => {
                let target = kind_of_type(type_)?;
                let inner_value = self.value_with(inner, state, blank);
                match (target, self.typing(inner)?) {
                    (_, Typing::Untyped) => inner_value,
                    (Kind::Int, Typing::Typed(_)) => inner_value,
                    (Kind::Int32, Typing::Typed(Kind::Int32)) => inner_value,
                    (Kind::Int32, Typing::Typed(Kind::Int)) => {
                        let (low, high) = Kind::Int32.range();
                        let fits = inner_value.is_some_and(|inner| {
                            self.lower(state, inner).is_some_and(|lower| lower >= low)
                                && self.upper(state, inner).is_some_and(|upper| upper <= high)
                        });
                        if fits { inner_value } else { None }
                    }
                }
            }
            GoExpression::Call { function, arguments } => match &**function {
                GoExpression::Identifier(name) if name == "len" && arguments.len() == 1 => {
                    self.length(&arguments[0], state)
                }
                GoExpression::Identifier(name)
                    if matches!(name.as_str(), "min" | "max") && !arguments.is_empty() =>
                {
                    self.extremum(name == "min", arguments, kind?, state, blank)
                }
                GoExpression::Qualified { package, name }
                    if package == "prim" && arguments.len() == 2 =>
                {
                    match name.as_str() {
                        "IntMod" => {
                            self.remainder(&arguments[0], &arguments[1], state, blank, true)
                        }
                        "IntDiv" => self.quotient(&arguments[0], &arguments[1], state, blank),
                        _ => None,
                    }
                }
                _ => None,
            },
            GoExpression::Binary { operator: operator @ ("+" | "-"), left, right } => {
                let kind = kind?;
                let left_value = self.value_with(left, state, blank);
                let right_value = self.value_with(right, state, blank);
                self.sum(operator, left_value, right_value, kind, state)
            }
            GoExpression::Binary { operator: "%", left, right } => {
                self.remainder(left, right, state, blank, false)
            }
            GoExpression::Binary { operator: "/", left, right } => {
                self.quotient(left, right, state, blank)
            }
            GoExpression::Binary { operator: "&", left, right } => {
                let mask = [left, right].into_iter().find_map(|side| match &**side {
                    GoExpression::Integer(mask) if *mask >= 0 => Some(*mask),
                    _ => None,
                })?;
                let temporary = self.temporary(state, kind);
                state.add(ZERO, temporary, 0);
                state.add(temporary, ZERO, mask as i128);
                Some(Value::of(temporary))
            }
            GoExpression::Binary { operator: "*", left, right } => {
                let kind = kind?;
                let left = self.value_with(left, state, blank)?;
                let right = self.value_with(right, state, blank)?;
                let bounds = [
                    (self.lower(state, left)?, self.lower(state, right)?),
                    (self.lower(state, left)?, self.upper(state, right)?),
                    (self.upper(state, left)?, self.lower(state, right)?),
                    (self.upper(state, left)?, self.upper(state, right)?),
                ];
                let products: Vec<i128> =
                    bounds.iter().map(|(a, b)| a.checked_mul(*b)).collect::<Option<_>>()?;
                let (low, high) = (*products.iter().min()?, *products.iter().max()?);
                let (least, most) = kind.range();
                if low < least || high > most {
                    return None;
                }
                let temporary = self.temporary(state, Some(kind));
                state.add(ZERO, temporary, -low);
                state.add(temporary, ZERO, high);
                Some(Value::of(temporary))
            }
            _ => None,
        }
    }

    fn extremum(
        &mut self,
        least: bool,
        arguments: &[GoExpression],
        kind: Kind,
        state: &mut State,
        blank: Option<Symbol>,
    ) -> Option<Value> {
        let values: Vec<Option<Value>> =
            arguments.iter().map(|argument| self.value_with(argument, state, blank)).collect();
        let temporary = Value::of(self.temporary(state, Some(kind)));
        let mut bounds = vec![];
        for value in &values {
            let bound = match value {
                Some(value) if least => {
                    state.assume_at_most(temporary, *value, 0);
                    self.lower(state, *value)
                }
                Some(value) => {
                    state.assume_at_most(*value, temporary, 0);
                    self.upper(state, *value)
                }
                None => None,
            };
            bounds.push(bound);
        }
        let bounds: Option<Vec<i128>> = bounds.into_iter().collect();
        if let Some(bounds) = bounds {
            match least {
                true => state.add(ZERO, temporary.symbol, -bounds.into_iter().min()?),
                false => state.add(temporary.symbol, ZERO, bounds.into_iter().max()?),
            }
        }
        Some(temporary)
    }

    /// `left ± right` of the kind, when it cannot wrap.
    fn sum(
        &mut self,
        operator: &str,
        left: Option<Value>,
        right: Option<Value>,
        kind: Kind,
        state: &mut State,
    ) -> Option<Value> {
        let (left, right) = (left?, right?);
        let sign: i128 = if operator == "+" { 1 } else { -1 };
        let (least, most) = kind.range();
        if right.symbol == ZERO || (left.symbol == ZERO && sign == 1) {
            let (base, constant) = if right.symbol == ZERO {
                (left, sign * right.offset as i128)
            } else {
                (right, left.offset as i128)
            };
            let fits = if constant >= 0 {
                base.symbol == ZERO && base.offset as i128 + constant <= most
                    || self.upper(state, base).is_some_and(|upper| upper + constant <= most)
            } else {
                base.symbol == ZERO && base.offset as i128 + constant >= least
                    || self.lower(state, base).is_some_and(|lower| lower + constant >= least)
            };
            return if fits { base.shifted(constant) } else { None };
        }
        // Two symbols: each bounds the other's distance from the result.
        let (left_low, left_high) = (self.lower(state, left)?, self.upper(state, left)?);
        let (right_low, right_high) = (self.lower(state, right)?, self.upper(state, right)?);
        let (low, high) = if sign == 1 {
            (left_low + right_low, left_high + right_high)
        } else {
            (left_low - right_high, left_high - right_low)
        };
        if low < least || high > most {
            return None;
        }
        let temporary = Value::of(self.temporary(state, Some(kind)));
        state.add(ZERO, temporary.symbol, -low);
        state.add(temporary.symbol, ZERO, high);
        if sign == 1 {
            state.assume_at_most(temporary, left, right_high);
            state.assume_at_most(left, temporary, -right_low);
            state.assume_at_most(temporary, right, left_high);
            state.assume_at_most(right, temporary, -left_low);
        } else {
            state.assume_at_most(temporary, left, -right_low);
            state.assume_at_most(left, temporary, right_high);
        }
        Some(temporary)
    }

    /// Euclidean `mod` (`euclidean`) or Go's `%`, by a divisor proven positive.
    fn remainder(
        &mut self,
        dividend: &GoExpression,
        divisor: &GoExpression,
        state: &mut State,
        blank: Option<Symbol>,
        euclidean: bool,
    ) -> Option<Value> {
        let divisor = self.value_with(divisor, state, blank)?;
        if self.lower(state, divisor).is_none_or(|lower| lower < 1) {
            return None;
        }
        let dividend = self.value_with(dividend, state, blank);
        let natural = dividend
            .is_some_and(|dividend| self.lower(state, dividend).is_some_and(|lower| lower >= 0));
        if !euclidean && !natural {
            return None;
        }
        let temporary = Value::of(self.temporary(state, Some(Kind::Int)));
        state.add(ZERO, temporary.symbol, 0);
        state.assume_at_most(temporary, divisor, -1);
        if natural && let Some(dividend) = dividend {
            state.assume_at_most(temporary, dividend, 0);
        }
        Some(temporary)
    }

    /// A non-negative dividend over a positive divisor.
    fn quotient(
        &mut self,
        dividend: &GoExpression,
        divisor: &GoExpression,
        state: &mut State,
        blank: Option<Symbol>,
    ) -> Option<Value> {
        let divisor = self.value_with(divisor, state, blank)?;
        let dividend = self.value_with(dividend, state, blank)?;
        if self.lower(state, divisor).is_none_or(|lower| lower < 1)
            || self.lower(state, dividend).is_none_or(|lower| lower < 0)
        {
            return None;
        }
        let temporary = Value::of(self.temporary(state, Some(Kind::Int)));
        state.add(ZERO, temporary.symbol, 0);
        state.assume_at_most(temporary, dividend, 0);
        Some(temporary)
    }

    /// The symbol of `len(array)`, for an array whose length is known to stay.
    fn length(&mut self, array: &GoExpression, _state: &mut State) -> Option<Value> {
        let (name, through_pointer) = match array {
            GoExpression::Identifier(name) => (name, false),
            GoExpression::Unary { operator: "*", operand } => match &**operand {
                GoExpression::Identifier(name) => (name, true),
                _ => return None,
            },
            GoExpression::String(text) => return Some(Value::constant(text.len() as i64)),
            _ => return None,
        };
        let binding = self.bindings.get(&self.lookup(name)?)?;
        (binding.through_pointer == through_pointer).then_some(Value::of(binding.length?))
    }

    /// The length of a slice-valued expression.
    fn length_of(&mut self, value: &GoExpression, state: &mut State) -> Option<Value> {
        match value {
            GoExpression::Identifier(_) | GoExpression::Unary { operator: "*", .. } => {
                self.length(value, state)
            }
            GoExpression::Address(inner) => self.length_of(inner, state),
            GoExpression::Composite { type_: GoType::Slice(_), fields } => fields
                .iter()
                .all(|(key, _)| key.is_none())
                .then_some(Value::constant(fields.len() as i64)),
            GoExpression::Call { function, arguments } => match &**function {
                GoExpression::Qualified { package, name }
                    if package == "array" && name == "Bounded" && arguments.len() == 1 =>
                {
                    self.length_of(&arguments[0], state)
                }
                // `append` panics rather than wrap a length.
                GoExpression::Identifier(name) if name == "append" && !arguments.is_empty() => {
                    if arguments.iter().any(|argument| matches!(argument, GoExpression::Spread(_)))
                    {
                        return None;
                    }
                    self.length_of(&arguments[0], state)?.shifted(arguments.len() as i128 - 1)
                }
                GoExpression::Identifier(name) if name == "make" && arguments.len() >= 2 => {
                    matches!(arguments[0], GoExpression::Type(GoType::Slice(_)))
                        .then(|| self.value(&arguments[1], state))
                        .flatten()
                }
                _ => None,
            },
            _ => None,
        }
    }

    // -----------------------------------------------------------------------------------------
    // Visiting expressions: closures, calls, and the divisions they prove

    fn visit(&mut self, value: &mut GoExpression, state: &mut State) {
        if state.unreachable {
            return;
        }
        match value {
            GoExpression::Function { parameters, body, .. } => {
                let frames = std::mem::take(&mut self.frames);
                let temporaries = std::mem::take(&mut self.temporaries);
                let mut inner = State::default();
                self.scopes.push(FxHashMap::default());
                for (name, type_) in parameters.iter() {
                    self.bind(name, kind_of_type(type_), shape_of_type(type_), &mut inner);
                }
                self.block(body, &mut inner);
                self.scopes.pop();
                self.frames = frames;
                self.temporaries = temporaries;
                return;
            }
            _ => walk_children(value, |child| self.visit(child, state)),
        }
        if let GoExpression::Composite { fields, .. } = value {
            for (label, field) in fields.iter() {
                if label.as_ref().is_some_and(|label| self.program.fields.contains(label)) {
                    let fits = self.fits_in_int32(field, state);
                    self.observe(site_of(field), fits);
                }
            }
        }
        if let GoExpression::Call { function, arguments } = value {
            if let GoExpression::Identifier(callee) = &**function {
                let callee = callee.clone();
                self.call(&callee, arguments, state);
            }
            if self.rewriting()
                && let GoExpression::Qualified { package, name } = &**function
                && package == "prim"
                && matches!(name.as_str(), "IntMod" | "IntDiv")
                && arguments.len() == 2
                && self.natural_division(&arguments[0], &arguments[1], state)
            {
                let operator = if name == "IntMod" { "%" } else { "/" };
                let mut arguments = std::mem::take(arguments);
                let right = arguments.pop().expect("a divisor");
                let left = arguments.pop().expect("a dividend");
                *value =
                    GoExpression::Binary { operator, left: Box::new(left), right: Box::new(right) };
            }
        }
    }

    fn visit_target(&mut self, target: &mut GoExpression, state: &mut State) {
        match target {
            GoExpression::Identifier(_) => {}
            GoExpression::Unary { operator: "*", operand } => self.visit_target(operand, state),
            _ => self.visit(target, state),
        }
    }

    /// Whether Go's truncating division agrees with Euclidean division here: a dividend proven
    /// non-negative, a divisor proven positive, and a typed one among them for the result's type.
    fn natural_division(
        &mut self,
        dividend: &GoExpression,
        divisor: &GoExpression,
        state: &State,
    ) -> bool {
        let typed = [dividend, divisor]
            .iter()
            .any(|side| matches!(self.typing(side), Some(Typing::Typed(_))));
        let from = self.temporaries.len();
        let mut scratch = state.clone();
        let dividend = self.value(dividend, &mut scratch);
        let divisor = self.value(divisor, &mut scratch);
        let natural = dividend
            .is_some_and(|value| self.lower(&scratch, value).is_some_and(|lower| lower >= 0))
            && divisor
                .is_some_and(|value| self.lower(&scratch, value).is_some_and(|lower| lower >= 1));
        self.forget_temporaries(&mut scratch, from);
        typed && natural
    }

    fn observe_stores(&mut self, targets: &[GoExpression], values: &[GoExpression], state: &State) {
        for (position, target) in targets.iter().enumerate() {
            if written_field(target, &self.program.fields).is_none() {
                continue;
            }
            let fits =
                targets.len() == values.len() && self.fits_in_int32(&values[position], state);
            self.observe(site_of(target), fits);
        }
    }

    fn fits_in_int32(&mut self, value: &GoExpression, state: &State) -> bool {
        if self.observations.is_none() || self.quiet > 0 || state.unreachable {
            return false;
        }
        let from = self.temporaries.len();
        let mut scratch = state.clone();
        let (low, high) = Kind::Int32.range();
        let fits = self.value(value, &mut scratch).is_some_and(|value| {
            self.lower(&scratch, value).is_some_and(|lower| lower >= low)
                && self.upper(&scratch, value).is_some_and(|upper| upper <= high)
        });
        self.forget_temporaries(&mut scratch, from);
        fits
    }

    fn observe(&mut self, site: usize, fits: bool) {
        if self.quiet > 0 {
            return;
        }
        if let Some(observations) = &mut self.observations {
            let proven = observations.entry(site).or_insert(true);
            *proven &= fits;
        }
    }

    /// Records what a call of an internal function gives its parameters.
    fn call(&mut self, callee: &str, arguments: &[GoExpression], state: &State) {
        if self.quiet > 0 || state.unreachable || !self.program.internal.contains(callee) {
            return;
        }
        let Some(signature) = self.program.signatures.get(callee) else { return };
        if signature.parameters.len() != arguments.len() {
            return;
        }
        let parameters = signature.parameters.clone();
        let from = self.temporaries.len();
        let mut scratch = state.clone();
        let mut places: Vec<(Place, Value)> = vec![(Place::Zero, Value::constant(0))];
        for (position, (argument, type_)) in arguments.iter().zip(&parameters).enumerate() {
            if kind_of_type(type_).is_some()
                && let Some(value) = self.value(argument, &mut scratch)
            {
                places.push((Place::Parameter(position), value));
            }
            let length = match shape_of_type(type_) {
                Some(Shape::Fixed) => self.length(argument, &mut scratch),
                Some(Shape::Pointer) => match argument {
                    GoExpression::Identifier(_) => {
                        let dereferenced = GoExpression::Unary {
                            operator: "*",
                            operand: Box::new(argument.clone()),
                        };
                        self.length(&dereferenced, &mut scratch)
                    }
                    _ => None,
                },
                None => None,
            };
            if let Some(length) = length {
                places.push((Place::Length(position), length));
            }
        }
        let mut facts = FxHashMap::default();
        // Bounds that come from the arguments' types, which the constraints leave implicit.
        for (place, value) in &places {
            if *place == Place::Zero {
                continue;
            }
            if let Some(upper) = self.upper(&scratch, *value)
                && upper <= i64::MAX as i128
            {
                facts.insert((*place, Place::Zero), upper as i64);
            }
            if let Some(lower) = self.lower(&scratch, *value)
                && -lower <= i64::MAX as i128
            {
                facts.insert((Place::Zero, *place), (-lower) as i64);
            }
        }
        for (a, left) in &places {
            for (b, right) in &places {
                if a == b {
                    continue;
                }
                if let Some(distance) = scratch.get(left.symbol, right.symbol) {
                    let bound = distance as i128 + left.offset as i128 - right.offset as i128;
                    if bound >= i64::MIN as i128 && bound <= i64::MAX as i128 {
                        let entry = facts.entry((*a, *b)).or_insert(i64::MAX);
                        *entry = (*entry).min(bound as i64);
                    }
                }
            }
        }
        self.forget_temporaries(&mut scratch, from);
        let facts = Entry(facts);
        let merged = match self.calls.get(callee) {
            Some(old) => old.join(&facts),
            None => facts,
        };
        self.calls.insert(callee.to_string(), merged);
    }

    // -----------------------------------------------------------------------------------------
    // Rewrites

    /// Rewrites the statement at `position` by what the state proves. True when the block
    /// changed there and the statement at `position` is to be looked at again.
    fn rewrite_statement(
        &mut self,
        body: &mut Vec<GoStatement>,
        position: usize,
        state: &State,
    ) -> bool {
        match &mut body[position] {
            GoStatement::If { condition, .. } if !self.is_bounds_test(condition) => false,
            GoStatement::If { condition, then, otherwise } => {
                let decided = if self.is_inert(condition, state) {
                    self.decide(state, condition)
                } else {
                    None
                };
                match decided {
                    Some(true) => {
                        let passed = std::mem::take(then);
                        match splice(body, position, passed) {
                            Ok(()) => true,
                            // Kept as a branch, as its names would clash where it stands.
                            Err(passed) => {
                                if let GoStatement::If { then, otherwise, .. } = &mut body[position]
                                {
                                    *then = passed;
                                    otherwise.clear();
                                }
                                false
                            }
                        }
                    }
                    Some(false) => {
                        let failed = std::mem::take(otherwise);
                        match splice(body, position, failed) {
                            Ok(()) => true,
                            Err(failed) => {
                                if let GoStatement::If { otherwise, .. } = &mut body[position] {
                                    *otherwise = failed;
                                }
                                false
                            }
                        }
                    }
                    None => {
                        self.drop_proven_conjuncts(condition, state);
                        false
                    }
                }
            }
            _ => false,
        }
    }

    /// `true` for a test the state proves, else the test without the conjuncts it proves.
    fn simplify_test(&mut self, test: &mut GoExpression, state: &State) {
        if self.is_inert(test, state) && self.decide(state, test) == Some(true) {
            *test = GoExpression::Boolean(true);
        } else {
            self.drop_proven_conjuncts(test, state);
        }
    }

    /// Drops each inert conjunct of `a && b && ...` that the state and the conjuncts before
    /// it prove.
    fn drop_proven_conjuncts(&mut self, condition: &mut GoExpression, state: &State) {
        if !matches!(condition, GoExpression::Binary { operator: "&&", .. }) {
            return;
        }
        let original = condition.clone();
        let mut conjuncts = vec![];
        flatten_conjuncts(
            std::mem::replace(condition, GoExpression::Boolean(true)),
            &mut conjuncts,
        );
        let count = conjuncts.len();
        let mut assumed = state.clone();
        let mut kept: Vec<GoExpression> = vec![];
        for conjunct in conjuncts {
            if self.is_inert(&conjunct, &assumed) && self.decide(&assumed, &conjunct) == Some(true)
            {
                continue;
            }
            assumed = self.assume(&assumed, &conjunct, true);
            kept.push(conjunct);
        }
        if kept.len() == count {
            *condition = original;
            return;
        }
        *condition = kept
            .into_iter()
            .reduce(|left, right| GoExpression::Binary {
                operator: "&&",
                left: Box::new(left),
                right: Box::new(right),
            })
            .unwrap_or(GoExpression::Boolean(true));
    }

    /// A bounds test, or a name bound to one.
    fn is_bounds_test(&self, test: &GoExpression) -> bool {
        match test {
            GoExpression::Identifier(name) => self
                .lookup(name)
                .and_then(|symbol| self.conditions.get(&symbol))
                .is_some_and(|condition| is_bounds_test(&condition.test)),
            test => is_bounds_test(test),
        }
    }

    /// Whether dropping the test changes nothing but its answer: it calls nothing but `len`,
    /// cannot panic, and reads through a pointer only one whose length is known.
    fn is_inert(&self, test: &GoExpression, state: &State) -> bool {
        match test {
            GoExpression::Identifier(_) | GoExpression::Integer(_) | GoExpression::Boolean(_) => {
                true
            }
            GoExpression::Unary { operator: "!" | "-", operand } => self.is_inert(operand, state),
            GoExpression::Binary { operator, left, right } => {
                matches!(
                    *operator,
                    "&&" | "||"
                        | "<"
                        | "<="
                        | ">"
                        | ">="
                        | "=="
                        | "!="
                        | "+"
                        | "-"
                        | "*"
                        | "&"
                        | "|"
                        | "^"
                ) && self.is_inert(left, state)
                    && self.is_inert(right, state)
            }
            GoExpression::Conversion { type_, value } => {
                kind_of_type(type_).is_some() && self.is_inert(value, state)
            }
            GoExpression::Call { function, arguments } => {
                matches!(&**function, GoExpression::Identifier(name) if name == "len")
                    && arguments.len() == 1
                    && match &arguments[0] {
                        GoExpression::Identifier(_) | GoExpression::String(_) => true,
                        GoExpression::Unary { operator: "*", operand } => match &**operand {
                            GoExpression::Identifier(name) => {
                                self.lookup(name).is_some_and(|symbol| {
                                    self.bindings[&symbol]
                                        .length
                                        .is_some_and(|length| state.mentions(length))
                                })
                            }
                            _ => false,
                        },
                        _ => false,
                    }
            }
            _ => false,
        }
    }
}

enum Header<'a> {
    Forever,
    Counting { variable: Symbol, end: &'a GoExpression },
    CountingDown { variable: Symbol },
    Range { index: Option<Symbol>, length: Option<Symbol> },
}

/// What is known of an expression's value: as an integer, and as a slice's length.
#[derive(Clone, Copy, Default)]
struct Computed {
    value: Option<Value>,
    length: Option<Value>,
}

fn negated(operator: &str) -> &'static str {
    match operator {
        "<" => ">=",
        "<=" => ">",
        ">" => "<=",
        ">=" => "<",
        "==" => "!=",
        _ => "==",
    }
}

/// A comparison, a combination of comparisons, or a constant.
fn is_test(value: &GoExpression) -> bool {
    match value {
        GoExpression::Boolean(_) => true,
        GoExpression::Binary { operator, .. } => {
            matches!(*operator, "&&" | "||" | "<" | "<=" | ">" | ">=" | "==" | "!=")
        }
        GoExpression::Unary { operator: "!", operand } => is_test(operand),
        _ => false,
    }
}

/// The tests the backend emits for an index: conjuncts `i >= 0` and `i < len(xs)`, at least
/// one of them a length's.
fn is_bounds_test(test: &GoExpression) -> bool {
    fn is_length(value: &GoExpression) -> bool {
        match value {
            GoExpression::Call { function, arguments } => {
                matches!(&**function, GoExpression::Identifier(name) if name == "len")
                    && arguments.len() == 1
            }
            GoExpression::Conversion { value, .. } => is_length(value),
            _ => false,
        }
    }
    fn conjuncts<'a>(test: &'a GoExpression, into: &mut Vec<&'a GoExpression>) {
        match test {
            GoExpression::Binary { operator: "&&", left, right } => {
                conjuncts(left, into);
                conjuncts(right, into);
            }
            test => into.push(test),
        }
    }
    if !matches!(test, GoExpression::Binary { .. }) {
        return false;
    }
    let mut parts = vec![];
    conjuncts(test, &mut parts);
    let below_length = |conjunct: &GoExpression| matches!(conjunct, GoExpression::Binary { operator: "<", right, .. } if is_length(right));
    let natural = |conjunct: &GoExpression| {
        matches!(conjunct, GoExpression::Binary { operator: ">=", right, .. }
            if matches!(**right, GoExpression::Integer(0)))
    };
    parts.iter().any(|part| below_length(part))
        && parts.iter().all(|part| below_length(part) || natural(part))
}

fn is_bound_bounds_test(statement: &GoStatement) -> bool {
    matches!(statement, GoStatement::Define { names, values }
        if names.len() == 1 && values.len() == 1 && is_bounds_test(&values[0]))
}

fn is_leaf(statement: &GoStatement) -> bool {
    matches!(
        statement,
        GoStatement::Define { .. }
            | GoStatement::Variable { .. }
            | GoStatement::Assign { .. }
            | GoStatement::Expression(_)
            | GoStatement::Return(_)
    )
}

fn flatten_conjuncts(condition: GoExpression, into: &mut Vec<GoExpression>) {
    match condition {
        GoExpression::Binary { operator: "&&", left, right } => {
            flatten_conjuncts(*left, into);
            flatten_conjuncts(*right, into);
        }
        condition => into.push(condition),
    }
}

/// Calls `visit` on the expression's direct children, outside function literals.
fn walk_children(value: &mut GoExpression, mut visit: impl FnMut(&mut GoExpression)) {
    match value {
        GoExpression::Function { .. } => {}
        GoExpression::Call { function, arguments } => {
            visit(function);
            arguments.iter_mut().for_each(visit);
        }
        GoExpression::Binary { left, right, .. } => {
            visit(left);
            visit(right);
        }
        GoExpression::Index { value, index } => {
            visit(value);
            visit(index);
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. }
        | GoExpression::TypeAssertion { value, .. }
        | GoExpression::Spread(value)
        | GoExpression::Instantiation { function: value, .. }
        | GoExpression::Attributed { value, .. } => visit(value),
        GoExpression::Composite { fields, .. } => {
            fields.iter_mut().for_each(|(_, field)| visit(field))
        }
        GoExpression::Results(values) => values.iter_mut().for_each(visit),
        _ => {}
    }
}

/// Calls `visit` on the expression and everything in it, function literals' bodies aside.
fn each_subexpression(value: &GoExpression, visit: &mut impl FnMut(&GoExpression)) {
    visit(value);
    match value {
        GoExpression::Function { .. } => {}
        GoExpression::Call { function, arguments } => {
            each_subexpression(function, visit);
            arguments.iter().for_each(|argument| each_subexpression(argument, visit));
        }
        GoExpression::Binary { left, right, .. }
        | GoExpression::Index { value: left, index: right } => {
            each_subexpression(left, visit);
            each_subexpression(right, visit);
        }
        GoExpression::Unary { operand: inner, .. }
        | GoExpression::Field { value: inner, .. }
        | GoExpression::Address(inner)
        | GoExpression::Conversion { value: inner, .. }
        | GoExpression::TypeAssertion { value: inner, .. }
        | GoExpression::Spread(inner)
        | GoExpression::Instantiation { function: inner, .. }
        | GoExpression::Attributed { value: inner, .. } => each_subexpression(inner, visit),
        GoExpression::Composite { fields, .. } => {
            fields.iter().for_each(|(_, field)| each_subexpression(field, visit))
        }
        GoExpression::Results(values) => {
            values.iter().for_each(|value| each_subexpression(value, visit))
        }
        _ => {}
    }
}

/// Replaces the statement at `position` with `statements` when their names cannot clash:
/// no other statement of the block binds a name they bind, and none after them reads one.
fn splice(
    body: &mut Vec<GoStatement>,
    position: usize,
    statements: Vec<GoStatement>,
) -> Result<(), Vec<GoStatement>> {
    let bound: FxHashSet<String> = statements.iter().flat_map(top_level_names).collect();
    let clashes = !bound.is_empty()
        && body.iter().enumerate().any(|(other, statement)| {
            other != position
                && (top_level_names(statement).iter().any(|name| bound.contains(name))
                    || other > position && reads_free(statement, &bound))
        });
    if clashes {
        return Err(statements);
    }
    body.splice(position..=position, statements);
    Ok(())
}

fn top_level_names(statement: &GoStatement) -> Vec<String> {
    match statement {
        GoStatement::Define { names, .. } => {
            names.iter().filter(|name| *name != "_").cloned().collect()
        }
        GoStatement::Variable { name, .. } => vec![name.clone()],
        _ => vec![],
    }
}

/// Whether the statement reads one of `names` from outside itself.
fn reads_free(statement: &GoStatement, names: &FxHashSet<String>) -> bool {
    struct Free<'a> {
        names: &'a FxHashSet<String>,
        shadowed: Vec<FxHashSet<String>>,
        found: bool,
    }
    impl Free<'_> {
        fn visible(&self, name: &str) -> bool {
            self.names.contains(name) && !self.shadowed.iter().any(|scope| scope.contains(name))
        }
        fn shadow(&mut self, name: &str) {
            if let Some(scope) = self.shadowed.last_mut() {
                scope.insert(name.to_string());
            }
        }
    }
    impl Walk for Free<'_> {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            self.shadowed.push(FxHashSet::default());
            body.iter_mut().for_each(|statement| self.statement(statement));
            self.shadowed.pop();
        }

        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Define { .. } => {
                    go_traversal::statement(self, statement);
                    if let GoStatement::Define { names, .. } = statement {
                        names.clone().iter().for_each(|name| self.shadow(name));
                    }
                }
                GoStatement::Variable { name, .. } => {
                    let name = name.clone();
                    go_traversal::statement(self, statement);
                    self.shadow(&name);
                }
                GoStatement::Range { index, element, iterable, body } => {
                    self.expression(iterable);
                    self.shadowed.push(index.iter().chain([&*element]).cloned().collect());
                    self.block(body);
                    self.shadowed.pop();
                }
                GoStatement::Counting { variable, start, end, body } => {
                    self.expression(start);
                    self.shadowed.push([variable.clone()].into_iter().collect());
                    self.expression(end);
                    self.block(body);
                    self.shadowed.pop();
                }
                GoStatement::CountingDown { variable, start, body } => {
                    self.expression(start);
                    self.shadowed.push([variable.clone()].into_iter().collect());
                    self.block(body);
                    self.shadowed.pop();
                }
                GoStatement::IfAssert { name, value, then, .. } => {
                    self.expression(value);
                    self.shadowed.push([name.clone()].into_iter().collect());
                    self.block(then);
                    self.shadowed.pop();
                }
                _ => go_traversal::statement(self, statement),
            }
        }

        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Identifier(name) => self.found |= self.visible(name),
                GoExpression::Function { parameters, body, .. } => {
                    self.shadowed.push(parameters.iter().map(|(name, _)| name.clone()).collect());
                    self.block(body);
                    self.shadowed.pop();
                }
                _ => go_traversal::expression(self, value),
            }
        }
    }
    let mut free = Free { names, shadowed: vec![FxHashSet::default()], found: false };
    free.statement(&mut statement.clone());
    free.found
}
