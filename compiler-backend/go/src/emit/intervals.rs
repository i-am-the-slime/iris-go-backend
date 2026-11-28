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

mod analysis;
mod constraints;
mod names;
mod program;
mod syntax;

use rustc_hash::{FxHashMap, FxHashSet};

use super::headers::{Effects, Keeping};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};
use analysis::Analysis;
use program::{FunctionTable, Plan};

pub(super) fn prove_bounds(
    declarations: &mut [GoDeclaration],
    effects: &Effects,
    helpers: &FxHashSet<String>,
) {
    let keeping = Keeping::of(declarations, effects, helpers);
    let program = FunctionTable::of(declarations, FxHashSet::default());
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
        let program = FunctionTable::of(declarations, assumed.clone());
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
