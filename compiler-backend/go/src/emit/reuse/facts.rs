use rustc_hash::{FxHashMap, FxHashSet};

use super::planner::Planner;
use super::{Cells, first_unused_local};
use crate::monomorphic::traversal::visit;
use crate::monomorphic::{Function, FunctionId, Program};

const MASK_LIMIT: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Variant {
    pub(super) function: FunctionId,
    pub(super) owned: u64,
    pub(super) checked: u64,
    pub(super) donor: bool,
}

pub(super) type Ownership = (FunctionId, u64, u64);

impl Variant {
    pub(super) fn plain(function: FunctionId) -> Variant {
        Variant { function, owned: 0, checked: 0, donor: false }
    }

    pub(super) fn is_plain(self) -> bool {
        self.owned == 0 && self.checked == 0 && !self.donor
    }

    pub(super) fn is_reusing(self) -> bool {
        self.owned != 0 || self.donor
    }

    pub(super) fn ownership(self) -> Ownership {
        (self.function, self.owned, self.checked)
    }
}

pub(super) struct Facts {
    pub(super) eligible: Vec<bool>,
    pub(super) inspecting: Vec<bool>,
    pub(super) next_local: u32,
    pub(super) unowned_results: FxHashSet<Ownership>,
    pub(super) unfresh_results: FxHashSet<Ownership>,
    pub(super) donor_used: FxHashSet<Variant>,
    pub(super) writes: FxHashSet<Variant>,
    pub(super) demanded: Vec<Variant>,
    seen: FxHashSet<Variant>,
    /// Whether a demanded variant's plan may change: it was never planned, or a
    /// fact it consulted has changed since it was last planned.
    stale: Vec<bool>,
    /// The demanded variants whose plans consulted the facts of a function at an
    /// ownership mask.
    consulted_by: FxHashMap<Ownership, FxHashSet<usize>>,
}

impl Facts {
    pub(super) fn new(program: &Program, cells: &mut impl Cells, inspecting: Vec<bool>) -> Facts {
        let eligible = program
            .functions
            .iter()
            .map(|function| {
                !cells.is_effect(function.result)
                    && function.parameters.len() <= MASK_LIMIT
                    && !has_escape_hatches(function, cells)
            })
            .collect();
        let mut facts = Facts {
            eligible,
            inspecting,
            next_local: first_unused_local(program),
            unowned_results: FxHashSet::default(),
            unfresh_results: FxHashSet::default(),
            donor_used: FxHashSet::default(),
            writes: FxHashSet::default(),
            demanded: vec![],
            seen: FxHashSet::default(),
            stale: vec![],
            consulted_by: FxHashMap::default(),
        };
        for index in 0..program.functions.len() {
            facts.demand(Variant::plain(FunctionId(index as u32)));
        }
        facts
    }

    pub(super) fn demand(&mut self, variant: Variant) {
        if self.seen.insert(variant) {
            self.demanded.push(variant);
            self.stale.push(true);
        }
    }

    /// Plans every demanded variant in turn until no fact changes. A plan is a
    /// function of the facts it consults, so a variant is planned again only
    /// once one of those facts has changed.
    pub(super) fn settle(&mut self, program: &Program, cells: &mut impl Cells) {
        loop {
            let mut changed = false;
            let mut index = 0;
            while index < self.demanded.len() {
                let variant = self.demanded[index];
                let planned = index;
                index += 1;
                if !self.stale[planned] {
                    continue;
                }
                self.stale[planned] = false;
                let function = program.function(variant.function);
                let (plan, consulted) =
                    Planner::new(program, cells, self, variant).plan_consulting(function);
                for ownership in consulted {
                    self.consulted_by.entry(ownership).or_default().insert(planned);
                }
                let ownership = variant.ownership();
                let mut grown = false;
                if !plan.result_owned && self.unowned_results.insert(ownership) {
                    grown = true;
                }
                if !plan.result_fresh && self.unfresh_results.insert(ownership) {
                    grown = true;
                }
                if plan.donor_used && self.donor_used.insert(variant) {
                    grown = true;
                }
                if plan.writes && self.writes.insert(variant) {
                    grown = true;
                }
                if grown {
                    changed = true;
                    for &consulting in self.consulted_by.get(&ownership).into_iter().flatten() {
                        self.stale[consulting] = true;
                    }
                }
            }
            if !changed {
                return;
            }
        }
    }
}

fn has_escape_hatches(function: &Function, cells: &mut impl Cells) -> bool {
    let mut monotypes = vec![function.result];
    monotypes.extend(function.parameters.iter().map(|parameter| parameter.monotype));
    visit(&function.body, &mut |expression| monotypes.push(expression.monotype));
    monotypes.sort_unstable();
    monotypes.dedup();
    monotypes.into_iter().any(|monotype| cells.erases(monotype) || cells.is_suspended(monotype))
}
