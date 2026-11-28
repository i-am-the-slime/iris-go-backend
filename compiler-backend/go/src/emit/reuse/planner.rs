mod cases;
mod companions;
mod expressions;

use rustc_hash::{FxHashMap, FxHashSet};

use super::Cells;
use super::facts::{Facts, Ownership, Variant};
use super::plan::{Dynamic, Held, Origin, Plan, Spare, Token};
use crate::emit::inspection::inspects;
use crate::emit::uniqueness::{self, Forced, Scope, Shapes};
use crate::monomorphic::traversal::mentions_local;
use crate::monomorphic::{
    Expression, ExpressionKind, Function, FunctionId, Literal, LocalId, Program,
};
use crate::monotype::{DataType, MonotypeId};

pub(super) struct Planner<'a, C> {
    program: &'a Program,
    cells: &'a mut C,
    facts: &'a mut Facts,
    variant: Variant,
    next_local: u32,
    boolean: MonotypeId,
    owned: FxHashMap<LocalId, Vec<LocalId>>,
    owned_records: FxHashSet<LocalId>,
    checked: FxHashMap<LocalId, Dynamic>,
    use_companions: FxHashMap<*const Expression, Expression>,
    alternatives: Vec<Vec<LocalId>>,
    hoisted_locals: FxHashMap<(*const Expression, usize), LocalId>,
    plan: Plan,
    consulted: Vec<Ownership>,
}

impl<C: Cells> Shapes for Planner<'_, C> {
    fn inspects(&mut self, call: &Expression, argument: &Expression) -> bool {
        inspects(&self.facts.inspecting, self.cells, call, argument)
    }

    fn is_spine(&mut self, cell: MonotypeId, field: MonotypeId) -> bool {
        self.cells.cell(cell).is_some_and(|cell| self.cells.is_spine(&cell, field))
    }
}

impl<'a, C: Cells> Planner<'a, C> {
    pub(super) fn new(
        program: &'a Program,
        cells: &'a mut C,
        facts: &'a mut Facts,
        variant: Variant,
    ) -> Planner<'a, C> {
        let next_local = facts.next_local;
        let boolean = cells.boolean();
        Planner {
            program,
            cells,
            facts,
            variant,
            next_local,
            boolean,
            owned: FxHashMap::default(),
            owned_records: FxHashSet::default(),
            checked: FxHashMap::default(),
            use_companions: FxHashMap::default(),
            alternatives: vec![],
            hoisted_locals: FxHashMap::default(),
            plan: Plan::default(),
            consulted: vec![],
        }
    }

    fn fresh(&mut self) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        id
    }

    fn truth(&self, value: bool) -> Expression {
        Expression::new(ExpressionKind::Literal(Literal::Boolean(value)), self.boolean)
    }

    fn is_checking(&self) -> bool {
        self.variant.checked != 0
    }

    fn companion(&self, held: &Held) -> Option<Expression> {
        match held {
            Held::Owned | Held::Fresh => Some(self.truth(true)),
            Held::Unique(companion) => Some(companion.clone()),
            Held::Shared => None,
        }
    }

    pub(super) fn plan(self, function: &Function) -> Plan {
        self.plan_consulting(function).0
    }

    /// The plan, with the functions and ownership masks whose facts it consulted.
    pub(super) fn plan_consulting(mut self, function: &Function) -> (Plan, Vec<Ownership>) {
        let body = Scope::Expression(&function.body);
        for (position, parameter) in function.parameters.iter().enumerate() {
            let tracked = match self.cells.cell(parameter.monotype) {
                Some(data) => self.cells.is_tracked(&data),
                None => false,
            };
            if self.variant.checked & (1 << position) != 0 {
                let companion = self.fresh();
                self.plan.companions.push((position, companion));
                let companion = Expression::new(ExpressionKind::Local(companion), self.boolean);
                if !tracked {
                    continue;
                }
                if self.is_linear(parameter.id, &[], body, &Forced::default()) {
                    let dynamic = Dynamic { companion, ancestors: vec![] };
                    self.checked.insert(parameter.id, dynamic);
                } else {
                    self.companions_at_uses(parameter.id, &companion, &[], body);
                }
            } else if self.variant.owned & (1 << position) != 0
                && self.is_ownable_record(parameter, body)
            {
                self.owned_records.insert(parameter.id);
            } else if self.variant.owned & (1 << position) != 0
                && self.cells.cell(parameter.monotype).is_some()
            {
                if self.is_linear(parameter.id, &[], body, &Forced::default()) {
                    self.owned.insert(parameter.id, vec![]);
                } else if tracked {
                    let companion = self.truth(true);
                    self.companions_at_uses(parameter.id, &companion, &[], body);
                }
            }
        }
        let mut stock = vec![];
        if self.variant.donor
            && let Some(data) = self.cells.cell(function.result)
        {
            let local = self.fresh();
            self.plan.donor = Some(local);
            let origin = Origin::Donor;
            stock.push(Spare { local, data, origin, owners: vec![], condition: None });
        }
        let held = self.expression(&function.body, true, &mut stock, &mut vec![]);
        self.plan.result_owned = held.is_owned();
        self.plan.result_fresh = held.is_fresh();
        self.plan.next_local = self.next_local;
        (self.plan, self.consulted)
    }

    fn take(
        &mut self,
        data: &DataType,
        stock: &mut Vec<Spare>,
        after: &[&Expression],
        conditional: bool,
    ) -> Option<Token> {
        let position = stock.iter().position(|spare| {
            spare.data == *data
                && (conditional || spare.condition.is_none())
                && !spare
                    .owners
                    .iter()
                    .any(|&owner| after.iter().any(|expression| mentions_local(expression, owner)))
        })?;
        let spare = stock.remove(position);
        let cell = self.used(&spare);
        Some(Token { cell, condition: spare.condition })
    }

    fn used(&mut self, spare: &Spare) -> LocalId {
        let (local, alternative) = match spare.origin {
            Origin::Donor => {
                self.plan.donor_used = true;
                return spare.local;
            }
            Origin::Scrutinee { alternative } => (spare.local, alternative),
            Origin::Hoisted { case, position, alternative } => {
                let local = *self.plan.hoisted.entry((case, position)).or_insert(spare.local);
                (local, alternative)
            }
            Origin::Field { pattern, alternative } => {
                self.plan.pattern_cells.insert(pattern, spare.local);
                self.plan.materialized.insert(spare.local);
                (spare.local, alternative)
            }
        };
        self.materialize(alternative);
        local
    }

    fn materialize(&mut self, alternative: usize) {
        let locals = &self.alternatives[alternative];
        self.plan.materialized.extend(locals.iter().copied());
    }

    fn is_owned_constant(&self, id: FunctionId) -> bool {
        let function = self.program.function(id);
        function.parameters.is_empty()
            && matches!(&function.body.kind, ExpressionKind::Construct { arguments, .. } if arguments.is_empty())
    }

    fn is_linear(
        &mut self,
        target: LocalId,
        ancestors: &[LocalId],
        scope: Scope<'_>,
        forced: &Forced,
    ) -> bool {
        uniqueness::is_unique(self, target, ancestors, scope, forced)
    }

    fn conflicts(
        &mut self,
        target: LocalId,
        ancestors: &[LocalId],
        scope: Scope<'_>,
    ) -> FxHashSet<LocalId> {
        uniqueness::relatives(self, target, ancestors, scope)
    }
}
