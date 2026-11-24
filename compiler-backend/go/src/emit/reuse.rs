use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use super::field_reads::hoist_field_reads;
use super::inspection::{inspecting_functions, inspects, sequence_inspections};
use super::kept::mark_kept_fields;
use super::{Emitter, uses_local};
use crate::foreign::{Boundary, Foreign, GoFunction, GoPackage, Iteration, Operator};
use crate::monomorphic::traversal::{
    for_each_child, for_each_child_mut, for_each_guarded_child, prune_unreachable, visit,
};
use crate::monomorphic::{
    Alternative, Binding, Edge, Expression, ExpressionKind, Function, FunctionId, Guarded, Kept,
    Literal, Local, LocalId, Pattern, PatternKind, Program,
};
use crate::monotype::{DataType, Monotype, MonotypeId};
use crate::purity::{can_fail, is_deferrable, is_trivial, is_within_size};
use crate::timing::timed;

/// What the name of a variant that reuses its arguments' cells adds to its
/// function's name.
pub(super) const REUSING: &str = "Reusing";

pub(super) const CHECKED: &str = "Checked";

pub(super) trait Cells {
    fn cell(&mut self, monotype: MonotypeId) -> Option<DataType>;
    fn is_spine(&mut self, cell: &DataType, field: MonotypeId) -> bool;
    fn is_effect(&self, monotype: MonotypeId) -> bool;
    fn holds(&mut self, monotype: MonotypeId, cell: &DataType) -> bool;
    fn erases(&mut self, monotype: MonotypeId) -> bool;
    fn is_suspended(&self, monotype: MonotypeId) -> bool;
    fn function_type(&mut self, parameters: &[MonotypeId], result: MonotypeId) -> MonotypeId;
    fn is_tracked(&mut self, cell: &DataType) -> bool;
    fn tracks(&mut self, cell: &DataType, constructor: usize, field: usize) -> bool;
    fn boolean(&mut self) -> MonotypeId;
    fn is_record(&self, monotype: MonotypeId) -> bool;
}

pub(super) struct Reused {
    pub program: Program,
    pub materialized: FxHashSet<(FunctionId, LocalId)>,
    pub candidates: FxHashSet<DataType>,
}

pub(super) fn reuse_cells(program: &Program, cells: &mut impl Cells) -> Reused {
    let inspecting = timed("find inspecting functions", || inspecting_functions(program));
    let hoisted = timed("hoist field reads", || hoist_field_reads(program, cells));
    let sequenced = timed("sequence", || sequence_inspections(&hoisted, &inspecting, cells));
    let program = &sequenced;
    let mut facts = Facts::new(program, cells, inspecting);
    timed("settle ownership", || facts.settle(program, cells));
    timed("rewrite variants", || Emission::new(program, facts).finish(cells))
}

const MASK_LIMIT: usize = 64;

const USE_LIMIT: usize = 8;

const DECIDING_LIMIT: usize = 8;

const DECIDING_SIZE: usize = 12;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Variant {
    function: FunctionId,
    owned: u64,
    checked: u64,
    donor: bool,
}

type Ownership = (FunctionId, u64, u64);

impl Variant {
    fn plain(function: FunctionId) -> Variant {
        Variant { function, owned: 0, checked: 0, donor: false }
    }

    fn is_plain(self) -> bool {
        self.owned == 0 && self.checked == 0 && !self.donor
    }

    fn is_reusing(self) -> bool {
        self.owned != 0 || self.donor
    }

    fn ownership(self) -> Ownership {
        (self.function, self.owned, self.checked)
    }
}

struct Facts {
    eligible: Vec<bool>,
    inspecting: Vec<bool>,
    next_local: u32,
    unowned_results: FxHashSet<Ownership>,
    unfresh_results: FxHashSet<Ownership>,
    donor_used: FxHashSet<Variant>,
    writes: FxHashSet<Variant>,
    demanded: Vec<Variant>,
    seen: FxHashSet<Variant>,
    /// Whether a demanded variant's plan may change: it was never planned, or a
    /// fact it consulted has changed since it was last planned.
    stale: Vec<bool>,
    /// The demanded variants whose plans consulted the facts of a function at an
    /// ownership mask.
    consulted_by: FxHashMap<Ownership, FxHashSet<usize>>,
}

impl Facts {
    fn new(program: &Program, cells: &mut impl Cells, inspecting: Vec<bool>) -> Facts {
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

    fn demand(&mut self, variant: Variant) {
        if self.seen.insert(variant) {
            self.demanded.push(variant);
            self.stale.push(true);
        }
    }

    /// Plans every demanded variant in turn until no fact changes. A plan is a
    /// function of the facts it consults, so a variant is planned again only
    /// once one of those facts has changed.
    fn settle(&mut self, program: &Program, cells: &mut impl Cells) {
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

pub(super) fn first_unused_local(program: &Program) -> u32 {
    let mut next_local = 0;
    for function in &program.functions {
        for parameter in &function.parameters {
            next_local = next_local.max(parameter.id.0 + 1);
        }
        visit(&function.body, &mut |expression| {
            next_local = next_local.max(highest_local(expression) + 1);
        });
    }
    next_local
}

fn highest_local(expression: &Expression) -> u32 {
    let mut highest = 0;
    let mut bind = |local: &Local| highest = highest.max(local.id.0);
    match &expression.kind {
        ExpressionKind::Local(id) => highest = id.0,
        ExpressionKind::Lambda { parameters, .. } => parameters.iter().for_each(&mut bind),
        ExpressionKind::Let { bindings, .. } => {
            bindings.iter().for_each(|binding| bind(&binding.local))
        }
        ExpressionKind::EffectBind { local, .. }
        | ExpressionKind::EffectEach { element: local, .. } => bind(local),
        ExpressionKind::Case { alternatives, .. } => {
            alternatives.iter().for_each(|alternative| alternative.for_each_local(&mut bind))
        }
        _ => {}
    }
    highest
}

#[derive(Clone)]
struct Spare {
    local: LocalId,
    data: DataType,
    origin: Origin,
    owners: Vec<LocalId>,
    condition: Option<Expression>,
}

#[derive(Clone)]
struct Token {
    cell: LocalId,
    condition: Option<Expression>,
}

#[derive(Clone, PartialEq)]
enum Held {
    Shared,
    Owned,
    Fresh,
    Unique(Expression),
}

impl Held {
    fn is_owned(&self) -> bool {
        matches!(self, Held::Owned)
    }

    fn is_fresh(&self) -> bool {
        match self {
            Held::Owned | Held::Fresh => true,
            Held::Unique(companion) => is_true(companion),
            Held::Shared => false,
        }
    }

    fn join(self, other: Held) -> Held {
        match (self, other) {
            (Held::Owned, Held::Owned) => Held::Owned,
            (left, right) if left.is_fresh() && right.is_fresh() => Held::Fresh,
            (Held::Unique(left), Held::Unique(right)) if left == right => Held::Unique(left),
            _ => Held::Shared,
        }
    }
}

#[derive(Clone)]
struct Dynamic {
    companion: Expression,
    ancestors: Vec<LocalId>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Branch {
    Then,
    Otherwise,
    Alternative(usize, Option<usize>),
}

type Forced = FxHashMap<*const Expression, Vec<Branch>>;

#[derive(Clone, Copy)]
enum Origin {
    Donor,
    Scrutinee { alternative: usize },
    Hoisted { case: *const Expression, position: usize, alternative: usize },
    Field { pattern: *const Pattern, alternative: usize },
}

#[derive(Default, Clone)]
struct Plan {
    result_owned: bool,
    result_fresh: bool,
    donor_used: bool,
    writes: bool,
    donor: Option<LocalId>,
    companions: Vec<(usize, LocalId)>,
    constructs: FxHashMap<*const Expression, Token>,
    edges: FxHashMap<*const Expression, Vec<(usize, Expression)>>,
    calls: FxHashMap<*const Expression, (Variant, Option<LocalId>, Vec<Expression>)>,
    callbacks: FxHashMap<*const Expression, Variant>,
    hoisted: FxHashMap<(*const Expression, usize), LocalId>,
    pattern_cells: FxHashMap<*const Pattern, LocalId>,
    bindings: FxHashMap<*const Alternative, Vec<Binding>>,
    materialized: FxHashSet<LocalId>,
    next_local: u32,
}

struct Planner<'a, C> {
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

impl<'a, C: Cells> Planner<'a, C> {
    fn new(
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

    fn plan(self, function: &Function) -> Plan {
        self.plan_consulting(function).0
    }

    /// The plan, with the functions and ownership masks whose facts it consulted.
    fn plan_consulting(mut self, function: &Function) -> (Plan, Vec<Ownership>) {
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
                    .any(|&owner| after.iter().any(|expression| uses_local(expression, owner)))
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

    fn expression<'e>(
        &mut self,
        expression: &'e Expression,
        tail: bool,
        stock: &mut Vec<Spare>,
        after: &mut Vec<&'e Expression>,
    ) -> Held {
        match &expression.kind {
            ExpressionKind::Local(id) => {
                stock.retain(|spare| !spare.owners.contains(id));
                if self.owned.contains_key(id) {
                    return Held::Owned;
                }
                if let Some(dynamic) = self.checked.get(id) {
                    return Held::Unique(dynamic.companion.clone());
                }
                match self.use_companions.get(&std::ptr::from_ref(expression)) {
                    Some(companion) => Held::Unique(companion.clone()),
                    None => Held::Shared,
                }
            }
            ExpressionKind::Function(id) if self.is_owned_constant(*id) => Held::Owned,
            ExpressionKind::Function(_) => Held::Shared,
            ExpressionKind::Fail(_) => Held::Owned,
            ExpressionKind::Construct { data, constructor, arguments } => {
                let cell = self.cells.cell(expression.monotype);
                let held = self.arguments(arguments, stock, after);
                let Some(cell) = cell else {
                    let values: Vec<&Expression> = arguments.iter().collect();
                    return if self.owns_cells(&values, &held) {
                        Held::Owned
                    } else {
                        Held::Shared
                    };
                };
                let mut spine_owned = true;
                let mut edges = vec![];
                for (position, (argument, held)) in arguments.iter().zip(held).enumerate() {
                    if !self.cells.is_spine(&cell, argument.monotype) {
                        continue;
                    }
                    spine_owned &= held.is_owned();
                    if self.cells.tracks(&cell, *constructor, position)
                        && let Some(companion) = self.companion(&held)
                    {
                        edges.push((position, companion));
                    }
                }
                let key = std::ptr::from_ref(expression);
                if self.cells.is_tracked(&cell) {
                    self.plan.edges.insert(key, edges);
                }
                if !arguments.is_empty()
                    && let Some(token) = self.take(data, stock, after, true)
                {
                    self.plan.constructs.insert(key, token);
                    self.plan.writes = true;
                }
                if spine_owned { Held::Owned } else { Held::Fresh }
            }
            ExpressionKind::Apply { function, arguments } => {
                if let ExpressionKind::Function(id) = function.kind
                    && self.facts.eligible[id.0 as usize]
                    && self.program.function(id).parameters.len() == arguments.len()
                {
                    return self.call(expression, id, arguments, tail, stock, after);
                }
                self.unordered(expression, stock, after);
                Held::Shared
            }
            ExpressionKind::Foreign {
                foreign:
                    Foreign::Call {
                        boundary:
                            Boundary {
                                iteration:
                                    Some(iteration @ (Iteration::FoldLeft | Iteration::FoldRight)),
                                ..
                            },
                        ..
                    },
                arguments,
            } if arguments.len() == 3 => {
                match self.fold(expression, *iteration, arguments, stock, after) {
                    true => Held::Owned,
                    false => Held::Shared,
                }
            }
            ExpressionKind::Lambda { .. }
            | ExpressionKind::Closure { .. }
            | ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. } => {
                for_each_child(expression, &mut |child| {
                    self.expression(child, false, &mut vec![], &mut vec![]);
                });
                stock.retain(|spare| {
                    !spare.owners.iter().any(|&owner| uses_local(expression, owner))
                });
                Held::Shared
            }
            ExpressionKind::Let { bindings, body } => {
                for (position, binding) in bindings.iter().enumerate() {
                    let mark = after.len();
                    after.extend(bindings[position + 1..].iter().map(|binding| &binding.value));
                    after.push(body);
                    let held = self.expression(&binding.value, false, stock, after);
                    after.truncate(mark);
                    self.bind(&binding.local, held, Scope::Expression(expression));
                }
                self.expression(body, tail, stock, after)
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let mark = after.len();
                after.push(then);
                after.push(otherwise);
                self.expression(condition, false, stock, after);
                after.truncate(mark);
                let mut then_stock = stock.clone();
                let then_held = self.expression(then, tail, &mut then_stock, after);
                let mut otherwise_stock = stock.clone();
                let otherwise_held = self.expression(otherwise, tail, &mut otherwise_stock, after);
                stock.retain(|spare| {
                    then_stock.iter().any(|other| other.local == spare.local)
                        && otherwise_stock.iter().any(|other| other.local == spare.local)
                });
                then_held.join(otherwise_held)
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                self.case(expression, scrutinees, alternatives, tail, stock, after)
            }
            ExpressionKind::Access { record, .. }
                if let ExpressionKind::Local(id) = record.kind
                    && self.owned_records.contains(&id)
                    && self.cells.cell(expression.monotype).is_some() =>
            {
                self.unordered(expression, stock, after);
                Held::Owned
            }
            ExpressionKind::Record(fields) => {
                let values: Vec<&'e Expression> = fields.iter().map(|(_, value)| value).collect();
                let held = self.arguments_of(&values, stock, after);
                if self.owns_cells(&values, &held) { Held::Owned } else { Held::Shared }
            }
            _ => {
                self.unordered(expression, stock, after);
                Held::Shared
            }
        }
    }

    fn bind(&mut self, local: &Local, held: Held, scope: Scope<'_>) {
        let Some(data) = self.cells.cell(local.monotype) else { return };
        let Some(companion) = self.companion(&held) else { return };
        if self.is_linear(local.id, &[], scope, &Forced::default()) {
            if held.is_owned() {
                self.owned.insert(local.id, vec![]);
            } else if self.is_checking() && self.cells.is_tracked(&data) {
                self.checked.insert(local.id, Dynamic { companion, ancestors: vec![] });
            }
        } else if self.cells.is_tracked(&data) {
            self.companions_at_uses(local.id, &companion, &[], scope);
        }
    }

    fn fold<'e>(
        &mut self,
        expression: &'e Expression,
        iteration: Iteration,
        arguments: &'e [Expression],
        stock: &mut Vec<Spare>,
        after: &mut Vec<&'e Expression>,
    ) -> bool {
        let [callback, initial, array] = arguments else { unreachable!() };
        let mark = after.len();
        after.extend([callback, array]);
        let initial_owned = self.expression(initial, false, stock, after).is_owned();
        after.truncate(mark);
        after.extend([callback, initial]);
        self.expression(array, false, stock, after);
        after.truncate(mark);
        stock.retain(|spare| !spare.owners.iter().any(|&owner| uses_local(callback, owner)));
        let accumulator = match iteration {
            Iteration::FoldLeft => 0,
            _ => 1,
        };
        let ownable = self.cells.cell(expression.monotype).is_some()
            || self.cells.is_record(expression.monotype);
        if initial_owned && ownable && self.owned_callback(callback, accumulator) {
            return true;
        }
        self.expression(callback, false, &mut vec![], &mut vec![]);
        false
    }

    fn owned_callback(&mut self, callback: &Expression, accumulator: usize) -> bool {
        let (head, leading): (&Expression, &[Expression]) = match &callback.kind {
            ExpressionKind::Apply { function, arguments } => (function, arguments),
            _ => (callback, &[]),
        };
        if let ExpressionKind::Function(id) = head.kind {
            let position = leading.len() + accumulator;
            let function = self.program.function(id);
            if !self.facts.eligible[id.0 as usize]
                || function.parameters.len() != leading.len() + 2
                || self.cells.cell(function.parameters[position].monotype).is_none()
            {
                return false;
            }
            for argument in leading {
                self.expression(argument, false, &mut vec![], &mut vec![]);
            }
            let variant = Variant { function: id, owned: 1 << position, checked: 0, donor: false };
            self.facts.demand(variant);
            self.consulted.push(variant.ownership());
            if self.facts.unowned_results.contains(&variant.ownership()) {
                return false;
            }
            if self.facts.writes.contains(&variant) {
                self.plan.callbacks.insert(std::ptr::from_ref(head), variant);
                self.plan.writes = true;
            }
            return true;
        }
        let mut parameters = vec![];
        let mut body = callback;
        while parameters.len() < 2 {
            let ExpressionKind::Lambda { parameters: more, body: inner } = &body.kind else {
                return false;
            };
            parameters.extend(more.iter());
            body = inner;
        }
        if parameters.len() != 2 {
            return false;
        }
        let accumulator = parameters[accumulator];
        if self.cells.is_record(accumulator.monotype) {
            return self.owned_record_callback(accumulator.id, body);
        }
        if self.cells.cell(accumulator.monotype).is_none()
            || !self.is_linear(accumulator.id, &[], Scope::Expression(body), &Forced::default())
        {
            return false;
        }
        let saved = self.plan.clone();
        self.owned.insert(accumulator.id, vec![]);
        if self.expression(body, false, &mut vec![], &mut vec![]).is_owned() {
            return true;
        }
        self.owned.remove(&accumulator.id);
        self.plan = saved;
        false
    }

    fn owned_record_callback(&mut self, accumulator: LocalId, body: &Expression) -> bool {
        if !reads_cell_fields_once(self.cells, body, accumulator, &mut vec![]) {
            return false;
        }
        let saved = self.plan.clone();
        self.owned_records.insert(accumulator);
        if self.expression(body, false, &mut vec![], &mut vec![]).is_owned() {
            return true;
        }
        self.owned_records.remove(&accumulator);
        self.plan = saved;
        false
    }

    fn owns_cells(&mut self, values: &[&Expression], held: &[Held]) -> bool {
        let mut cells = vec![];
        for value in values {
            if let Some(cell) = self.cells.cell(value.monotype) {
                cells.push(cell);
            }
        }
        if cells.is_empty() {
            return false;
        }
        for (value, held) in values.iter().zip(held) {
            if self.cells.cell(value.monotype).is_some() {
                if !held.is_owned() {
                    return false;
                }
                continue;
            }
            for cell in &cells {
                if self.cells.holds(value.monotype, cell) {
                    return false;
                }
            }
        }
        true
    }

    fn unordered<'e>(
        &mut self,
        expression: &'e Expression,
        stock: &mut Vec<Spare>,
        after: &mut Vec<&'e Expression>,
    ) {
        let mut children = vec![];
        for_each_child(expression, &mut |child| children.push(child));
        self.arguments_of(&children, stock, after);
    }

    fn arguments<'e>(
        &mut self,
        arguments: &'e [Expression],
        stock: &mut Vec<Spare>,
        after: &mut Vec<&'e Expression>,
    ) -> Vec<Held> {
        let arguments: Vec<&'e Expression> = arguments.iter().collect();
        self.arguments_of(&arguments, stock, after)
    }

    fn arguments_of<'e>(
        &mut self,
        arguments: &[&'e Expression],
        stock: &mut Vec<Spare>,
        after: &mut Vec<&'e Expression>,
    ) -> Vec<Held> {
        let mut owned = vec![];
        for (position, argument) in arguments.iter().enumerate() {
            let mark = after.len();
            for (other, sibling) in arguments.iter().enumerate() {
                if other != position {
                    after.push(sibling);
                }
            }
            owned.push(self.expression(argument, false, stock, after));
            after.truncate(mark);
        }
        owned
    }

    fn call<'e>(
        &mut self,
        expression: &'e Expression,
        callee: FunctionId,
        arguments: &'e [Expression],
        tail: bool,
        stock: &mut Vec<Spare>,
        after: &mut Vec<&'e Expression>,
    ) -> Held {
        let argument_held = self.arguments(arguments, stock, after);
        let program = self.program;
        let parameters = &program.function(callee).parameters;
        let mut owned = 0u64;
        let mut checked = 0u64;
        let mut companions = vec![];
        for (position, (argument, held)) in arguments.iter().zip(argument_held).enumerate() {
            let borrowed = inspects(&self.facts.inspecting, self.cells, expression, argument);
            let Some(data) = self.cells.cell(parameters[position].monotype) else { continue };
            if borrowed {
                continue;
            }
            match held {
                Held::Owned => owned |= 1 << position,
                Held::Fresh if self.is_checking() && self.cells.is_tracked(&data) => {
                    checked |= 1 << position;
                    companions.push(self.truth(true));
                }
                Held::Unique(companion) if self.cells.is_tracked(&data) => {
                    checked |= 1 << position;
                    companions.push(companion);
                }
                _ => {}
            }
        }
        let variant = Variant { function: callee, owned, checked, donor: false };
        self.facts.demand(variant);
        self.consulted.push(variant.ownership());
        let result = if !self.facts.unowned_results.contains(&variant.ownership()) {
            Held::Owned
        } else if !self.facts.unfresh_results.contains(&variant.ownership()) {
            Held::Fresh
        } else {
            Held::Shared
        };
        let mut target = None;
        if tail
            && let Some(data) = self.cells.cell(expression.monotype)
            && stock.iter().any(|spare| spare.data == data && spare.condition.is_none())
        {
            let donating = Variant { donor: true, ..variant };
            self.facts.demand(donating);
            if self.facts.donor_used.contains(&donating)
                && self.permits(donating, tail)
                && let Some(donor) = self.take(&data, stock, after, false)
            {
                target = Some((donating, Some(donor.cell)));
            }
        }
        if target.is_none()
            && !variant.is_plain()
            && self.facts.writes.contains(&variant)
            && self.permits(variant, tail)
        {
            target = Some((variant, None));
        }
        if let Some((target, _)) = target
            && (target.donor || self.facts.writes.contains(&target))
        {
            self.plan.writes = true;
        }
        if let Some((target, donor)) = target {
            let call = (target, donor, companions);
            self.plan.calls.insert(std::ptr::from_ref(expression), call);
        }
        result
    }

    fn permits(&self, target: Variant, tail: bool) -> bool {
        if !tail || target.function != self.variant.function || target == self.variant {
            return true;
        }
        let current = self.variant;
        let within = target.owned & !current.owned == 0;
        let fewer_owned = target.owned != current.owned;
        let newly_checked = current.checked == 0;
        target.checked != 0
            && !target.donor
            && within
            && (fewer_owned || newly_checked || current.donor)
    }

    fn case<'e>(
        &mut self,
        expression: &'e Expression,
        scrutinees: &'e [Expression],
        alternatives: &'e [Alternative],
        tail: bool,
        stock: &mut Vec<Spare>,
        after: &mut Vec<&'e Expression>,
    ) -> Held {
        let case = std::ptr::from_ref(expression);
        let mut sources = vec![];
        for (position, scrutinee) in scrutinees.iter().enumerate() {
            let source = match &scrutinee.kind {
                ExpressionKind::Local(id) => {
                    if let Some(ancestors) = self.owned.get(id) {
                        let mut owners = ancestors.clone();
                        owners.push(*id);
                        Source::Owned { top: Top::Local(*id), owners }
                    } else if let Some(dynamic) = self.checked.get(id) {
                        let mut owners = dynamic.ancestors.clone();
                        owners.push(*id);
                        let companion = dynamic.companion.clone();
                        Source::Checked { top: Top::Local(*id), owners, companion }
                    } else {
                        Source::Shared
                    }
                }
                _ => {
                    let mark = after.len();
                    after.extend(&scrutinees[position + 1..]);
                    after.extend(alternatives.iter().flat_map(alternative_expressions));
                    let held = self.expression(scrutinee, false, stock, after);
                    after.truncate(mark);
                    let top = Top::Hoisted(case, position);
                    match self.cells.cell(scrutinee.monotype) {
                        Some(_) if held.is_owned() => Source::Owned { top, owners: vec![] },
                        None if held.is_owned() => Source::OwnedFields,
                        Some(data) if self.is_checking() && self.cells.is_tracked(&data) => {
                            match self.companion(&held) {
                                Some(companion) => {
                                    let local = self.hoisted_local(case, position);
                                    self.plan.hoisted.insert((case, position), local);
                                    Source::Checked { top, owners: vec![], companion }
                                }
                                None => Source::Shared,
                            }
                        }
                        _ => Source::Shared,
                    }
                }
            };
            sources.push(source);
        }
        let mut held: Option<Held> = None;
        let mut remaining = stock.clone();
        for alternative in alternatives {
            let index = self.alternatives.len();
            let mut bound = vec![];
            for pattern in &alternative.patterns {
                pattern.for_each_local(&mut |local| bound.push(local.id));
            }
            self.alternatives.push(bound);
            let mut alternative_stock = stock.clone();
            let mut bindings = vec![];
            for (pattern, source) in alternative.patterns.iter().zip(&sources) {
                match source {
                    Source::Owned { top, owners } => {
                        self.materialize(index);
                        self.pattern(
                            pattern,
                            Some(owners.clone()),
                            Some(*top),
                            index,
                            &alternative.body,
                            &mut alternative_stock,
                        );
                    }
                    Source::Checked { top, owners, companion }
                        if matches!(alternative.body, Guarded::Unconditional(_)) =>
                    {
                        self.materialize(index);
                        let place = Place {
                            companion: companion.clone(),
                            owners: owners.clone(),
                            top: Some(*top),
                        };
                        let mut placing = Placing {
                            alternative: index,
                            body: &alternative.body,
                            stock: &mut alternative_stock,
                            bindings: &mut bindings,
                        };
                        self.checked_pattern(pattern, place, &mut placing);
                    }
                    Source::OwnedFields => self.adopt_fields(pattern, &alternative.body),
                    Source::Checked { .. } | Source::Shared => {}
                }
            }
            if !bindings.is_empty() {
                self.plan.bindings.insert(std::ptr::from_ref(alternative), bindings);
            }
            let alternative_held = match &alternative.body {
                Guarded::Unconditional(body) => {
                    self.expression(body, tail, &mut alternative_stock, after)
                }
                Guarded::Guards(branches) => {
                    let mut all: Option<Held> = None;
                    for branch in branches {
                        for guard in &branch.guards {
                            let value = guard.value();
                            self.expression(value, false, &mut vec![], &mut vec![]);
                            alternative_stock.retain(|spare| {
                                !spare.owners.iter().any(|&owner| uses_local(value, owner))
                            });
                        }
                        let mut branch_stock = alternative_stock.clone();
                        let branch_held =
                            self.expression(&branch.body, tail, &mut branch_stock, after);
                        all = Some(match all {
                            Some(all) => all.join(branch_held),
                            None => branch_held,
                        });
                        remaining.retain(|spare| {
                            branch_stock.iter().any(|other| other.local == spare.local)
                        });
                    }
                    all.unwrap_or(Held::Owned)
                }
            };
            remaining
                .retain(|spare| alternative_stock.iter().any(|other| other.local == spare.local));
            held = Some(match held {
                Some(held) => held.join(alternative_held),
                None => alternative_held,
            });
        }
        *stock = remaining;
        held.unwrap_or(Held::Owned)
    }

    fn hoisted_local(&mut self, case: *const Expression, position: usize) -> LocalId {
        if let Some(&local) = self.hoisted_locals.get(&(case, position)) {
            return local;
        }
        let local = self.fresh();
        self.hoisted_locals.insert((case, position), local);
        local
    }

    fn checked_pattern(&mut self, pattern: &Pattern, mut place: Place, placing: &mut Placing<'_>) {
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Literal(_) => {}
            PatternKind::Variable(local) => {
                self.adopt_checked(local, place.owners, place.companion, placing.body);
            }
            PatternKind::Named { local, pattern: inner } => {
                let companion = place.companion.clone();
                self.adopt_checked(local, place.owners.clone(), companion, placing.body);
                place.owners.push(local.id);
                self.checked_pattern(inner, place, placing);
            }
            PatternKind::Array(_) | PatternKind::Record(_) | PatternKind::Closure { .. } => {
                let (alternative, body) = (placing.alternative, placing.body);
                self.pattern(pattern, None, None, alternative, body, placing.stock);
            }
            PatternKind::Constructor { data, constructor, arguments } => {
                let alternative = placing.alternative;
                let Some(cell) = self.cells.cell(pattern.monotype) else {
                    self.pattern(pattern, None, None, alternative, placing.body, placing.stock);
                    return;
                };
                let (local, origin) = match place.top {
                    Some(Top::Local(id)) => (id, Origin::Scrutinee { alternative }),
                    Some(Top::Hoisted(case, position)) => {
                        let local = self.hoisted_local(case, position);
                        (local, Origin::Hoisted { case, position, alternative })
                    }
                    None => {
                        let local = self.fresh();
                        self.plan.pattern_cells.insert(std::ptr::from_ref(pattern), local);
                        self.plan.materialized.insert(local);
                        let origin =
                            Origin::Field { pattern: std::ptr::from_ref(pattern), alternative };
                        (local, origin)
                    }
                };
                if !arguments.is_empty() {
                    let mut owners = place.owners.clone();
                    if let Origin::Hoisted { .. } = origin {
                        owners.push(local);
                    }
                    let usable = !owners.iter().any(|&owner| guarded_uses(placing.body, owner) > 0);
                    if usable {
                        let condition =
                            (!is_true(&place.companion)).then(|| place.companion.clone());
                        let data = data.clone();
                        placing.stock.push(Spare { local, data, origin, owners, condition });
                    }
                }
                for (position, argument) in arguments.iter().enumerate() {
                    if !self.cells.is_spine(&cell, argument.monotype)
                        || !self.cells.tracks(&cell, *constructor, position)
                    {
                        self.pattern(
                            argument,
                            None,
                            None,
                            alternative,
                            placing.body,
                            placing.stock,
                        );
                        continue;
                    }
                    let companion = self.fresh();
                    let edge =
                        Edge { data: data.clone(), constructor: *constructor, field: position };
                    let cell = Expression::new(ExpressionKind::Local(local), pattern.monotype);
                    let owned = Box::new(place.companion.clone());
                    let edge = ExpressionKind::UniqueEdge { owned, cell: Box::new(cell), edge };
                    let name = SmolStr::new(format!("{}Owned", pattern_name(argument)));
                    let binding = Binding {
                        local: Local { id: companion, name, monotype: self.boolean },
                        value: Expression::new(edge, self.boolean),
                    };
                    placing.bindings.push(binding);
                    self.plan.materialized.insert(companion);
                    let place = Place {
                        companion: Expression::new(ExpressionKind::Local(companion), self.boolean),
                        owners: place.owners.clone(),
                        top: None,
                    };
                    self.checked_pattern(argument, place, placing);
                }
            }
        }
    }

    fn adopt_checked(
        &mut self,
        local: &Local,
        ancestors: Vec<LocalId>,
        companion: Expression,
        body: &Guarded,
    ) {
        let Some(data) = self.cells.cell(local.monotype) else { return };
        if !self.cells.is_tracked(&data) {
            return;
        }
        let scope = Scope::Guarded(body);
        if self.is_linear(local.id, &ancestors, scope, &Forced::default()) {
            self.checked.insert(local.id, Dynamic { companion, ancestors });
        } else {
            self.companions_at_uses(local.id, &companion, &ancestors, scope);
        }
    }

    fn pattern(
        &mut self,
        pattern: &Pattern,
        owners: Option<Vec<LocalId>>,
        top: Option<Top>,
        alternative: usize,
        body: &Guarded,
        stock: &mut Vec<Spare>,
    ) {
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Literal(_) => {}
            PatternKind::Variable(local) => {
                if let Some(owners) = owners {
                    self.adopt(local, owners, body);
                }
            }
            PatternKind::Named { local, pattern: inner } => {
                let Some(mut owners) = owners else {
                    return self.pattern(inner, None, None, alternative, body, stock);
                };
                self.adopt(local, owners.clone(), body);
                owners.push(local.id);
                self.pattern(inner, Some(owners), top, alternative, body, stock);
            }
            PatternKind::Array(elements) => {
                for element in elements {
                    self.pattern(element, None, None, alternative, body, stock);
                }
            }
            PatternKind::Record(fields) => {
                for (_, field) in fields {
                    self.pattern(field, None, None, alternative, body, stock);
                }
            }
            PatternKind::Closure { captures, .. } => {
                for capture in captures {
                    self.pattern(capture, None, None, alternative, body, stock);
                }
            }
            PatternKind::Constructor { data, arguments, .. } => {
                let cell = self.cells.cell(pattern.monotype);
                if let Some(owners) = &owners
                    && !arguments.is_empty()
                    && cell.is_some()
                {
                    let (local, origin) = match top {
                        Some(Top::Local(id)) => (id, Origin::Scrutinee { alternative }),
                        Some(Top::Hoisted(case, position)) => {
                            let local = match self.hoisted_locals.get(&(case, position)) {
                                Some(&local) => local,
                                None => {
                                    let local = self.fresh();
                                    self.hoisted_locals.insert((case, position), local);
                                    local
                                }
                            };
                            (local, Origin::Hoisted { case, position, alternative })
                        }
                        None => (
                            self.fresh(),
                            Origin::Field { pattern: std::ptr::from_ref(pattern), alternative },
                        ),
                    };
                    let mut owners = owners.clone();
                    if let Origin::Hoisted { .. } = origin {
                        owners.push(local);
                    }
                    let usable = !owners.iter().any(|&owner| guarded_uses(body, owner) > 0);
                    if usable {
                        let data = data.clone();
                        stock.push(Spare { local, data, origin, owners, condition: None });
                    }
                }
                for argument in arguments {
                    let spine = owners.is_some()
                        && cell
                            .as_ref()
                            .is_some_and(|cell| self.cells.is_spine(cell, argument.monotype));
                    let child = if spine { owners.clone() } else { None };
                    self.pattern(argument, child, None, alternative, body, stock);
                }
            }
        }
    }

    fn adopt_fields(&mut self, pattern: &Pattern, body: &Guarded) {
        let PatternKind::Constructor { arguments, .. } = &pattern.kind else { return };
        for argument in arguments {
            if let PatternKind::Variable(local) = &argument.kind {
                self.adopt(local, vec![], body);
            }
        }
    }

    fn adopt(&mut self, local: &Local, ancestors: Vec<LocalId>, body: &Guarded) {
        if self.cells.cell(local.monotype).is_some()
            && self.is_linear(local.id, &ancestors, Scope::Guarded(body), &Forced::default())
        {
            self.owned.insert(local.id, ancestors);
        }
    }

    fn is_linear(
        &mut self,
        target: LocalId,
        ancestors: &[LocalId],
        scope: Scope<'_>,
        forced: &Forced,
    ) -> bool {
        let family = self.conflicts(target, ancestors, scope);
        let counter = Counter { target, conflicts: &family, forced };
        let paths = match scope {
            Scope::Expression(expression) => counter.count(self, expression),
            Scope::Guarded(guarded) => counter.guarded(self, guarded),
        };
        paths.all_linear()
    }

    fn conflicts(
        &mut self,
        target: LocalId,
        ancestors: &[LocalId],
        scope: Scope<'_>,
    ) -> FxHashSet<LocalId> {
        let mut family = FxHashSet::default();
        family.insert(target);
        match scope {
            Scope::Expression(expression) => self.descendants(expression, &mut family),
            Scope::Guarded(guarded) => {
                for expression in guarded_expressions(guarded) {
                    self.descendants(expression, &mut family);
                }
            }
        }
        family.remove(&target);
        family.extend(ancestors.iter().copied());
        family
    }

    fn descendants(&mut self, expression: &Expression, family: &mut FxHashSet<LocalId>) {
        if let ExpressionKind::Case { scrutinees, alternatives } = &expression.kind {
            for (position, scrutinee) in scrutinees.iter().enumerate() {
                let ExpressionKind::Local(id) = scrutinee.kind else { continue };
                if !family.contains(&id) {
                    continue;
                }
                for alternative in alternatives {
                    self.spine_locals(&alternative.patterns[position], family);
                }
            }
        }
        for_each_child(expression, &mut |child| self.descendants(child, family));
    }

    fn spine_locals(&mut self, pattern: &Pattern, family: &mut FxHashSet<LocalId>) {
        match &pattern.kind {
            PatternKind::Variable(local) => {
                family.insert(local.id);
            }
            PatternKind::Named { local, pattern } => {
                family.insert(local.id);
                self.spine_locals(pattern, family);
            }
            PatternKind::Constructor { arguments, .. } => {
                let Some(cell) = self.cells.cell(pattern.monotype) else { return };
                for argument in arguments {
                    if self.cells.is_spine(&cell, argument.monotype) {
                        self.spine_locals(argument, family);
                    }
                }
            }
            PatternKind::Wildcard
            | PatternKind::Literal(_)
            | PatternKind::Array(_)
            | PatternKind::Record(_)
            | PatternKind::Closure { .. } => {}
        }
    }

    fn companions_at_uses(
        &mut self,
        target: LocalId,
        companion: &Expression,
        ancestors: &[LocalId],
        scope: Scope<'_>,
    ) {
        let roots = scope_expressions(scope);
        let mut search = Search {
            target,
            branches: vec![],
            in_scope: vec![],
            sites: vec![],
            conditionals: vec![],
            bound: FxHashSet::default(),
        };
        for root in &roots {
            search.expression(root);
        }
        if search.sites.len() > USE_LIMIT {
            return;
        }
        let mut family = self.conflicts(target, ancestors, scope);
        family.insert(target);
        for site in &search.sites {
            let mut forced = Forced::default();
            for &(conditional, branch) in &site.branches {
                forced.insert(conditional, vec![branch]);
            }
            if self.is_linear(target, ancestors, scope, &forced) {
                self.use_companions.insert(site.expression, companion.clone());
                continue;
            }
            let mut decisions = vec![];
            for &conditional in &search.conditionals {
                if decisions.len() == DECIDING_LIMIT {
                    break;
                }
                if let Some(clean) = self.clean_branches(conditional, &family, &search, site) {
                    forced.insert(std::ptr::from_ref(conditional), clean.clone());
                    decisions.push((conditional, clean));
                }
            }
            if decisions.is_empty() || !self.is_linear(target, ancestors, scope, &forced) {
                continue;
            }
            let mut owned = companion.clone();
            for (conditional, clean) in decisions {
                let decision = self.decision(conditional, &clean);
                owned = self.both(&owned, decision);
            }
            self.use_companions.insert(site.expression, owned);
        }
    }

    fn clean_branches(
        &mut self,
        conditional: &Expression,
        family: &FxHashSet<LocalId>,
        search: &Search<'_>,
        site: &Site,
    ) -> Option<Vec<Branch>> {
        let key = std::ptr::from_ref(conditional);
        if site.branches.iter().any(|(branch, _)| *branch == key)
            || contains_expression(conditional, site.expression)
        {
            return None;
        }
        let mut decidable = |expression: &Expression| {
            is_decidable(expression)
                && free_locals(expression).iter().all(|&(local, monotype)| {
                    (!search.bound.contains(&local) || site.in_scope.contains(&local))
                        && self.cells.cell(monotype).is_none()
                })
        };
        let touches =
            |expression: &Expression| family.iter().any(|&local| uses_local(expression, local));
        let branches: Vec<(Branch, bool)> = match &conditional.kind {
            ExpressionKind::If { condition, then, otherwise } if decidable(condition) => {
                vec![(Branch::Then, touches(then)), (Branch::Otherwise, touches(otherwise))]
            }
            ExpressionKind::Case { scrutinees, alternatives }
                if scrutinees.iter().all(decidable) =>
            {
                let mut branches = vec![];
                for (index, alternative) in alternatives.iter().enumerate() {
                    let Guarded::Unconditional(body) = &alternative.body else { return None };
                    branches.push((Branch::Alternative(index, None), touches(body)));
                }
                branches
            }
            _ => return None,
        };
        let clean: Vec<Branch> =
            branches.iter().filter(|(_, touched)| !touched).map(|(branch, _)| *branch).collect();
        let touched = clean.len() < branches.len();
        (touched && !clean.is_empty()).then_some(clean)
    }

    fn decision(&mut self, conditional: &Expression, clean: &[Branch]) -> Expression {
        match &conditional.kind {
            ExpressionKind::If { condition, .. } => match clean {
                [Branch::Then] => (**condition).clone(),
                [Branch::Otherwise] => self.negation((**condition).clone()),
                _ => self.truth(true),
            },
            ExpressionKind::Case { scrutinees, alternatives } => {
                let alternatives = alternatives
                    .iter()
                    .enumerate()
                    .map(|(index, alternative)| Alternative {
                        patterns: alternative.patterns.iter().map(shape).collect(),
                        body: Guarded::Unconditional(
                            self.truth(clean.contains(&Branch::Alternative(index, None))),
                        ),
                        position: alternative.position,
                    })
                    .collect();
                let case = ExpressionKind::Case { scrutinees: scrutinees.clone(), alternatives };
                Expression::new(case, self.boolean)
            }
            _ => self.truth(false),
        }
    }

    fn negation(&self, value: Expression) -> Expression {
        let foreign = Foreign::Operator(Operator::BooleanNot).interned();
        Expression::new(ExpressionKind::Foreign { foreign, arguments: vec![value] }, self.boolean)
    }

    fn both(&self, left: &Expression, right: Expression) -> Expression {
        if is_true(left) {
            return right;
        }
        let foreign = Foreign::Operator(Operator::BooleanAnd).interned();
        let arguments = vec![left.clone(), right];
        Expression::new(ExpressionKind::Foreign { foreign, arguments }, self.boolean)
    }
}

struct Site {
    expression: *const Expression,
    branches: Vec<(*const Expression, Branch)>,
    in_scope: FxHashSet<LocalId>,
}

struct Search<'e> {
    target: LocalId,
    branches: Vec<(*const Expression, Branch)>,
    in_scope: Vec<LocalId>,
    sites: Vec<Site>,
    conditionals: Vec<&'e Expression>,
    bound: FxHashSet<LocalId>,
}

impl<'e> Search<'e> {
    fn expression(&mut self, expression: &'e Expression) {
        let key = std::ptr::from_ref(expression);
        match &expression.kind {
            ExpressionKind::Local(id) if *id == self.target => {
                let site = Site {
                    expression: key,
                    branches: self.branches.clone(),
                    in_scope: self.in_scope.iter().copied().collect(),
                };
                self.sites.push(site);
            }
            ExpressionKind::Lambda { .. }
            | ExpressionKind::Closure { .. }
            | ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. } => {
                visit(expression, &mut |inner| bind_all(inner, &mut self.bound));
            }
            ExpressionKind::Let { bindings, body } => {
                let mark = self.in_scope.len();
                for binding in bindings {
                    self.expression(&binding.value);
                    self.bound.insert(binding.local.id);
                    self.in_scope.push(binding.local.id);
                }
                self.expression(body);
                self.in_scope.truncate(mark);
            }
            ExpressionKind::If { condition, then, otherwise } => {
                self.conditionals.push(expression);
                self.expression(condition);
                self.branch(key, Branch::Then, then);
                self.branch(key, Branch::Otherwise, otherwise);
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                self.conditionals.push(expression);
                for scrutinee in scrutinees {
                    self.expression(scrutinee);
                }
                for (index, alternative) in alternatives.iter().enumerate() {
                    let mark = self.in_scope.len();
                    alternative.for_each_local(&mut |local| {
                        self.bound.insert(local.id);
                        self.in_scope.push(local.id);
                    });
                    match &alternative.body {
                        Guarded::Unconditional(body) => {
                            self.branch(key, Branch::Alternative(index, None), body);
                        }
                        Guarded::Guards(branches) => {
                            for (position, branch) in branches.iter().enumerate() {
                                for guard in &branch.guards {
                                    let value = guard.value();
                                    self.branch(key, Branch::Alternative(index, None), value);
                                }
                                let taken = Branch::Alternative(index, Some(position));
                                self.branch(key, taken, &branch.body);
                            }
                        }
                    }
                    self.in_scope.truncate(mark);
                }
            }
            _ => for_each_child(expression, &mut |child| self.expression(child)),
        }
    }

    fn branch(&mut self, key: *const Expression, branch: Branch, expression: &'e Expression) {
        self.branches.push((key, branch));
        self.expression(expression);
        self.branches.pop();
    }
}

fn reads_cell_fields_once(
    cells: &mut impl Cells,
    expression: &Expression,
    record: LocalId,
    read: &mut Vec<SmolStr>,
) -> bool {
    match &expression.kind {
        ExpressionKind::Local(id) => *id != record,
        ExpressionKind::Access { record: accessed, label } if matches!(accessed.kind, ExpressionKind::Local(id) if id == record) =>
        {
            if cells.cell(expression.monotype).is_none() {
                return true;
            }
            if read.contains(label) {
                return false;
            }
            read.push(label.clone());
            true
        }
        ExpressionKind::Lambda { .. }
        | ExpressionKind::Closure { .. }
        | ExpressionKind::EffectPure(_)
        | ExpressionKind::EffectBind { .. }
        | ExpressionKind::EffectEach { .. } => !uses_local(expression, record),
        _ => {
            let mut once = true;
            for_each_child(expression, &mut |child| {
                once = once && reads_cell_fields_once(cells, child, record, read);
            });
            once
        }
    }
}

fn bind_all(expression: &Expression, bound: &mut FxHashSet<LocalId>) {
    match &expression.kind {
        ExpressionKind::Lambda { parameters, .. } => {
            bound.extend(parameters.iter().map(|parameter| parameter.id));
        }
        ExpressionKind::Let { bindings, .. } => {
            bound.extend(bindings.iter().map(|binding| binding.local.id));
        }
        ExpressionKind::EffectBind { local, .. }
        | ExpressionKind::EffectEach { element: local, .. } => {
            bound.insert(local.id);
        }
        ExpressionKind::Case { alternatives, .. } => {
            for alternative in alternatives {
                alternative.for_each_local(&mut |local| {
                    bound.insert(local.id);
                });
            }
        }
        _ => {}
    }
}

fn scope_expressions(scope: Scope<'_>) -> Vec<&Expression> {
    match scope {
        Scope::Expression(expression) => vec![expression],
        Scope::Guarded(guarded) => guarded_expressions(guarded),
    }
}

fn contains_expression(expression: &Expression, target: *const Expression) -> bool {
    let mut found = false;
    visit(expression, &mut |inner| found |= std::ptr::eq(inner, target));
    found
}

fn is_decidable(expression: &Expression) -> bool {
    let mut simple = true;
    visit(expression, &mut |inner| {
        simple &= match &inner.kind {
            ExpressionKind::Literal(_)
            | ExpressionKind::Unit
            | ExpressionKind::Local(_)
            | ExpressionKind::Access { .. } => true,
            ExpressionKind::Foreign { foreign, .. } => matches!(
                foreign,
                Foreign::Operator(_)
                    | Foreign::Int64 { .. }
                    | Foreign::Call { function: GoFunction { package: GoPackage::Prim, .. }, .. }
            ),
            _ => false,
        }
    });
    simple
        && is_deferrable(expression)
        && !can_fail(expression)
        && is_within_size(expression, DECIDING_SIZE)
}

fn free_locals(expression: &Expression) -> Vec<(LocalId, MonotypeId)> {
    let mut locals = vec![];
    visit(expression, &mut |inner| {
        if let ExpressionKind::Local(id) = inner.kind {
            locals.push((id, inner.monotype));
        }
    });
    locals
}

fn shape(pattern: &Pattern) -> Pattern {
    let kind = match &pattern.kind {
        PatternKind::Wildcard | PatternKind::Variable(_) => PatternKind::Wildcard,
        PatternKind::Named { pattern, .. } => return shape(pattern),
        PatternKind::Literal(literal) => PatternKind::Literal(literal.clone()),
        PatternKind::Array(elements) => PatternKind::Array(elements.iter().map(shape).collect()),
        PatternKind::Record(fields) => PatternKind::Record(
            fields.iter().map(|(label, field)| (label.clone(), shape(field))).collect(),
        ),
        PatternKind::Constructor { data, constructor, arguments } => PatternKind::Constructor {
            data: data.clone(),
            constructor: *constructor,
            arguments: arguments.iter().map(shape).collect(),
        },
        PatternKind::Closure { tag, captures } => {
            PatternKind::Closure { tag: *tag, captures: captures.iter().map(shape).collect() }
        }
    };
    Pattern { kind, monotype: pattern.monotype }
}

fn pattern_name(pattern: &Pattern) -> SmolStr {
    match &pattern.kind {
        PatternKind::Variable(local) | PatternKind::Named { local, .. } => local.name.clone(),
        _ => SmolStr::new_static("cell"),
    }
}

fn is_true(expression: &Expression) -> bool {
    matches!(expression.kind, ExpressionKind::Literal(Literal::Boolean(true)))
}

#[derive(Clone, Copy)]
enum Scope<'e> {
    Expression(&'e Expression),
    Guarded(&'e Guarded),
}

#[derive(Clone)]
enum Source {
    Owned { top: Top, owners: Vec<LocalId> },
    Checked { top: Top, owners: Vec<LocalId>, companion: Expression },
    OwnedFields,
    Shared,
}

#[derive(Clone, Copy)]
enum Top {
    Local(LocalId),
    Hoisted(*const Expression, usize),
}

struct Place {
    companion: Expression,
    owners: Vec<LocalId>,
    top: Option<Top>,
}

struct Placing<'p> {
    alternative: usize,
    body: &'p Guarded,
    stock: &'p mut Vec<Spare>,
    bindings: &'p mut Vec<Binding>,
}

struct Counter<'f> {
    target: LocalId,
    conflicts: &'f FxHashSet<LocalId>,
    forced: &'f Forced,
}

impl Counter<'_> {
    fn count<C: Cells>(&self, planner: &mut Planner<'_, C>, expression: &Expression) -> Paths {
        match &expression.kind {
            ExpressionKind::Local(id) if *id == self.target => Paths::event(Event::Consume),
            ExpressionKind::Local(id) if self.conflicts.contains(id) => {
                Paths::event(Event::Conflict)
            }
            ExpressionKind::Lambda { .. }
            | ExpressionKind::Closure { .. }
            | ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. } => {
                if uses_local(expression, self.target) {
                    Paths::event(Event::Shared)
                } else if self.conflicts.iter().any(|&conflict| uses_local(expression, conflict)) {
                    Paths::event(Event::Conflict)
                } else {
                    Paths::empty()
                }
            }
            ExpressionKind::Let { bindings, body } => {
                let mut paths = Paths::empty();
                for binding in bindings {
                    paths = paths.then(self.count(planner, &binding.value));
                }
                paths.then(self.count(planner, body))
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let allowed = self.forced.get(&std::ptr::from_ref(expression));
                let taken =
                    |branch: Branch| allowed.is_none_or(|allowed| allowed.contains(&branch));
                let mut branches = Paths::nothing();
                if taken(Branch::Then) {
                    branches = branches.or(self.count(planner, then));
                }
                if taken(Branch::Otherwise) {
                    branches = branches.or(self.count(planner, otherwise));
                }
                self.count(planner, condition).then(branches)
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                let mut paths = Paths::empty();
                for (position, scrutinee) in scrutinees.iter().enumerate() {
                    let inspected = alternatives.iter().any(|alternative| {
                        !matches!(alternative.patterns[position].kind, PatternKind::Wildcard)
                    });
                    let scrutinised = match scrutinee.kind {
                        ExpressionKind::Local(id) if id == self.target => {
                            if inspected {
                                Paths::event(Event::Peek)
                            } else {
                                Paths::empty()
                            }
                        }
                        _ => self.count(planner, scrutinee),
                    };
                    paths = paths.then(scrutinised);
                }
                let allowed = self.forced.get(&std::ptr::from_ref(expression));
                let taken = |index: usize, branch: Option<usize>| {
                    allowed.is_none_or(|allowed| {
                        allowed.iter().any(|allowed| match *allowed {
                            Branch::Alternative(alternative, allowed_branch) => {
                                alternative == index
                                    && (allowed_branch.is_none()
                                        || branch.is_none()
                                        || allowed_branch == branch)
                            }
                            Branch::Then | Branch::Otherwise => false,
                        })
                    })
                };
                let mut guards = Paths::empty();
                let mut bodies = Paths::nothing();
                for (index, alternative) in alternatives.iter().enumerate() {
                    match &alternative.body {
                        Guarded::Unconditional(body) => {
                            if taken(index, None) {
                                bodies = bodies.or(self.count(planner, body));
                            }
                        }
                        Guarded::Guards(branches) => {
                            for (position, branch) in branches.iter().enumerate() {
                                for guard in &branch.guards {
                                    let value = guard.value();
                                    guards = guards.then(self.count(planner, value));
                                }
                                if taken(index, Some(position)) {
                                    bodies = bodies.or(self.count(planner, &branch.body));
                                }
                            }
                        }
                    }
                }
                let bodies = if alternatives.is_empty() { Paths::empty() } else { bodies };
                paths.then(guards).then(bodies)
            }
            ExpressionKind::Apply { function, arguments } => {
                let paths = self.count(planner, function);
                self.call(planner, expression, arguments, paths)
            }
            ExpressionKind::Foreign { arguments, .. } => {
                self.call(planner, expression, arguments, Paths::empty())
            }
            _ => {
                let mut children = vec![];
                for_each_child(expression, &mut |child| children.push(child));
                let mut paths = Paths::empty();
                for child in children {
                    paths = paths.unordered(self.count(planner, child));
                }
                paths
            }
        }
    }

    fn call<C: Cells>(
        &self,
        planner: &mut Planner<'_, C>,
        call: &Expression,
        arguments: &[Expression],
        mut paths: Paths,
    ) -> Paths {
        for argument in arguments {
            let inspected = matches!(argument.kind, ExpressionKind::Local(id) if id == self.target)
                && inspects(&planner.facts.inspecting, planner.cells, call, argument);
            let argument_paths =
                if inspected { Paths::event(Event::Peek) } else { self.count(planner, argument) };
            paths = paths.unordered(argument_paths);
        }
        paths
    }

    fn guarded<C: Cells>(&self, planner: &mut Planner<'_, C>, guarded: &Guarded) -> Paths {
        match guarded {
            Guarded::Unconditional(body) => self.count(planner, body),
            Guarded::Guards(branches) => {
                let mut guards = Paths::empty();
                let mut bodies = Paths::nothing();
                for branch in branches {
                    for guard in &branch.guards {
                        let value = guard.value();
                        guards = guards.then(self.count(planner, value));
                    }
                    bodies = bodies.or(self.count(planner, &branch.body));
                }
                guards.then(bodies)
            }
        }
    }
}

#[derive(Clone, Copy)]
enum Event {
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
struct Paths(u32);

impl Paths {
    fn nothing() -> Paths {
        Paths(0)
    }

    fn empty() -> Paths {
        Paths(1 << Path::START.index())
    }

    fn event(event: Event) -> Paths {
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

    fn then(self, next: Paths) -> Paths {
        let mut combined = 0;
        for first in self.paths() {
            for second in next.paths() {
                combined |= 1 << first.then(second).index();
            }
        }
        Paths(combined)
    }

    fn unordered(self, other: Paths) -> Paths {
        Paths(self.then(other).0 | other.then(self).0)
    }

    fn or(self, other: Paths) -> Paths {
        Paths(self.0 | other.0)
    }

    fn all_linear(self) -> bool {
        self.paths().all(Path::is_linear)
    }
}

fn alternative_expressions(alternative: &Alternative) -> Vec<&Expression> {
    guarded_expressions(&alternative.body)
}

fn guarded_expressions(guarded: &Guarded) -> Vec<&Expression> {
    let mut expressions = vec![];
    for_each_guarded_child(guarded, &mut |expression| expressions.push(expression));
    expressions
}

fn guarded_uses(guarded: &Guarded, local: LocalId) -> usize {
    guarded_expressions(guarded)
        .into_iter()
        .filter(|expression| uses_local(expression, local))
        .count()
}

struct Emission<'p> {
    program: &'p Program,
    facts: Facts,
    identifiers: FxHashMap<Variant, FunctionId>,
}

impl<'p> Emission<'p> {
    fn new(program: &'p Program, facts: Facts) -> Emission<'p> {
        Emission { program, facts, identifiers: FxHashMap::default() }
    }

    fn finish(mut self, cells: &mut impl Cells) -> Reused {
        let count = self.program.functions.len();
        let mut pending = vec![];
        for index in 0..count {
            let id = FunctionId(index as u32);
            self.identifiers.insert(Variant::plain(id), id);
            pending.push(Variant::plain(id));
        }
        let demanded = self.facts.demanded.len();
        let mut functions: Vec<Option<Function>> = (0..count).map(|_| None).collect();
        let mut materialized = FxHashSet::default();
        let boolean = cells.boolean();
        while let Some(variant) = pending.pop() {
            let mut function = Box::new(self.program.function(variant.function).clone());
            let plan = Planner::new(self.program, cells, &mut self.facts, variant).plan(&function);
            let callbacks = plan.callbacks.values();
            let targets = plan.calls.values().map(|(target, _, _)| target).chain(callbacks);
            let mut targets: Vec<Variant> = targets.copied().collect();
            targets.sort_unstable_by_key(|target| {
                (target.function, target.owned, target.checked, target.donor)
            });
            for target in targets {
                if !self.identifiers.contains_key(&target) {
                    let next = FunctionId(self.identifiers.len() as u32);
                    self.identifiers.insert(target, next);
                    pending.push(target);
                }
            }
            let mut next_local = plan.next_local;
            self.rewrite(&mut function.body, &plan, cells, &mut next_local);
            mark_kept_fields(&mut function.body);
            if variant.is_reusing() {
                function.name = SmolStr::new(format!("{}{REUSING}", function.name));
            }
            if variant.checked != 0 {
                function.name = SmolStr::new(format!("{}{CHECKED}", function.name));
            }
            for &(position, companion) in &plan.companions {
                let name = SmolStr::new(format!("{}Owned", function.parameters[position].name));
                let local = Local { id: companion, name, monotype: boolean };
                function.parameters.push(local);
            }
            if let Some(donor) = plan.donor {
                let monotype = function.result;
                function.parameters.push(Local { id: donor, name: "donor".into(), monotype });
            }
            let id = self.identifiers[&variant];
            materialized.extend(plan.materialized.iter().map(|&local| (id, local)));
            if functions.len() <= id.0 as usize {
                functions.resize_with(id.0 as usize + 1, || None);
            }
            functions[id.0 as usize] = Some(*function);
        }
        assert_eq!(
            demanded,
            self.facts.demanded.len(),
            "invariant violated: emission planned a variant that ownership never settled"
        );
        let mut functions: Vec<Function> = functions
            .into_iter()
            .map(|function| {
                function.expect("invariant violated: a planned variant was not emitted")
            })
            .collect();
        let mut candidates = FxHashSet::default();
        for function in &functions {
            visit(&function.body, &mut |expression| {
                if let ExpressionKind::UniqueEdge { edge, .. } = &expression.kind {
                    candidates.insert(edge.data.clone());
                }
            });
        }
        for function in &mut functions {
            untrack(&mut function.body, &candidates);
        }
        let duplicates = self.duplicates(&mut functions);
        for function in &mut functions {
            redirect(&mut function.body, &duplicates);
        }
        let (program, renumbering) = prune_unreachable(functions, self.program.entry);
        let materialized = materialized
            .into_iter()
            .filter_map(|(function, local)| Some((*renumbering.get(&function)?, local)))
            .collect();
        Reused { program, materialized, candidates }
    }

    /// The variants that equal an earlier variant of the same function once
    /// each stops calling itself. Each variant calls itself as an unnamed function while
    /// they are compared.
    fn duplicates(&self, functions: &mut [Function]) -> FxHashMap<FunctionId, FunctionId> {
        let unnamed = FunctionId(u32::MAX);
        let mut variants: Vec<(Variant, FunctionId)> = self
            .identifiers
            .iter()
            .filter(|(variant, _)| !variant.is_plain())
            .map(|(variant, id)| (*variant, *id))
            .collect();
        variants.sort_by_key(|(_, id)| *id);
        for &(_, id) in &variants {
            let itself = FxHashMap::from_iter([(id, unnamed)]);
            redirect(&mut functions[id.0 as usize].body, &itself);
        }
        let mut representatives: FxHashMap<FunctionId, Vec<FunctionId>> = FxHashMap::default();
        let mut duplicates = FxHashMap::default();
        for &(variant, id) in &variants {
            let same = |other: &FunctionId| {
                let (this, other) = (&functions[id.0 as usize], &functions[other.0 as usize]);
                this.parameters == other.parameters && this.body == other.body
            };
            let candidates = representatives.entry(variant.function).or_default();
            match candidates.iter().find(|other| same(other)) {
                Some(&representative) => {
                    duplicates.insert(id, representative);
                }
                None => candidates.push(id),
            }
        }
        for &(_, id) in &variants {
            let itself = FxHashMap::from_iter([(unnamed, id)]);
            redirect(&mut functions[id.0 as usize].body, &itself);
        }
        duplicates
    }

    fn rewrite(
        &self,
        expression: &mut Expression,
        plan: &Plan,
        cells: &mut impl Cells,
        next_local: &mut u32,
    ) {
        let key = std::ptr::from_ref(&*expression);
        if let ExpressionKind::Case { alternatives, .. } = &mut expression.kind {
            for alternative in alternatives.iter_mut() {
                for pattern in &mut alternative.patterns {
                    rewrite_pattern(pattern, plan);
                }
            }
        }
        for_each_child_mut(expression, &mut |child| self.rewrite(child, plan, cells, next_local));
        if let ExpressionKind::Case { alternatives, .. } = &mut expression.kind {
            for alternative in alternatives.iter_mut() {
                let Some(bindings) = plan.bindings.get(&std::ptr::from_ref(&*alternative)) else {
                    continue;
                };
                match &mut alternative.body {
                    Guarded::Unconditional(body) => bind_companions(body, bindings),
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            bind_companions(&mut branch.body, bindings);
                        }
                    }
                }
            }
        }
        let edges = plan.edges.get(&key);
        if let Some(token) = plan.constructs.get(&key) {
            let monotype = expression.monotype;
            let position = expression.position;
            let kind = std::mem::replace(&mut expression.kind, ExpressionKind::Unit);
            let ExpressionKind::Construct { data, constructor, arguments } = kind else {
                unreachable!("invariant violated: a planned reuse is not a construction")
            };
            let cell = Box::new(Expression::new(ExpressionKind::Local(token.cell), monotype));
            *expression = match &token.condition {
                None => {
                    let kept = Kept::default();
                    let reuse = ExpressionKind::Reuse { cell, data, constructor, arguments, kept };
                    tracked(Expression::new(reuse, monotype), edges, true)
                }
                Some(condition) => {
                    let mut bindings = vec![];
                    let mut values = vec![];
                    for argument in arguments {
                        if is_trivial(&argument) {
                            values.push(argument);
                            continue;
                        }
                        let local = Local::fresh(next_local, "field".into(), argument.monotype);
                        values.push(local.expression());
                        bindings.push(Binding { local, value: argument });
                    }
                    let reuse = ExpressionKind::Reuse {
                        cell,
                        data: data.clone(),
                        constructor,
                        arguments: values.clone(),
                        kept: Kept::default(),
                    };
                    let construct =
                        ExpressionKind::Construct { data, constructor, arguments: values };
                    let choice = ExpressionKind::If {
                        condition: Box::new(condition.clone()),
                        then: Box::new(tracked(Expression::new(reuse, monotype), edges, true)),
                        otherwise: Box::new(tracked(
                            Expression::new(construct, monotype),
                            edges,
                            false,
                        )),
                    };
                    let choice = Expression::new(choice, monotype);
                    match bindings.is_empty() {
                        true => choice,
                        false => {
                            let body = Box::new(choice);
                            Expression::new(ExpressionKind::Let { bindings, body }, monotype)
                        }
                    }
                }
            };
            expression.position = position;
        } else if matches!(expression.kind, ExpressionKind::Construct { .. }) {
            let construct = std::mem::replace(
                expression,
                Expression::new(ExpressionKind::Unit, expression.monotype),
            );
            *expression = tracked(construct, edges, false);
        }
        if let Some(target) = plan.callbacks.get(&key) {
            expression.kind = ExpressionKind::Function(self.identifiers[target]);
        }
        if let Some((target, donor, companions)) = plan.calls.get(&key) {
            let id = self.identifiers[target];
            let ExpressionKind::Apply { function, arguments } = &mut expression.kind else {
                unreachable!("invariant violated: a planned variant call is not an application")
            };
            let callee = self.program.function(target.function);
            let mut parameters: Vec<MonotypeId> =
                callee.parameters.iter().map(|parameter| parameter.monotype).collect();
            for companion in companions {
                parameters.push(companion.monotype);
                arguments.push(companion.clone());
            }
            if let &Some(donor) = donor {
                parameters.push(callee.result);
                arguments.push(Expression::new(ExpressionKind::Local(donor), callee.result));
            }
            let monotype = cells.function_type(&parameters, callee.result);
            **function = Expression::new(ExpressionKind::Function(id), monotype);
        }
        if let ExpressionKind::Case { scrutinees, .. } = &mut expression.kind {
            let mut bindings = vec![];
            for (position, scrutinee) in scrutinees.iter_mut().enumerate() {
                if let Some(&local) = plan.hoisted.get(&(key, position)) {
                    let monotype = scrutinee.monotype;
                    let reference = Expression::new(ExpressionKind::Local(local), monotype);
                    let value = std::mem::replace(scrutinee, reference);
                    let local = Local { id: local, name: "scrutinee".into(), monotype };
                    bindings.push(Binding { local, value });
                }
            }
            if !bindings.is_empty() {
                let monotype = expression.monotype;
                let case =
                    std::mem::replace(expression, Expression::new(ExpressionKind::Unit, monotype));
                let body = Box::new(case);
                *expression = Expression::new(ExpressionKind::Let { bindings, body }, monotype);
            }
        }
    }
}

fn tracked(
    value: Expression,
    edges: Option<&Vec<(usize, Expression)>>,
    reused: bool,
) -> Expression {
    let Some(edges) = edges else { return value };
    if edges.is_empty() && !reused {
        return value;
    }
    let monotype = value.monotype;
    let position = value.position;
    let edges = edges.clone();
    let mut marked =
        Expression::new(ExpressionKind::UniqueEdges { value: Box::new(value), edges }, monotype);
    marked.position = position;
    marked
}

fn untrack(expression: &mut Expression, candidates: &FxHashSet<DataType>) {
    for_each_child_mut(expression, &mut |child| untrack(child, candidates));
    let ExpressionKind::UniqueEdges { value, .. } = &mut expression.kind else { return };
    let data = match &value.kind {
        ExpressionKind::Construct { data, .. } | ExpressionKind::Reuse { data, .. } => data,
        _ => return,
    };
    if !candidates.contains(data) {
        let monotype = value.monotype;
        let value =
            std::mem::replace(&mut **value, Expression::new(ExpressionKind::Unit, monotype));
        let position = expression.position;
        *expression = value;
        expression.position = position;
    }
}

fn bind_companions(body: &mut Expression, bindings: &[Binding]) {
    let mut kept: Vec<Binding> = vec![];
    for binding in bindings.iter().rev() {
        let used = uses_local(body, binding.local.id)
            || kept.iter().any(|later| uses_local(&later.value, binding.local.id));
        if used {
            kept.push(binding.clone());
        }
    }
    let monotype = body.monotype;
    for binding in kept {
        let inner = std::mem::replace(body, Expression::new(ExpressionKind::Unit, monotype));
        let bindings = vec![binding];
        *body = Expression::new(ExpressionKind::Let { bindings, body: Box::new(inner) }, monotype);
    }
}

fn rewrite_pattern(pattern: &mut Pattern, plan: &Plan) {
    let key = std::ptr::from_ref(&*pattern);
    match &mut pattern.kind {
        PatternKind::Named { pattern, .. } => rewrite_pattern(pattern, plan),
        PatternKind::Array(elements) => {
            elements.iter_mut().for_each(|element| rewrite_pattern(element, plan))
        }
        PatternKind::Record(fields) => {
            fields.iter_mut().for_each(|(_, field)| rewrite_pattern(field, plan))
        }
        PatternKind::Constructor { arguments, .. }
        | PatternKind::Closure { captures: arguments, .. } => {
            arguments.iter_mut().for_each(|argument| rewrite_pattern(argument, plan))
        }
        PatternKind::Wildcard | PatternKind::Variable(_) | PatternKind::Literal(_) => {}
    }
    if let Some(&local) = plan.pattern_cells.get(&key) {
        let monotype = pattern.monotype;
        let inner = std::mem::replace(pattern, Pattern { kind: PatternKind::Wildcard, monotype });
        let local = Local { id: local, name: "cell".into(), monotype };
        pattern.kind = PatternKind::Named { local, pattern: Box::new(inner) };
    }
}

fn redirect(expression: &mut Expression, targets: &FxHashMap<FunctionId, FunctionId>) {
    if let ExpressionKind::Function(id) = &mut expression.kind {
        if let Some(&target) = targets.get(id) {
            *id = target;
        }
        return;
    }
    for_each_child_mut(expression, &mut |child| redirect(child, targets));
}

fn has_escape_hatches(function: &Function, cells: &mut impl Cells) -> bool {
    let mut monotypes = vec![function.result];
    monotypes.extend(function.parameters.iter().map(|parameter| parameter.monotype));
    visit(&function.body, &mut |expression| monotypes.push(expression.monotype));
    monotypes.sort_unstable();
    monotypes.dedup();
    monotypes.into_iter().any(|monotype| cells.erases(monotype) || cells.is_suspended(monotype))
}

impl<Q> Cells for Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    fn cell(&mut self, monotype: MonotypeId) -> Option<DataType> {
        let Monotype::Data(data) = self.monotypes.get(monotype).clone() else { return None };
        if let Some(&cell) = self.cell_types.get(&data) {
            return cell.then_some(data);
        }
        let cell = self.is_cell(&data);
        self.cell_types.insert(data.clone(), cell);
        cell.then_some(data)
    }

    fn is_spine(&mut self, cell: &DataType, field: MonotypeId) -> bool {
        let Some(child) = Cells::cell(self, field) else { return false };
        let key = (child.clone(), cell.clone());
        if let Some(&reaches) = self.reaching.get(&key) {
            return reaches;
        }
        let reaches = self.reaches(&child, cell).unwrap_or(false);
        self.reaching.insert(key, reaches);
        reaches
    }

    fn is_effect(&self, monotype: MonotypeId) -> bool {
        self.monotypes.effect_result(monotype).is_some()
    }

    fn is_suspended(&self, monotype: MonotypeId) -> bool {
        matches!(self.monotypes.get(monotype), Monotype::Lazy(_) | Monotype::Effect(_))
    }

    fn erases(&mut self, monotype: MonotypeId) -> bool {
        if let Some(&erases) = self.erasing.get(&monotype) {
            return erases;
        }
        self.erasing.insert(monotype, false);
        let erases = match self.monotypes.get(monotype).clone() {
            Monotype::Erased(_) | Monotype::Recursive(_) => true,
            Monotype::Data(data) => self.erases_arguments(&data).unwrap_or(true),
            Monotype::Function(argument, result) => {
                Cells::erases(self, argument) || Cells::erases(self, result)
            }
            Monotype::Record(fields) => {
                fields.iter().any(|field| Cells::erases(self, field.monotype))
            }
            container => container.element().is_some_and(|element| Cells::erases(self, element)),
        };
        self.erasing.insert(monotype, erases);
        erases
    }

    fn holds(&mut self, monotype: MonotypeId, cell: &DataType) -> bool {
        let key = (monotype, cell.clone());
        if let Some(&holds) = self.holding.get(&key) {
            return holds;
        }
        let mut pending = vec![monotype];
        let mut visited = FxHashSet::default();
        let mut holds = false;
        while let Some(monotype) = pending.pop() {
            if !visited.insert(monotype) {
                continue;
            }
            match self.monotypes.get(monotype).clone() {
                Monotype::Int
                | Monotype::Number
                | Monotype::Boolean
                | Monotype::Char
                | Monotype::String
                | Monotype::Unit
                | Monotype::BigInt
                | Monotype::Int64
                | Monotype::UInt64
                | Monotype::Regex => {}
                Monotype::Array(element)
                | Monotype::MutableArray(element)
                | Monotype::Nullable(element)
                | Monotype::ConsList(element)
                | Monotype::Object(element) => pending.push(element),
                Monotype::Record(fields) => {
                    pending.extend(fields.iter().map(|field| field.monotype));
                }
                Monotype::Data(data) | Monotype::Recursive(data) if data == *cell => {
                    holds = true;
                }
                Monotype::Data(data) | Monotype::Recursive(data) => {
                    match self.constructor_fields(&data) {
                        Ok(fields) => pending.extend(fields),
                        Err(_) => holds = true,
                    }
                }
                _ => holds = true,
            }
            if holds {
                break;
            }
        }
        self.holding.insert(key, holds);
        holds
    }

    fn function_type(&mut self, parameters: &[MonotypeId], result: MonotypeId) -> MonotypeId {
        parameters
            .iter()
            .rev()
            .fold(result, |result, &parameter| self.monotypes.function(parameter, result))
    }

    fn is_tracked(&mut self, cell: &DataType) -> bool {
        self.edge_bits(cell).ok().flatten().is_some()
    }

    fn tracks(&mut self, cell: &DataType, constructor: usize, field: usize) -> bool {
        let bits = self.edge_bits(cell).ok().flatten();
        bits.is_some_and(|bits| bits.bit(constructor, field).is_some())
    }

    fn boolean(&mut self) -> MonotypeId {
        self.monotypes.intern(Monotype::Boolean)
    }

    fn is_record(&self, monotype: MonotypeId) -> bool {
        matches!(self.monotypes.get(monotype), Monotype::Record(_))
            && !self.monotypes.is_instantiated_record(monotype)
    }
}
