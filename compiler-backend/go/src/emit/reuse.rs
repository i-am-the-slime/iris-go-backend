use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use super::uses_local;
use crate::foreign::{Boundary, Foreign, Iteration};
use crate::mono::{
    Alternative, Binding, Expression, ExpressionKind, Function, FunctionId, Guarded, Local,
    LocalId, Pattern, PatternKind, Program,
};
use crate::monotype::{DataType, MonotypeId};
use crate::simplify::{
    for_each_child, for_each_child_mut, for_each_guarded_child, prune_unreachable, visit,
};
use crate::timing::timed;

/// What the name of a variant that reuses its arguments' cells adds to its
/// function's name.
pub(super) const REUSING: &str = "Reusing";

pub(super) trait Cells {
    fn cell(&mut self, monotype: MonotypeId) -> Option<DataType>;
    fn is_spine(&mut self, cell: &DataType, field: MonotypeId) -> bool;
    fn is_effect(&self, monotype: MonotypeId) -> bool;
    fn retains(&mut self, monotype: MonotypeId) -> bool;
    fn erases(&mut self, monotype: MonotypeId) -> bool;
    fn is_suspended(&self, monotype: MonotypeId) -> bool;
    fn function_type(&mut self, parameters: &[MonotypeId], result: MonotypeId) -> MonotypeId;
}

pub(super) struct Reused {
    pub program: Program,
    pub materialized: FxHashSet<(FunctionId, LocalId)>,
}

pub(super) fn reuse_cells(program: &Program, cells: &mut impl Cells) -> Reused {
    let mut facts = Facts::new(program, cells);
    timed("settle ownership", || facts.settle(program, cells));
    timed("rewrite variants", || Emission::new(program, facts).finish(cells))
}

const MASK_LIMIT: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Variant {
    function: FunctionId,
    owned: u64,
    donor: bool,
}

impl Variant {
    fn plain(function: FunctionId) -> Variant {
        Variant { function, owned: 0, donor: false }
    }

    fn is_plain(self) -> bool {
        self.owned == 0 && !self.donor
    }
}

struct Facts {
    eligible: Vec<bool>,
    next_local: u32,
    unowned_results: FxHashSet<(FunctionId, u64)>,
    donor_used: FxHashSet<Variant>,
    writes: FxHashSet<Variant>,
    demanded: Vec<Variant>,
    seen: FxHashSet<Variant>,
    /// Whether a demanded variant's plan may change: it was never planned, or a
    /// fact it consulted has changed since it was last planned.
    stale: Vec<bool>,
    /// The demanded variants whose plans consulted the facts of a function at an
    /// ownership mask.
    consulted_by: FxHashMap<(FunctionId, u64), FxHashSet<usize>>,
}

impl Facts {
    fn new(program: &Program, cells: &mut impl Cells) -> Facts {
        let eligible = program
            .functions
            .iter()
            .map(|function| {
                !cells.is_effect(function.result)
                    && function.parameters.len() <= MASK_LIMIT
                    && !has_escape_hatches(function, cells)
            })
            .collect();
        let mut next_local = 0;
        for function in &program.functions {
            for parameter in &function.parameters {
                next_local = next_local.max(parameter.id.0 + 1);
            }
            visit(&function.body, &mut |expression| {
                next_local = next_local.max(highest_local(expression) + 1);
            });
        }
        let mut facts = Facts {
            eligible,
            next_local,
            unowned_results: FxHashSet::default(),
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
                let ownership = (variant.function, variant.owned);
                let mut grown = false;
                if !plan.result_owned && self.unowned_results.insert(ownership) {
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
}

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
    donor_used: bool,
    writes: bool,
    donor: Option<LocalId>,
    constructs: FxHashMap<*const Expression, LocalId>,
    calls: FxHashMap<*const Expression, (Variant, Option<LocalId>)>,
    callbacks: FxHashMap<*const Expression, Variant>,
    hoisted: FxHashMap<(*const Expression, usize), LocalId>,
    pattern_cells: FxHashMap<*const Pattern, LocalId>,
    materialized: FxHashSet<LocalId>,
}

struct Planner<'a, C> {
    program: &'a Program,
    cells: &'a mut C,
    facts: &'a mut Facts,
    variant: Variant,
    next_local: u32,
    owned: FxHashMap<LocalId, Vec<LocalId>>,
    alternatives: Vec<Vec<LocalId>>,
    plan: Plan,
    consulted: Vec<(FunctionId, u64)>,
}

impl<'a, C: Cells> Planner<'a, C> {
    fn new(
        program: &'a Program,
        cells: &'a mut C,
        facts: &'a mut Facts,
        variant: Variant,
    ) -> Planner<'a, C> {
        let next_local = facts.next_local;
        Planner {
            program,
            cells,
            facts,
            variant,
            next_local,
            owned: FxHashMap::default(),
            alternatives: vec![],
            plan: Plan::default(),
            consulted: vec![],
        }
    }

    fn fresh(&mut self) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        id
    }

    fn plan(self, function: &Function) -> Plan {
        self.plan_consulting(function).0
    }

    /// The plan, with the functions and ownership masks whose facts it consulted.
    fn plan_consulting(mut self, function: &Function) -> (Plan, Vec<(FunctionId, u64)>) {
        for (position, parameter) in function.parameters.iter().enumerate() {
            if self.variant.owned & (1 << position) != 0
                && self.cells.cell(parameter.monotype).is_some()
                && self.is_linear(parameter.id, &[], Scope::Expression(&function.body))
            {
                self.owned.insert(parameter.id, vec![]);
            }
        }
        let mut stock = vec![];
        if self.variant.donor
            && let Some(data) = self.cells.cell(function.result)
        {
            let local = self.fresh();
            self.plan.donor = Some(local);
            stock.push(Spare { local, data, origin: Origin::Donor, owners: vec![] });
        }
        self.plan.result_owned = self.expression(&function.body, true, &mut stock, &mut vec![]);
        (self.plan, self.consulted)
    }

    fn take(
        &mut self,
        data: &DataType,
        stock: &mut Vec<Spare>,
        after: &[&Expression],
    ) -> Option<LocalId> {
        let position = stock.iter().position(|spare| {
            spare.data == *data
                && !spare
                    .owners
                    .iter()
                    .any(|&owner| after.iter().any(|expression| uses_local(expression, owner)))
        })?;
        let spare = stock.remove(position);
        self.used(&spare);
        Some(spare.local)
    }

    fn used(&mut self, spare: &Spare) {
        let alternative = match spare.origin {
            Origin::Donor => {
                self.plan.donor_used = true;
                return;
            }
            Origin::Scrutinee { alternative } => alternative,
            Origin::Hoisted { case, position, alternative } => {
                self.plan.hoisted.insert((case, position), spare.local);
                alternative
            }
            Origin::Field { pattern, alternative } => {
                self.plan.pattern_cells.insert(pattern, spare.local);
                self.plan.materialized.insert(spare.local);
                alternative
            }
        };
        self.materialize(alternative);
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
    ) -> bool {
        match &expression.kind {
            ExpressionKind::Local(id) => {
                stock.retain(|spare| !spare.owners.contains(id));
                self.owned.contains_key(id)
            }
            ExpressionKind::Function(id) => self.is_owned_constant(*id),
            ExpressionKind::Fail(_) => true,
            ExpressionKind::Construct { data, arguments, .. } => {
                let cell = self.cells.cell(expression.monotype);
                let owned = self.arguments(arguments, stock, after);
                let mut spine_owned = true;
                for (argument, argument_owned) in arguments.iter().zip(owned) {
                    if let Some(cell) = &cell
                        && self.cells.is_spine(cell, argument.monotype)
                    {
                        spine_owned &= argument_owned;
                    }
                }
                if cell.is_none() {
                    return false;
                }
                if !arguments.is_empty()
                    && let Some(local) = self.take(data, stock, after)
                {
                    self.plan.constructs.insert(std::ptr::from_ref(expression), local);
                    self.plan.writes = true;
                }
                spine_owned
            }
            ExpressionKind::Apply { function, arguments } => {
                if let ExpressionKind::Function(id) = function.kind
                    && self.facts.eligible[id.0 as usize]
                    && self.program.function(id).parameters.len() == arguments.len()
                {
                    return self.call(expression, id, arguments, tail, stock, after);
                }
                self.unordered(expression, stock, after);
                false
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
            } if arguments.len() == 3 => self.fold(expression, *iteration, arguments, stock, after),
            ExpressionKind::Lambda { .. }
            | ExpressionKind::Closure { .. }
            | ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. } => {
                for_each_child(expression, &mut |child| {
                    self.expression(child, false, &mut vec![], &mut vec![]);
                });
                stock.retain(|spare| !spare.owners.iter().any(|&owner| uses_local(expression, owner)));
                false
            }
            ExpressionKind::Let { bindings, body } => {
                for (position, binding) in bindings.iter().enumerate() {
                    let mark = after.len();
                    after.extend(bindings[position + 1..].iter().map(|binding| &binding.value));
                    after.push(body);
                    let owned = self.expression(&binding.value, false, stock, after);
                    after.truncate(mark);
                    if owned
                        && self.cells.cell(binding.local.monotype).is_some()
                        && self.is_linear(binding.local.id, &[], Scope::Expression(expression))
                    {
                        self.owned.insert(binding.local.id, vec![]);
                    }
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
                let then_owned = self.expression(then, tail, &mut then_stock, after);
                let mut otherwise_stock = stock.clone();
                let otherwise_owned = self.expression(otherwise, tail, &mut otherwise_stock, after);
                stock.retain(|spare| {
                    then_stock.iter().any(|other| other.local == spare.local)
                        && otherwise_stock.iter().any(|other| other.local == spare.local)
                });
                then_owned && otherwise_owned
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                self.case(expression, scrutinees, alternatives, tail, stock, after)
            }
            _ => {
                self.unordered(expression, stock, after);
                false
            }
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
        let initial_owned = self.expression(initial, false, stock, after);
        after.truncate(mark);
        after.extend([callback, initial]);
        self.expression(array, false, stock, after);
        after.truncate(mark);
        stock.retain(|spare| !spare.owners.iter().any(|&owner| uses_local(callback, owner)));
        let accumulator = match iteration {
            Iteration::FoldLeft => 0,
            _ => 1,
        };
        if initial_owned
            && self.cells.cell(expression.monotype).is_some()
            && self.owned_callback(callback, accumulator)
        {
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
            let variant = Variant { function: id, owned: 1 << position, donor: false };
            self.facts.demand(variant);
            self.consulted.push((id, variant.owned));
            if self.facts.unowned_results.contains(&(id, variant.owned)) {
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
        if self.cells.cell(accumulator.monotype).is_none()
            || !self.is_linear(accumulator.id, &[], Scope::Expression(body))
        {
            return false;
        }
        let saved = self.plan.clone();
        self.owned.insert(accumulator.id, vec![]);
        if self.expression(body, false, &mut vec![], &mut vec![]) {
            return true;
        }
        self.owned.remove(&accumulator.id);
        self.plan = saved;
        false
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
    ) -> Vec<bool> {
        let arguments: Vec<&'e Expression> = arguments.iter().collect();
        self.arguments_of(&arguments, stock, after)
    }

    fn arguments_of<'e>(
        &mut self,
        arguments: &[&'e Expression],
        stock: &mut Vec<Spare>,
        after: &mut Vec<&'e Expression>,
    ) -> Vec<bool> {
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
    ) -> bool {
        let argument_owned = self.arguments(arguments, stock, after);
        let borrows = !self.cells.retains(expression.monotype);
        let parameters = &self.program.function(callee).parameters;
        let mut owned = 0u64;
        for (position, argument_owned) in argument_owned.into_iter().enumerate() {
            let borrowed = borrows && matches!(arguments[position].kind, ExpressionKind::Local(_));
            if argument_owned
                && !borrowed
                && self.cells.cell(parameters[position].monotype).is_some()
            {
                owned |= 1 << position;
            }
        }
        let variant = Variant { function: callee, owned, donor: false };
        self.facts.demand(variant);
        self.consulted.push((callee, owned));
        let result_owned = !self.facts.unowned_results.contains(&(callee, owned));
        let mut target = None;
        if tail
            && let Some(data) = self.cells.cell(expression.monotype)
            && stock.iter().any(|spare| spare.data == data)
        {
            let donating = Variant { donor: true, ..variant };
            self.facts.demand(donating);
            if self.facts.donor_used.contains(&donating)
                && self.permits(donating, tail)
                && let Some(donor) = self.take(&data, stock, after)
            {
                target = Some((donating, Some(donor)));
            }
        }
        if target.is_none()
            && !variant.is_plain()
            && self.facts.writes.contains(&variant)
            && self.permits(variant, tail)
        {
            target = Some((variant, None));
        }
        if let Some((target, _)) = target {
            if target.donor || self.facts.writes.contains(&target) {
                self.plan.writes = true;
            }
        }
        if let Some(target) = target {
            self.plan.calls.insert(std::ptr::from_ref(expression), target);
        }
        result_owned
    }

    fn permits(&self, target: Variant, tail: bool) -> bool {
        !(tail && target.function == self.variant.function && target != self.variant)
    }

    fn case<'e>(
        &mut self,
        expression: &'e Expression,
        scrutinees: &'e [Expression],
        alternatives: &'e [Alternative],
        tail: bool,
        stock: &mut Vec<Spare>,
        after: &mut Vec<&'e Expression>,
    ) -> bool {
        let mut sources = vec![];
        for (position, scrutinee) in scrutinees.iter().enumerate() {
            let source = match &scrutinee.kind {
                ExpressionKind::Local(id) => match self.owned.get(id) {
                    Some(ancestors) => {
                        let mut owners = ancestors.clone();
                        owners.push(*id);
                        Source::Owned { top: Top::Local(*id), owners }
                    }
                    None => Source::Shared,
                },
                _ => {
                    let mark = after.len();
                    after.extend(&scrutinees[position + 1..]);
                    after.extend(alternatives.iter().flat_map(alternative_expressions));
                    let owned = self.expression(scrutinee, false, stock, after)
                        && self.cells.cell(scrutinee.monotype).is_some();
                    after.truncate(mark);
                    if owned {
                        let top = Top::Hoisted(std::ptr::from_ref(expression), position);
                        Source::Owned { top, owners: vec![] }
                    } else {
                        Source::Shared
                    }
                }
            };
            sources.push(source);
        }
        let mut owned = true;
        let mut remaining = stock.clone();
        for alternative in alternatives {
            let index = self.alternatives.len();
            let mut bound = vec![];
            for pattern in &alternative.patterns {
                pattern.for_each_local(&mut |local| bound.push(local.id));
            }
            self.alternatives.push(bound);
            let mut alternative_stock = stock.clone();
            for (pattern, source) in alternative.patterns.iter().zip(&sources) {
                let Source::Owned { top, owners } = source else { continue };
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
            let alternative_owned = match &alternative.body {
                Guarded::Unconditional(body) => {
                    self.expression(body, tail, &mut alternative_stock, after)
                }
                Guarded::Guards(branches) => {
                    let mut all = true;
                    for branch in branches {
                        for guard in &branch.guards {
                            let value = guard.value();
                            self.expression(value, false, &mut vec![], &mut vec![]);
                            alternative_stock.retain(|spare| {
                                !spare.owners.iter().any(|&owner| uses_local(value, owner))
                            });
                        }
                        let mut branch_stock = alternative_stock.clone();
                        all &= self.expression(&branch.body, tail, &mut branch_stock, after);
                        remaining.retain(|spare| {
                            branch_stock.iter().any(|other| other.local == spare.local)
                        });
                    }
                    all
                }
            };
            remaining
                .retain(|spare| alternative_stock.iter().any(|other| other.local == spare.local));
            owned &= alternative_owned;
        }
        *stock = remaining;
        owned
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
                            (self.fresh(), Origin::Hoisted { case, position, alternative })
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
                        stock.push(Spare { local, data: data.clone(), origin, owners });
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

    fn adopt(&mut self, local: &Local, ancestors: Vec<LocalId>, body: &Guarded) {
        if self.cells.cell(local.monotype).is_some()
            && self.is_linear(local.id, &ancestors, Scope::Guarded(body))
        {
            self.owned.insert(local.id, ancestors);
        }
    }

    fn is_linear(&mut self, target: LocalId, ancestors: &[LocalId], scope: Scope<'_>) -> bool {
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
        let counter = Counter { target, conflicts: &family };
        let paths = match scope {
            Scope::Expression(expression) => counter.count(self, expression),
            Scope::Guarded(guarded) => counter.guarded(self, guarded),
        };
        paths.all_linear()
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
}

#[derive(Clone, Copy)]
enum Scope<'e> {
    Expression(&'e Expression),
    Guarded(&'e Guarded),
}

#[derive(Clone)]
enum Source {
    Owned { top: Top, owners: Vec<LocalId> },
    Shared,
}

#[derive(Clone, Copy)]
enum Top {
    Local(LocalId),
    Hoisted(*const Expression, usize),
}

struct Counter<'f> {
    target: LocalId,
    conflicts: &'f FxHashSet<LocalId>,
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
                let branches = self.count(planner, then).or(self.count(planner, otherwise));
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
                let mut guards = Paths::empty();
                let mut bodies = Paths::nothing();
                for alternative in alternatives {
                    match &alternative.body {
                        Guarded::Unconditional(body) => {
                            bodies = bodies.or(self.count(planner, body));
                        }
                        Guarded::Guards(branches) => {
                            for branch in branches {
                                for guard in &branch.guards {
                                    let value = guard.value();
                                    guards = guards.then(self.count(planner, value));
                                }
                                bodies = bodies.or(self.count(planner, &branch.body));
                            }
                        }
                    }
                }
                let bodies = if alternatives.is_empty() { Paths::empty() } else { bodies };
                paths.then(guards).then(bodies)
            }
            ExpressionKind::Apply { function, arguments }
                if !planner.cells.retains(expression.monotype) =>
            {
                let mut paths = self.count(planner, function);
                for argument in arguments {
                    let argument_paths = match argument.kind {
                        ExpressionKind::Local(id) if id == self.target => Paths::event(Event::Peek),
                        _ => self.count(planner, argument),
                    };
                    paths = paths.unordered(argument_paths);
                }
                paths
            }
            ExpressionKind::Foreign { arguments, .. }
                if !planner.cells.retains(expression.monotype) =>
            {
                let mut paths = Paths::empty();
                for argument in arguments {
                    let argument_paths = match argument.kind {
                        ExpressionKind::Local(id) if id == self.target => Paths::event(Event::Peek),
                        _ => self.count(planner, argument),
                    };
                    paths = paths.unordered(argument_paths);
                }
                paths
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
    guarded_expressions(guarded).into_iter().filter(|expression| uses_local(expression, local)).count()
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
        while let Some(variant) = pending.pop() {
            let mut function = self.program.function(variant.function).clone();
            let plan = Planner::new(self.program, cells, &mut self.facts, variant).plan(&function);
            let callbacks = plan.callbacks.values();
            let targets = plan.calls.values().map(|(target, _)| target).chain(callbacks);
            let mut targets: Vec<Variant> = targets.copied().collect();
            targets.sort_unstable_by_key(|target| (target.function, target.owned, target.donor));
            for target in targets {
                if !self.identifiers.contains_key(&target) {
                    let next = FunctionId(self.identifiers.len() as u32);
                    self.identifiers.insert(target, next);
                    pending.push(target);
                }
            }
            self.rewrite(&mut function.body, &plan, cells);
            if !variant.is_plain() {
                function.name = SmolStr::new(format!("{}{REUSING}", function.name));
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
            functions[id.0 as usize] = Some(function);
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
        let duplicates = self.duplicates(&mut functions);
        for function in &mut functions {
            redirect(&mut function.body, &duplicates);
        }
        let (program, renumbering) = prune_unreachable(functions, self.program.entry);
        let materialized = materialized
            .into_iter()
            .filter_map(|(function, local)| Some((*renumbering.get(&function)?, local)))
            .collect();
        Reused { program, materialized }
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

    fn rewrite(&self, expression: &mut Expression, plan: &Plan, cells: &mut impl Cells) {
        let key = std::ptr::from_ref(&*expression);
        if let ExpressionKind::Case { alternatives, .. } = &mut expression.kind {
            for alternative in alternatives.iter_mut() {
                for pattern in &mut alternative.patterns {
                    rewrite_pattern(pattern, plan);
                }
            }
        }
        for_each_child_mut(expression, &mut |child| self.rewrite(child, plan, cells));
        if let Some(&local) = plan.constructs.get(&key) {
            let monotype = expression.monotype;
            let kind = std::mem::replace(&mut expression.kind, ExpressionKind::Unit);
            let ExpressionKind::Construct { data, constructor, arguments } = kind else {
                unreachable!("invariant violated: a planned reuse is not a construction")
            };
            let cell = Box::new(Expression::new(ExpressionKind::Local(local), monotype));
            expression.kind = ExpressionKind::Reuse { cell, data, constructor, arguments };
        }
        if let Some(target) = plan.callbacks.get(&key) {
            expression.kind = ExpressionKind::Function(self.identifiers[target]);
        }
        if let Some(&(target, donor)) = plan.calls.get(&key) {
            let id = self.identifiers[&target];
            let ExpressionKind::Apply { function, arguments } = &mut expression.kind else {
                unreachable!("invariant violated: a planned variant call is not an application")
            };
            let callee = self.program.function(target.function);
            let mut parameters: Vec<MonotypeId> =
                callee.parameters.iter().map(|parameter| parameter.monotype).collect();
            if let Some(donor) = donor {
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
