use smol_str::SmolStr;

use crate::emit::inspection::inspects;
use crate::emit::reuse::Cells;
use crate::emit::reuse::facts::Variant;
use crate::emit::reuse::plan::{Dynamic, Held, Spare};
use crate::emit::uniqueness::{self, Forced, Scope};
use crate::foreign::{Boundary, Foreign, Iteration};
use crate::monomorphic::traversal::{for_each_child, mentions_local};
use crate::monomorphic::{Expression, ExpressionKind, FunctionId, Local, LocalId, RecordUpdate};
use crate::monotype::{DataType, MonotypeId};

use super::Planner;

impl<C: Cells> Planner<'_, C> {
    pub(super) fn expression<'e>(
        &mut self,
        expression: &'e Expression,
        tail: bool,
        stock: &mut Vec<Spare>,
        after: &mut Vec<&'e Expression>,
    ) -> Held {
        match &expression.kind {
            ExpressionKind::Local(id) => {
                stock.retain(|spare| !spare.owners.contains(id));
                if self.owned.contains_key(id) || self.owned_records.contains(id) {
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
                    !spare.owners.iter().any(|&owner| mentions_local(expression, owner))
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
                    && (self.cells.cell(expression.monotype).is_some()
                        || !self.cells.cell_fields(expression.monotype).is_empty()) =>
            {
                self.unordered(expression, stock, after);
                Held::Owned
            }
            ExpressionKind::Record(fields) => {
                let values: Vec<&'e Expression> = fields.iter().map(|(_, value)| value).collect();
                let held = self.arguments_of(&values, stock, after);
                if self.owns_cells(&values, &held) { Held::Owned } else { Held::Shared }
            }
            ExpressionKind::Update { record, updates } => {
                let mut values: Vec<&'e Expression> = vec![record];
                let mut nested = false;
                for update in updates {
                    match update {
                        RecordUpdate::Leaf { value, .. } => values.push(value),
                        RecordUpdate::Branch { .. } => nested = true,
                    }
                }
                if nested {
                    self.unordered(expression, stock, after);
                    return Held::Shared;
                }
                let held = self.arguments_of(&values, stock, after);
                match self.owns_updated_cells(record.monotype, &values[1..], &held) {
                    true => Held::Owned,
                    false => Held::Shared,
                }
            }
            _ => {
                self.unordered(expression, stock, after);
                Held::Shared
            }
        }
    }

    fn bind(&mut self, local: &Local, held: Held, scope: Scope<'_>) {
        if held.is_owned() && self.is_ownable_record(local, scope) {
            self.owned_records.insert(local.id);
            return;
        }
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
        stock.retain(|spare| !spare.owners.iter().any(|&owner| mentions_local(callback, owner)));
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
                || (self.cells.cell(function.parameters[position].monotype).is_none()
                    && self.cells.cell_fields(function.parameters[position].monotype).is_empty())
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
            return self.owned_record_callback(accumulator, body);
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

    fn owned_record_callback(&mut self, accumulator: &Local, body: &Expression) -> bool {
        if !reads_cell_fields_once(self.cells, body, accumulator.id, &mut vec![])
            && !self.is_ownable_record(accumulator, Scope::Expression(body))
        {
            return false;
        }
        let saved = self.plan.clone();
        self.owned_records.insert(accumulator.id);
        if self.expression(body, false, &mut vec![], &mut vec![]).is_owned() {
            return true;
        }
        self.owned_records.remove(&accumulator.id);
        self.plan = saved;
        false
    }

    /// Whether an update of a record owns the record's cells: the record it updates is owned,
    /// every cell it writes is owned, and no other value it writes holds such cells.
    fn owns_updated_cells(
        &mut self,
        record: MonotypeId,
        written: &[&Expression],
        held: &[Held],
    ) -> bool {
        let [base, held @ ..] = held else { return false };
        let cells = self.cells.cell_fields(record).into_iter().flat_map(|(_, cells)| cells);
        let cells: Vec<DataType> = cells.collect();
        if !base.is_owned() || cells.is_empty() {
            return false;
        }
        for (value, held) in written.iter().zip(held) {
            if self.cells.cell(value.monotype).is_some()
                || !self.cells.cell_fields(value.monotype).is_empty()
            {
                if !held.is_owned() {
                    return false;
                }
                continue;
            }
            if cells.iter().any(|cell| self.cells.holds(value.monotype, cell)) {
                return false;
            }
        }
        true
    }

    /// Whether a record local may be owned in `scope`: it has fields that are cells, and each
    /// of them is used at most once, whether read on its own or passed on with the record.
    pub(super) fn is_ownable_record(&mut self, record: &Local, scope: Scope<'_>) -> bool {
        let fields = self.cells.cell_fields(record.monotype);
        !fields.is_empty()
            && fields
                .iter()
                .all(|(label, _)| uniqueness::is_unique_field(self, record.id, label, scope))
    }

    fn owns_cells(&mut self, values: &[&Expression], held: &[Held]) -> bool {
        let mut cells = vec![];
        let mut owning = vec![];
        for value in values {
            if let Some(cell) = self.cells.cell(value.monotype) {
                cells.push(cell);
                owning.push(true);
                continue;
            }
            let fields = self.cells.cell_fields(value.monotype);
            owning.push(!fields.is_empty());
            cells.extend(fields.into_iter().flat_map(|(_, cells)| cells));
        }
        if cells.is_empty() {
            return false;
        }
        for ((value, held), owning) in values.iter().zip(held).zip(owning) {
            if owning {
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
            let Some(data) = self.cells.cell(parameters[position].monotype) else {
                let record = parameters[position].monotype;
                if held.is_owned() && !self.cells.cell_fields(record).is_empty() {
                    owned |= 1 << position;
                }
                continue;
            };
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
        | ExpressionKind::EffectEach { .. } => !mentions_local(expression, record),
        _ => {
            let mut once = true;
            for_each_child(expression, &mut |child| {
                once = once && reads_cell_fields_once(cells, child, record, read);
            });
            once
        }
    }
}
