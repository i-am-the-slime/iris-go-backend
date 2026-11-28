use smol_str::SmolStr;

use crate::emit::reuse::Cells;
use crate::emit::reuse::plan::{Dynamic, Held, Origin, Spare, is_true};
use crate::emit::uniqueness::{Forced, Scope, guarded_expressions};
use crate::monomorphic::traversal::mentions_local;
use crate::monomorphic::{
    Alternative, Binding, Edge, Expression, ExpressionKind, Guarded, GuardedBranch, Local, LocalId,
    Pattern, PatternKind,
};

use super::Planner;

impl<C: Cells> Planner<'_, C> {
    pub(super) fn case<'e>(
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
                    } else if self.owned_records.contains(id) {
                        Source::OwnedFields
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
                    let constant = match &scrutinee.kind {
                        ExpressionKind::Function(id) => self.is_owned_constant(*id),
                        ExpressionKind::Construct { arguments, .. } => arguments.is_empty(),
                        _ => false,
                    };
                    match self.cells.cell(scrutinee.monotype) {
                        // A constructor without fields, such as `Leaf`, has no cell to reuse.
                        Some(_) if constant => Source::Shared,
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
                    let matched: Vec<LocalId> = alternative_stock
                        .iter()
                        .filter(|spare| !stock.iter().any(|other| other.local == spare.local))
                        .map(|spare| spare.local)
                        .collect();
                    let mut all: Option<Held> = None;
                    for branch in branches {
                        for guard in &branch.guards {
                            let value = guard.value();
                            self.expression(value, false, &mut vec![], &mut vec![]);
                            alternative_stock.retain(|spare| {
                                !spare.owners.iter().any(|&owner| mentions_local(value, owner))
                            });
                        }
                        let mut branch_stock = alternative_stock.clone();
                        branch_stock.retain(|spare| {
                            !matched.contains(&spare.local) || unused_in_branch(spare, branch)
                        });
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
                    let usable = is_spare_usable(placing.body, &owners);
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
                    let usable = is_spare_usable(body, &owners);
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
        let fields: Vec<&Pattern> = match &pattern.kind {
            PatternKind::Constructor { arguments, .. } => arguments.iter().collect(),
            PatternKind::Record(fields) => fields.iter().map(|(_, field)| field).collect(),
            _ => return,
        };
        for field in fields {
            if let PatternKind::Variable(local) = &field.kind {
                self.adopt(local, vec![], body);
            }
        }
    }

    fn adopt(&mut self, local: &Local, ancestors: Vec<LocalId>, body: &Guarded) {
        if ancestors.is_empty() && self.is_ownable_record(local, Scope::Guarded(body)) {
            self.owned_records.insert(local.id);
            return;
        }
        if self.cells.cell(local.monotype).is_some()
            && self.is_linear(local.id, &ancestors, Scope::Guarded(body), &Forced::default())
        {
            self.owned.insert(local.id, ancestors);
        }
    }
}

fn pattern_name(pattern: &Pattern) -> SmolStr {
    match &pattern.kind {
        PatternKind::Variable(local) | PatternKind::Named { local, .. } => local.name.clone(),
        _ => SmolStr::new_static("cell"),
    }
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

fn alternative_expressions(alternative: &Alternative) -> Vec<&Expression> {
    guarded_expressions(&alternative.body)
}

/// Whether a cell an alternative's pattern matched may be rebuilt in its body: none of its
/// owners is used there. A guarded body is decided branch by branch (`unused_in_branch`), so
/// that a branch that drops the cell may reuse it while another passes its owner on.
fn is_spare_usable(body: &Guarded, owners: &[LocalId]) -> bool {
    match body {
        Guarded::Unconditional(_) => !owners.iter().any(|&owner| guarded_uses(body, owner) > 0),
        Guarded::Guards(_) => true,
    }
}

fn unused_in_branch(spare: &Spare, branch: &GuardedBranch) -> bool {
    !spare.owners.iter().any(|&owner| {
        mentions_local(&branch.body, owner)
            || branch.guards.iter().any(|guard| mentions_local(guard.value(), owner))
    })
}

fn guarded_uses(guarded: &Guarded, local: LocalId) -> usize {
    guarded_expressions(guarded)
        .into_iter()
        .filter(|expression| mentions_local(expression, local))
        .count()
}
