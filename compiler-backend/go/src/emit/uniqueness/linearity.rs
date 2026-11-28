//! Whether a local is the only reference to its cells wherever a body uses it.

use std::cell::Cell;

use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use super::paths::{Event, Paths};
use crate::emit::uses_local;
use crate::monomorphic::traversal::{for_each_child, for_each_guarded_child};
use crate::monomorphic::{
    Expression, ExpressionKind, Guarded, LocalId, Pattern, PatternKind, RecordUpdate,
};
use crate::monotype::MonotypeId;

/// What the framework asks of the program's data layout and of the functions a body calls.
pub(in crate::emit) trait Shapes {
    /// Whether `call` only reads `argument`, a local holding cells, and keeps none of them.
    fn inspects(&mut self, call: &Expression, argument: &Expression) -> bool;
    /// Whether a field of type `field` of a cell of type `cell` is part of its spine: a cell of
    /// the same data that the outer cell's owner owns too.
    fn is_spine(&mut self, cell: MonotypeId, field: MonotypeId) -> bool;
    /// Whether a call hands on the locals it is passed only once every argument is computed, so
    /// that the others may still read them: `f (lookup k m) m`.
    fn passes_locals_last(&self) -> bool {
        false
    }
    /// Whether a call runs a callback it is passed while it runs, any number of times, and keeps
    /// nothing of it: `Array.filter (\x -> member x m) xs`.
    fn runs_now(&mut self, _call: &Expression, _callback: &Expression) -> bool {
        false
    }
    /// Whether an effect that uses a local only to read it peeks at it, as a callback that runs
    /// now does: the effect may run any number of times, but reads nothing that changes.
    fn effects_only_peek(&self) -> bool {
        false
    }
    /// Whether a call does nothing with a local it is passed that counts as a use.
    fn ignores(&mut self, _call: &Expression, _argument: &Expression) -> bool {
        false
    }
    /// Whether a closure that reads only fields of a record off the followed field's path keeps
    /// nothing of that field.
    fn closures_keep_what_they_read(&self) -> bool {
        false
    }
    /// Whether a closure that only reads a local ([`Shapes::only_reads`]) peeks at it, so that
    /// the local is linear where nothing consumes it.
    fn closures_only_read(&self) -> bool {
        false
    }
    /// Whether such a closure's reads count: a peek that forbids consuming the local anywhere,
    /// as the closure may run after it. Otherwise they are no use of the local at all.
    fn closure_reads_count(&self) -> bool {
        true
    }
    /// Whether `call` only reads `argument` and keeps nothing of it, so that a closure that
    /// uses a local only in such calls reads it whenever it runs, and changes nothing.
    fn only_reads(&mut self, _call: &Expression, _argument: &Expression) -> bool {
        false
    }
    /// Whether a value of the type may hold cells of the followed local.
    fn holds_cells(&mut self, _monotype: MonotypeId) -> bool {
        true
    }
}

/// One branch of an `if` (`Then`, `Otherwise`) or of a `case` (the alternative, and the guarded
/// branch within it when it has guards).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::emit) enum Branch {
    Then,
    Otherwise,
    Alternative(usize, Option<usize>),
}

/// The branches each conditional is known to take, by its address; a conditional missing from it
/// may take any branch.
pub(in crate::emit) type Forced = FxHashMap<*const Expression, Vec<Branch>>;

/// The code a local is used in: an expression or the body of an alternative.
#[derive(Clone, Copy)]
pub(in crate::emit) enum Scope<'e> {
    Expression(&'e Expression),
    Guarded(&'e Guarded),
}

impl<'e> Scope<'e> {
    pub(in crate::emit) fn expressions(self) -> Vec<&'e Expression> {
        match self {
            Scope::Expression(expression) => vec![expression],
            Scope::Guarded(guarded) => guarded_expressions(guarded),
        }
    }
}

/// Whether `target` is unique in `scope`: on every path the scope can take, it is consumed at
/// most once, its relatives (`ancestors`, and the locals that patterns on it bind to its spine)
/// are not used next to that consumption, and it is not read after it.
pub(in crate::emit) fn is_unique(
    shapes: &mut impl Shapes,
    target: LocalId,
    ancestors: &[LocalId],
    scope: Scope<'_>,
    forced: &Forced,
) -> bool {
    let relatives = relatives(shapes, target, ancestors, scope);
    let counter = Counter::new(target, None, &relatives, forced);
    let paths = match scope {
        Scope::Expression(expression) => counter.count(shapes, expression),
        Scope::Guarded(guarded) => counter.guarded(shapes, guarded),
    };
    counter.is_linear(paths)
}

/// Whether `target` is only ever read in `scope`: no order consumes it.
pub(in crate::emit) fn is_only_read(
    shapes: &mut impl Shapes,
    target: LocalId,
    scope: Scope<'_>,
) -> bool {
    let relatives = FxHashSet::default();
    let forced = Forced::default();
    let counter = Counter::new(target, None, &relatives, &forced);
    let paths = match scope {
        Scope::Expression(expression) => counter.count(shapes, expression),
        Scope::Guarded(guarded) => counter.guarded(shapes, guarded),
    };
    paths.never_consumed()
}

/// Whether the field `label` of the record `record` is unique in `scope`: on every path the
/// field is consumed at most once, by reading it (`record.label`) or by passing on the whole
/// record or an update of it that keeps the field, and read only before that.
pub(in crate::emit) fn is_unique_field(
    shapes: &mut impl Shapes,
    record: LocalId,
    label: &str,
    scope: Scope<'_>,
) -> bool {
    is_unique_path(shapes, record, &[SmolStr::new(label)], scope)
}

/// [`is_unique_field`] of a field of fields: `record.outer.inner` is consumed by reading it,
/// or by reading or passing on `record.outer` or `record` whole.
pub(in crate::emit) fn is_unique_path(
    shapes: &mut impl Shapes,
    record: LocalId,
    path: &[SmolStr],
    scope: Scope<'_>,
) -> bool {
    let relatives = FxHashSet::default();
    let forced = Forced::default();
    let counter = Counter::new(record, Some(path), &relatives, &forced);
    let paths = match scope {
        Scope::Expression(expression) => counter.count(shapes, expression),
        Scope::Guarded(guarded) => counter.guarded(shapes, guarded),
    };
    counter.is_linear(paths)
}

/// The locals that share cells with `target` in `scope`: its ancestors, and the locals that
/// patterns on it, or on those locals, bind to its spine.
pub(in crate::emit) fn relatives(
    shapes: &mut impl Shapes,
    target: LocalId,
    ancestors: &[LocalId],
    scope: Scope<'_>,
) -> FxHashSet<LocalId> {
    let mut family = FxHashSet::default();
    family.insert(target);
    for expression in scope.expressions() {
        descendants(shapes, expression, &mut family);
    }
    family.remove(&target);
    family.extend(ancestors.iter().copied());
    family
}

fn descendants(shapes: &mut impl Shapes, expression: &Expression, family: &mut FxHashSet<LocalId>) {
    if let ExpressionKind::Case { scrutinees, alternatives } = &expression.kind {
        for (position, scrutinee) in scrutinees.iter().enumerate() {
            let ExpressionKind::Local(id) = scrutinee.kind else { continue };
            if !family.contains(&id) {
                continue;
            }
            for alternative in alternatives {
                spine_locals(shapes, &alternative.patterns[position], family);
            }
        }
    }
    for_each_child(expression, &mut |child| descendants(shapes, child, family));
}

fn spine_locals(shapes: &mut impl Shapes, pattern: &Pattern, family: &mut FxHashSet<LocalId>) {
    match &pattern.kind {
        PatternKind::Variable(local) => {
            family.insert(local.id);
        }
        PatternKind::Named { local, pattern } => {
            family.insert(local.id);
            spine_locals(shapes, pattern, family);
        }
        PatternKind::Constructor { arguments, .. } => {
            for argument in arguments {
                if shapes.is_spine(pattern.monotype, argument.monotype) {
                    spine_locals(shapes, argument, family);
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

pub(in crate::emit) fn guarded_expressions(guarded: &Guarded) -> Vec<&Expression> {
    let mut expressions = vec![];
    for_each_guarded_child(guarded, &mut |expression| expressions.push(expression));
    expressions
}

struct Counter<'f> {
    target: LocalId,
    /// The field of the record `target`, by the labels that lead to it, that is followed instead
    /// of the whole value.
    field: Option<&'f [SmolStr]>,
    relatives: &'f FxHashSet<LocalId>,
    forced: &'f Forced,
    /// Whether a closure reads the target whenever it runs, which may be after anything.
    read_by_closure: Cell<bool>,
}

impl<'f> Counter<'f> {
    fn new(
        target: LocalId,
        field: Option<&'f [SmolStr]>,
        relatives: &'f FxHashSet<LocalId>,
        forced: &'f Forced,
    ) -> Counter<'f> {
        Counter { target, field, relatives, forced, read_by_closure: Cell::new(false) }
    }

    /// Whether the target is linear on all paths: a closure that reads it may read it after
    /// any of them, so then nothing may consume it.
    fn is_linear(&self, paths: Paths) -> bool {
        let closures_see_it_unchanged = !self.read_by_closure.get() || paths.never_consumed();
        paths.all_linear() && closures_see_it_unchanged
    }
    fn count(&self, shapes: &mut impl Shapes, expression: &Expression) -> Paths {
        if let Some(field) = self.field
            && let Some(paths) = self.count_field(shapes, field, expression)
        {
            return paths;
        }
        match &expression.kind {
            ExpressionKind::Local(id) if *id == self.target => Paths::event(Event::Consume),
            ExpressionKind::Local(id) if self.relatives.contains(id) => {
                Paths::event(Event::Conflict)
            }
            ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. }
                if shapes.effects_only_peek() =>
            {
                let mut children = vec![];
                for_each_child(expression, &mut |child| children.push(child));
                let mut paths = Paths::empty();
                for child in children {
                    paths = paths.then(self.count(shapes, child));
                }
                paths.repeated()
            }
            ExpressionKind::Lambda { .. }
            | ExpressionKind::Closure { .. }
            | ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. } => {
                let uses = match self.field {
                    Some(path) if shapes.closures_keep_what_they_read() => {
                        uses_followed(expression, self.target, path)
                    }
                    _ => uses_local(expression, self.target),
                };
                let only_reads = uses
                    && shapes.closures_only_read()
                    && matches!(&expression.kind, ExpressionKind::Lambda { body, .. }
                        if only_read(shapes, self.target, self.field, body));
                if only_reads && !shapes.closure_reads_count() {
                    Paths::empty()
                } else if only_reads {
                    self.read_by_closure.set(true);
                    Paths::event(Event::Peek)
                } else if uses {
                    Paths::event(Event::Shared)
                } else if self.relatives.iter().any(|&conflict| uses_local(expression, conflict)) {
                    Paths::event(Event::Conflict)
                } else {
                    Paths::empty()
                }
            }
            ExpressionKind::Let { bindings, body } => {
                let mut paths = Paths::empty();
                for binding in bindings {
                    paths = paths.then(self.count(shapes, &binding.value));
                }
                paths.then(self.count(shapes, body))
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let allowed = self.forced.get(&std::ptr::from_ref(expression));
                let taken =
                    |branch: Branch| allowed.is_none_or(|allowed| allowed.contains(&branch));
                let mut branches = Paths::nothing();
                if taken(Branch::Then) {
                    branches = branches.or(self.count(shapes, then));
                }
                if taken(Branch::Otherwise) {
                    branches = branches.or(self.count(shapes, otherwise));
                }
                self.count(shapes, condition).then(branches)
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
                        _ => self.count(shapes, scrutinee),
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
                                bodies = bodies.or(self.count(shapes, body));
                            }
                        }
                        Guarded::Guards(branches) => {
                            for (position, branch) in branches.iter().enumerate() {
                                for guard in &branch.guards {
                                    let value = guard.value();
                                    guards = guards.then(self.count(shapes, value));
                                }
                                if taken(index, Some(position)) {
                                    bodies = bodies.or(self.count(shapes, &branch.body));
                                }
                            }
                        }
                    }
                }
                let bodies = if alternatives.is_empty() { Paths::empty() } else { bodies };
                paths.then(guards).then(bodies)
            }
            ExpressionKind::Apply { function, arguments } => {
                let paths = self.count(shapes, function);
                self.call(shapes, expression, arguments, paths)
            }
            ExpressionKind::Foreign { arguments, .. } => {
                self.call(shapes, expression, arguments, Paths::empty())
            }
            ExpressionKind::Construct { arguments, .. } => self.stored(shapes, arguments.iter()),
            ExpressionKind::Record(fields) => {
                self.stored(shapes, fields.iter().map(|(_, value)| value))
            }
            _ => {
                let mut children = vec![];
                for_each_child(expression, &mut |child| children.push(child));
                let mut paths = Paths::empty();
                for child in children {
                    paths = paths.unordered(self.count(shapes, child));
                }
                paths
            }
        }
    }

    fn call(
        &self,
        shapes: &mut impl Shapes,
        call: &Expression,
        arguments: &[Expression],
        mut paths: Paths,
    ) -> Paths {
        let mut passed = Paths::empty();
        for argument in arguments {
            let followed = match &argument.kind {
                ExpressionKind::Local(id) => *id == self.target,
                ExpressionKind::Access { .. } => {
                    self.field.is_some_and(|path| self.depth(argument) == Some(path.len()))
                }
                _ => false,
            };
            if followed && shapes.ignores(call, argument) {
                continue;
            }
            let inspected = followed && shapes.inspects(call, argument);
            if followed && !inspected && self.field.is_none() && shapes.passes_locals_last() {
                passed = passed.unordered(Paths::event(Event::Consume));
                continue;
            }
            let argument_paths = match &argument.kind {
                _ if inspected => Paths::event(Event::Peek),
                ExpressionKind::Lambda { body, .. } if shapes.runs_now(call, argument) => {
                    self.count(shapes, body).repeated()
                }
                _ => self.count(shapes, argument),
            };
            paths = paths.unordered(argument_paths);
        }
        paths.then(passed)
    }

    /// How many labels of the followed field's path `expression` reads of the target: none for
    /// the target itself.
    fn depth(&self, expression: &Expression) -> Option<usize> {
        match &expression.kind {
            ExpressionKind::Local(id) if *id == self.target => Some(0),
            ExpressionKind::Access { record, label } => {
                let path = self.field?;
                let depth = self.depth(record)?;
                (depth < path.len() && path[depth] == *label).then_some(depth + 1)
            }
            _ => None,
        }
    }

    /// The uses of the followed field that differ from uses of a local: reading it, reading
    /// another field, updating the record, matching on the field or on the record.
    fn count_field(
        &self,
        shapes: &mut impl Shapes,
        field: &[SmolStr],
        expression: &Expression,
    ) -> Option<Paths> {
        let paths = match &expression.kind {
            ExpressionKind::Access { record, label } => {
                let depth = self.depth(record)?;
                match field.get(depth) == Some(label) {
                    true => Paths::event(Event::Consume),
                    false => Paths::empty(),
                }
            }
            ExpressionKind::Update { record, updates } => {
                let depth = self.depth(record)?;
                let replaced = replaces(updates, &field[depth..]);
                let mut values = vec![];
                for update in updates {
                    update_values(update, &mut values);
                }
                let mut paths =
                    if replaced { Paths::empty() } else { Paths::event(Event::Consume) };
                for value in values {
                    paths = paths.unordered(self.count(shapes, value));
                }
                paths
            }
            ExpressionKind::Case { scrutinees, .. }
                if scrutinees.iter().any(|scrutinee| self.depth(scrutinee).is_some()) =>
            {
                return Some(self.count_field_case(shapes, field, expression));
            }
            _ => return None,
        };
        Some(paths)
    }

    /// A `case` on the followed field only peeks at it when its patterns bind nothing of the
    /// field's spine; one that binds the spine, or matches on the whole record, consumes it.
    fn count_field_case(
        &self,
        shapes: &mut impl Shapes,
        field: &[SmolStr],
        expression: &Expression,
    ) -> Paths {
        let ExpressionKind::Case { scrutinees, alternatives } = &expression.kind else {
            unreachable!("invariant violated: a field case is not a case")
        };
        let mut paths = Paths::empty();
        for (position, scrutinee) in scrutinees.iter().enumerate() {
            let depth = self.depth(scrutinee);
            let scrutinised = match &scrutinee.kind {
                ExpressionKind::Access { .. } if depth == Some(field.len()) => {
                    let mut spine = FxHashSet::default();
                    for alternative in alternatives {
                        spine_locals(shapes, &alternative.patterns[position], &mut spine);
                    }
                    if spine.is_empty() {
                        Paths::event(Event::Peek)
                    } else {
                        Paths::event(Event::Shared)
                    }
                }
                _ if depth.is_some() => Paths::event(Event::Consume),
                _ => self.count(shapes, scrutinee),
            };
            paths = paths.then(scrutinised);
        }
        let mut guards = Paths::empty();
        let mut bodies = Paths::nothing();
        for alternative in alternatives {
            match &alternative.body {
                Guarded::Unconditional(body) => bodies = bodies.or(self.count(shapes, body)),
                Guarded::Guards(branches) => {
                    for branch in branches {
                        for guard in &branch.guards {
                            guards = guards.then(self.count(shapes, guard.value()));
                        }
                        bodies = bodies.or(self.count(shapes, &branch.body));
                    }
                }
            }
        }
        let bodies = if alternatives.is_empty() { Paths::empty() } else { bodies };
        paths.then(guards).then(bodies)
    }

    /// The fields of a construction: a field that is a local only stores a reference to it once
    /// the others are computed, and storing changes no cell, so reading the local in another
    /// field (`Node (rank b + 1) x left b`) comes first.
    fn stored<'e>(
        &self,
        shapes: &mut impl Shapes,
        fields: impl Iterator<Item = &'e Expression>,
    ) -> Paths {
        let mut computed = Paths::empty();
        let mut stored = Paths::empty();
        for field in fields {
            match field.kind {
                ExpressionKind::Local(_) => stored = stored.unordered(self.count(shapes, field)),
                _ => computed = computed.unordered(self.count(shapes, field)),
            }
        }
        computed.then(stored)
    }

    fn guarded(&self, shapes: &mut impl Shapes, guarded: &Guarded) -> Paths {
        match guarded {
            Guarded::Unconditional(body) => self.count(shapes, body),
            Guarded::Guards(branches) => {
                let mut guards = Paths::empty();
                let mut bodies = Paths::nothing();
                for branch in branches {
                    for guard in &branch.guards {
                        let value = guard.value();
                        guards = guards.then(self.count(shapes, value));
                    }
                    bodies = bodies.or(self.count(shapes, &branch.body));
                }
                guards.then(bodies)
            }
        }
    }
}

/// Where an expression stands to the followed value of `target`: the depth of an access chain
/// along the followed field's path that it is (`Ok`), or a read of a field off that path
/// (`Err`); `None` for an expression that is neither.
fn followed_depth(
    target: LocalId,
    field: Option<&[SmolStr]>,
    expression: &Expression,
) -> Option<Result<usize, ()>> {
    match &expression.kind {
        ExpressionKind::Local(id) if *id == target => Some(Ok(0)),
        ExpressionKind::Access { record, label } => match followed_depth(target, field, record)? {
            Ok(depth) => match field {
                Some(path) if depth < path.len() && path[depth] != *label => Some(Err(())),
                _ => Some(Ok(depth + 1)),
            },
            Err(()) => Some(Err(())),
        },
        _ => None,
    }
}

/// Whether `expression` uses the followed value of `target` only to read it: as an argument
/// that its call only reads ([`Shapes::only_reads`]), as a scrutinee whose patterns bind locals
/// that, where they may hold its cells, are only read in turn, or by reading another field.
fn only_read(
    shapes: &mut impl Shapes,
    target: LocalId,
    field: Option<&[SmolStr]>,
    expression: &Expression,
) -> bool {
    match followed_depth(target, field, expression) {
        Some(Ok(_)) => return false,
        Some(Err(())) => return true,
        None => {}
    }
    match &expression.kind {
        ExpressionKind::Apply { arguments, .. } | ExpressionKind::Foreign { arguments, .. } => {
            if let ExpressionKind::Apply { function, .. } = &expression.kind
                && !only_read(shapes, target, field, function)
            {
                return false;
            }
            arguments.iter().all(|argument| match followed_depth(target, field, argument) {
                Some(Ok(_)) => shapes.only_reads(expression, argument),
                Some(Err(())) => true,
                None => only_read(shapes, target, field, argument),
            })
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            for (position, scrutinee) in scrutinees.iter().enumerate() {
                match followed_depth(target, field, scrutinee) {
                    Some(Ok(_)) => {
                        for alternative in alternatives {
                            let mut bound = vec![];
                            pattern_locals(&alternative.patterns[position], &mut bound);
                            for local in bound {
                                if !shapes.holds_cells(local.monotype) {
                                    continue;
                                }
                                let body = guarded_expressions(&alternative.body);
                                let reads = |shapes: &mut _, body: &&Expression| {
                                    only_read(shapes, local.id, None, body)
                                };
                                if !body.iter().all(|body| reads(shapes, body)) {
                                    return false;
                                }
                            }
                        }
                    }
                    Some(Err(())) => {}
                    None => {
                        if !only_read(shapes, target, field, scrutinee) {
                            return false;
                        }
                    }
                }
            }
            alternatives.iter().all(|alternative| {
                let body = guarded_expressions(&alternative.body);
                body.iter().all(|body| only_read(shapes, target, field, body))
            })
        }
        _ => {
            let mut children = vec![];
            for_each_child(expression, &mut |child| children.push(child));
            children.into_iter().all(|child| only_read(shapes, target, field, child))
        }
    }
}

/// The locals a pattern binds, at any depth.
fn pattern_locals<'p>(pattern: &'p Pattern, locals: &mut Vec<&'p crate::monomorphic::Local>) {
    match &pattern.kind {
        PatternKind::Variable(local) => locals.push(local),
        PatternKind::Named { local, pattern } => {
            locals.push(local);
            pattern_locals(pattern, locals);
        }
        PatternKind::Constructor { arguments: patterns, .. }
        | PatternKind::Array(patterns)
        | PatternKind::Closure { captures: patterns, .. } => {
            patterns.iter().for_each(|pattern| pattern_locals(pattern, locals));
        }
        PatternKind::Record(fields) => {
            fields.iter().for_each(|(_, pattern)| pattern_locals(pattern, locals));
        }
        PatternKind::Wildcard | PatternKind::Literal(_) => {}
    }
}

/// Whether `expression` uses `target` otherwise than to read a field off the path to the
/// followed one.
fn uses_followed(expression: &Expression, target: LocalId, path: &[SmolStr]) -> bool {
    match &expression.kind {
        ExpressionKind::Access { record, label } if matches!(record.kind, ExpressionKind::Local(id) if id == target) => {
            *label == path[0]
        }
        ExpressionKind::Local(id) => *id == target,
        _ => {
            let mut found = false;
            for_each_child(expression, &mut |child| {
                found = found || uses_followed(child, target, path);
            });
            found
        }
    }
}

/// Whether updates replace the field the labels lead to, or a field that holds it.
fn replaces(updates: &[RecordUpdate], path: &[SmolStr]) -> bool {
    let Some(first) = path.first() else { return true };
    updates.iter().any(|update| match update {
        RecordUpdate::Leaf { label, .. } => label == first,
        RecordUpdate::Branch { label, updates } => label == first && replaces(updates, &path[1..]),
    })
}

fn update_values<'e>(update: &'e RecordUpdate, values: &mut Vec<&'e Expression>) {
    match update {
        RecordUpdate::Leaf { value, .. } => values.push(value),
        RecordUpdate::Branch { updates, .. } => {
            updates.iter().for_each(|update| update_values(update, values))
        }
    }
}

#[cfg(test)]
mod tests {
    use smol_str::SmolStr;

    use super::{Branch, Forced, Scope, Shapes, is_unique};
    use crate::monomorphic::{Binding, Expression, ExpressionKind, FunctionId, Local, LocalId};
    use crate::monotype::MonotypeId;

    const CONSUME: FunctionId = FunctionId(0);
    const INSPECT: FunctionId = FunctionId(1);

    struct Layout;

    impl Shapes for Layout {
        fn inspects(&mut self, call: &Expression, _: &Expression) -> bool {
            let ExpressionKind::Apply { function, .. } = &call.kind else { return false };
            matches!(function.kind, ExpressionKind::Function(INSPECT))
        }

        fn is_spine(&mut self, _: MonotypeId, _: MonotypeId) -> bool {
            true
        }
    }

    fn expression(kind: ExpressionKind) -> Expression {
        Expression::new(kind, MonotypeId::for_tests())
    }

    fn local(id: u32) -> Expression {
        expression(ExpressionKind::Local(LocalId(id)))
    }

    fn call(function: FunctionId, arguments: Vec<Expression>) -> Expression {
        let function = Box::new(expression(ExpressionKind::Function(function)));
        expression(ExpressionKind::Apply { function, arguments })
    }

    fn binding(id: u32, value: Expression, body: Expression) -> Expression {
        let local = Local {
            id: LocalId(id),
            name: SmolStr::new_static("bound"),
            monotype: MonotypeId::for_tests(),
        };
        let bindings = vec![Binding { local, value }];
        expression(ExpressionKind::Let { bindings, body: Box::new(body) })
    }

    fn conditional(then: Expression, otherwise: Expression) -> Expression {
        expression(ExpressionKind::If {
            condition: Box::new(local(9)),
            then: Box::new(then),
            otherwise: Box::new(otherwise),
        })
    }

    fn unique(body: &Expression) -> bool {
        is_unique(&mut Layout, LocalId(1), &[], Scope::Expression(body), &Forced::default())
    }

    #[test]
    fn a_local_passed_on_once_is_unique() {
        assert!(unique(&call(CONSUME, vec![local(1)])));
        assert!(unique(&call(CONSUME, vec![local(2), local(3)])));
    }

    #[test]
    fn a_local_passed_on_twice_is_shared() {
        assert!(!unique(&call(CONSUME, vec![local(1), local(1)])));
        assert!(!unique(&binding(2, local(1), call(CONSUME, vec![local(1)]))));
    }

    #[test]
    fn each_branch_may_consume_it_once() {
        let branches = conditional(call(CONSUME, vec![local(1)]), local(1));
        assert!(unique(&branches));
        let twice = conditional(local(1), call(CONSUME, vec![local(1), local(1)]));
        assert!(!unique(&twice));
    }

    #[test]
    fn it_may_be_inspected_before_it_is_consumed_but_not_after() {
        let inspected = call(INSPECT, vec![local(1)]);
        assert!(unique(&binding(2, inspected.clone(), call(CONSUME, vec![local(1)]))));
        assert!(!unique(&binding(2, call(CONSUME, vec![local(1)]), inspected)));
    }

    #[test]
    fn a_closure_capturing_it_shares_it() {
        let parameters = vec![];
        let lambda = expression(ExpressionKind::Lambda { parameters, body: Box::new(local(1)) });
        assert!(!unique(&lambda));
    }

    #[test]
    fn an_ancestor_used_next_to_it_shares_its_cells() {
        let body = call(CONSUME, vec![local(1), local(5)]);
        let scope = Scope::Expression(&body);
        assert!(is_unique(&mut Layout, LocalId(1), &[LocalId(6)], scope, &Forced::default()));
        assert!(!is_unique(&mut Layout, LocalId(1), &[LocalId(5)], scope, &Forced::default()));
    }

    #[test]
    fn a_branch_known_not_to_be_taken_does_not_count() {
        let body = conditional(local(1), call(CONSUME, vec![local(1), local(1)]));
        let scope = Scope::Expression(&body);
        let mut forced = Forced::default();
        forced.insert(std::ptr::from_ref(&body), vec![Branch::Then]);
        assert!(!is_unique(&mut Layout, LocalId(1), &[], scope, &Forced::default()));
        assert!(is_unique(&mut Layout, LocalId(1), &[], scope, &forced));
    }
}
