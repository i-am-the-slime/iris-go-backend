use smol_str::SmolStr;

use crate::foreign::{self, Foreign, Operator};
use crate::monomorphic::traversal::for_each_child;
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, FunctionId, Guard, Guarded, LocalId,
    PatternKind, RecordUpdate,
};

/// Where an accumulator keeps the array, or the string, that a loop appends to.
#[derive(Clone)]
pub(super) enum Place {
    /// The accumulator itself.
    Whole,
    /// A field of the accumulator record, by its label and its Go field.
    Field(SmolStr, String),
    /// The field at `index` of the accumulator's constructor `constructor`, read through the
    /// locals that a `case` on the accumulator binds to it. `go_field` is its Go field.
    Constructor { constructor: usize, index: usize, go_field: String },
}

#[derive(Clone, Copy)]
pub(super) struct Carried<'a> {
    pub accumulator: LocalId,
    pub place: &'a Place,
    /// The locals that patterns bind to the carried constructor field.
    aliases: &'a [LocalId],
    updates: bool,
    /// Whether the step is performed as it is read, as a loop in Effect runs its binds in order,
    /// rather than built as an action that may run any number of times.
    performed: bool,
}

impl<'a> Carried<'a> {
    pub(super) fn new(accumulator: LocalId, place: &'a Place) -> Carried<'a> {
        Carried { accumulator, place, aliases: &[], updates: false, performed: false }
    }

    pub(super) fn updating(accumulator: LocalId, place: &'a Place) -> Carried<'a> {
        Carried { accumulator, place, aliases: &[], updates: true, performed: false }
    }

    pub(super) fn performed(self, performed: bool) -> Carried<'a> {
        Carried { performed, ..self }
    }
}

/// The appends in `step` that may extend the carried value in place, when the step reads it
/// only to append to it or to return it unchanged.
pub(super) fn owned_snocs<'e>(
    carried: Carried<'_>,
    step: &'e Expression,
) -> Option<Vec<&'e Expression>> {
    let aliases = aliases(carried, step)?;
    let carried = Carried { aliases: &aliases, ..carried };
    if spine_reads(carried, step, true) > 1 {
        return None;
    }
    let mut owned = vec![];
    results(carried, step, &mut owned)?;
    Some(owned)
}

#[derive(Clone, Copy)]
pub(super) struct TailCall {
    pub function: FunctionId,
    pub arity: usize,
    pub position: usize,
}

pub(super) fn owned_loop_snocs<'e>(
    carried: Carried<'_>,
    body: &'e Expression,
    tail_call: TailCall,
) -> Option<Vec<&'e Expression>> {
    let aliases = aliases(carried, body)?;
    let carried = Carried { aliases: &aliases, ..carried };
    if spine_reads(carried, body, true) > 1 {
        return None;
    }
    let mut owned = vec![];
    loop_results(carried, body, tail_call, &mut owned)?;
    Some(owned)
}

fn aliases(carried: Carried<'_>, expression: &Expression) -> Option<Vec<LocalId>> {
    let mut aliases = constructor_aliases(carried, expression)?;
    loop {
        let known = aliases.len();
        let carried = Carried { aliases: &aliases, ..carried };
        let mut bound = vec![];
        crate::monomorphic::traversal::visit(expression, &mut |expression| {
            let ExpressionKind::Let { bindings, .. } = &expression.kind else { return };
            for binding in bindings {
                if is_carried(carried, &binding.value)
                    && !carried.aliases.contains(&binding.local.id)
                {
                    bound.push(binding.local.id);
                }
            }
        });
        aliases.extend(bound);
        if aliases.len() == known {
            return Some(aliases);
        }
    }
}

/// The locals bound to the carried constructor field by patterns on the accumulator; none when
/// a pattern binds the accumulator as a whole, which would read it once more.
fn constructor_aliases(carried: Carried<'_>, expression: &Expression) -> Option<Vec<LocalId>> {
    let Place::Constructor { constructor, index, .. } = *carried.place else {
        return Some(vec![]);
    };
    let mut aliases = vec![];
    let mut whole = false;
    crate::monomorphic::traversal::visit(expression, &mut |expression| {
        let ExpressionKind::Case { scrutinees, alternatives } = &expression.kind else { return };
        for (position, scrutinee) in scrutinees.iter().enumerate() {
            if !is_accumulator(carried, scrutinee) {
                continue;
            }
            for alternative in alternatives {
                match &alternative.patterns[position].kind {
                    PatternKind::Constructor { constructor: matched, arguments, .. }
                        if *matched == constructor =>
                    {
                        match &arguments[index].kind {
                            PatternKind::Variable(local) => aliases.push(local.id),
                            PatternKind::Wildcard => {}
                            _ => whole = true,
                        }
                    }
                    PatternKind::Constructor { .. } | PatternKind::Wildcard => {}
                    _ => whole = true,
                }
            }
        }
    });
    (!whole).then_some(aliases)
}

const SHARED: usize = 2;

fn loop_results<'e>(
    carried: Carried<'_>,
    expression: &'e Expression,
    tail_call: TailCall,
    owned: &mut Vec<&'e Expression>,
) -> Option<()> {
    if let Some(branches) = branches(expression) {
        for branch in branches {
            loop_results(carried, branch, tail_call, owned)?;
        }
        return Some(());
    }
    match &expression.kind {
        ExpressionKind::EffectBind { body, .. } if carried.performed => {
            loop_results(carried, body, tail_call, owned)
        }
        ExpressionKind::Apply { function, arguments }
            if matches!(function.kind, ExpressionKind::Function(id) if id == tail_call.function)
                && arguments.len() == tail_call.arity =>
        {
            results(carried, &arguments[tail_call.position], owned)
        }
        _ => Some(()),
    }
}

fn is_accumulator(carried: Carried<'_>, expression: &Expression) -> bool {
    matches!(expression.kind, ExpressionKind::Local(id) if id == carried.accumulator)
}

fn is_carried(carried: Carried<'_>, expression: &Expression) -> bool {
    match (&expression.kind, carried.place) {
        (ExpressionKind::Local(id), _) if carried.aliases.contains(id) => true,
        (ExpressionKind::Local(id), Place::Whole) => *id == carried.accumulator,
        (ExpressionKind::Access { record, label }, Place::Field(field, _)) => {
            label == field && is_accumulator(carried, record)
        }
        _ => false,
    }
}

/// `snoc carried x`, `carried <> [x, …]` or, for a string, `carried <> s`: the carried value,
/// which an owned append extends in place.
fn snoc_of_carried<'e>(carried: Carried<'_>, expression: &'e Expression) -> Option<&'e Expression> {
    let ExpressionKind::Foreign { foreign, arguments } = &expression.kind else { return None };
    if let Some(position) = write_position(carried, foreign) {
        let map = &arguments[position];
        return is_carried(carried, map).then_some(map);
    }
    let appends = match foreign {
        Foreign::Snoc | Foreign::Operator(Operator::StringAppend) => true,
        _ => {
            foreign.calls(foreign::ARRAY_APPEND)
                && matches!(arguments[1].kind, ExpressionKind::Array(_))
        }
    };
    (appends && is_carried(carried, &arguments[0])).then_some(&arguments[0])
}

pub(super) fn object_write_position(foreign: &Foreign) -> Option<usize> {
    if foreign.calls(foreign::OBJECT_INSERT) {
        Some(2)
    } else if foreign.calls(foreign::OBJECT_DELETE) {
        Some(1)
    } else {
        None
    }
}

fn map_write_position(foreign: &Foreign) -> Option<usize> {
    object_write_position(foreign).or_else(|| foreign::hash_map_write_position(foreign))
}

fn write_position(carried: Carried<'_>, foreign: &Foreign) -> Option<usize> {
    match foreign {
        Foreign::ArrayUpdated if carried.updates => Some(2),
        _ => map_write_position(foreign),
    }
}

fn is_borrowing(foreign: &Foreign) -> bool {
    matches!(foreign, Foreign::Operator(Operator::ArrayLength | Operator::ArrayIndex))
        || matches!(foreign, Foreign::MaybeIndex)
        || foreign.calls(foreign::OBJECT_LOOKUP)
        || foreign.calls(foreign::OBJECT_SIZE)
        || foreign.calls(foreign::OBJECT_INDEX)
        || foreign::borrows_hash_map(foreign)
}

fn owned_appends_of<'e>(
    carried: Carried<'_>,
    expression: &'e Expression,
    owned: &mut Vec<&'e Expression>,
) -> Option<()> {
    if let Some(snoc) = snoc_of_carried(carried, expression) {
        owned.push(snoc);
        return Some(());
    }
    let ExpressionKind::Foreign { foreign: Foreign::Operator(Operator::StringAppend), arguments } =
        &expression.kind
    else {
        return None;
    };
    owned_appends_of(carried, &arguments[0], owned)?;
    owned.push(&arguments[0]);
    Some(())
}

fn results<'e>(
    carried: Carried<'_>,
    expression: &'e Expression,
    owned: &mut Vec<&'e Expression>,
) -> Option<()> {
    if let Some(branches) = branches(expression) {
        for branch in branches {
            results(carried, branch, owned)?;
        }
        return Some(());
    }
    match &expression.kind {
        _ if matches!(carried.place, Place::Whole) => carried_value(carried, expression, owned),
        ExpressionKind::Local(id) if *id == carried.accumulator => Some(()),
        ExpressionKind::Construct { constructor, arguments, .. } => match *carried.place {
            Place::Constructor { constructor: carrying, index, .. } if *constructor == carrying => {
                carried_value(carried, &arguments[index], owned)
            }
            Place::Constructor { .. } => Some(()),
            _ => None,
        },
        ExpressionKind::Record(fields) => {
            let Place::Field(field, _) = carried.place else { return None };
            let (_, value) = fields.iter().find(|(label, _)| label == field)?;
            carried_value(carried, value, owned)
        }
        ExpressionKind::Update { record, updates } if is_accumulator(carried, record) => {
            let Place::Field(field, _) = carried.place else { return None };
            let updated = updates.iter().find_map(|update| match update {
                RecordUpdate::Leaf { label, value } if label == field => Some(value),
                _ => None,
            });
            match updated {
                Some(value) => carried_value(carried, value, owned),
                None => Some(()),
            }
        }
        _ => None,
    }
}

fn carried_value<'e>(
    carried: Carried<'_>,
    value: &'e Expression,
    owned: &mut Vec<&'e Expression>,
) -> Option<()> {
    if let Some(branches) = branches(value) {
        for branch in branches {
            carried_value(carried, branch, owned)?;
        }
        return Some(());
    }
    if is_carried(carried, value) || matches!(value.kind, ExpressionKind::Array(_)) {
        return Some(());
    }
    owned_appends_of(carried, value, owned)
}

fn reads(carried: Carried<'_>, expression: &Expression) -> usize {
    match &expression.kind {
        _ if is_carried(carried, expression) => 1,
        ExpressionKind::EffectBind { action, body, .. } if carried.performed => {
            reads(carried, action) + reads(carried, body)
        }
        ExpressionKind::EffectPure(value) if carried.performed => reads(carried, value),
        ExpressionKind::Let { bindings, body } => {
            let bound: usize = bindings
                .iter()
                .filter(|binding| !binds_alias(carried, binding))
                .map(|binding| reads(carried, &binding.value))
                .sum();
            bound + reads(carried, body)
        }
        ExpressionKind::Local(id) if *id == carried.accumulator => 1,
        ExpressionKind::Access { record, .. } if is_accumulator(carried, record) => 0,
        ExpressionKind::Foreign { foreign, arguments }
            if let Some(position) = write_position(carried, foreign)
                && is_carried(carried, &arguments[position]) =>
        {
            let others: usize = arguments
                .iter()
                .enumerate()
                .filter(|(index, _)| *index != position)
                .map(|(_, argument)| reads_before_write(carried, argument))
                .sum();
            1 + others
        }
        ExpressionKind::Update { record, updates }
            if is_accumulator(carried, record) && overwrites(carried, updates) =>
        {
            updates.iter().map(|update| update_reads(carried, update)).sum()
        }
        ExpressionKind::Lambda { body, .. } => {
            if reads(carried, body) > 0 {
                SHARED
            } else {
                0
            }
        }
        ExpressionKind::Closure { .. }
        | ExpressionKind::EffectPure(_)
        | ExpressionKind::EffectBind { .. }
        | ExpressionKind::EffectEach { .. } => {
            let mut total = 0;
            for_each_child(expression, &mut |child| total += reads(carried, child));
            if total > 0 { SHARED } else { 0 }
        }
        ExpressionKind::If { condition, then, otherwise } => {
            reads_before_write(carried, condition)
                + reads(carried, then).max(reads(carried, otherwise))
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            // Matching a constructor on the accumulator reads the carried field only through
            // the aliases the patterns bind.
            let destructured = |scrutinee: &Expression| {
                matches!(carried.place, Place::Constructor { .. })
                    && is_accumulator(carried, scrutinee)
            };
            let scrutinised: usize = scrutinees
                .iter()
                .filter(|scrutinee| !destructured(scrutinee))
                .map(|scrutinee| reads_before_write(carried, scrutinee))
                .sum();
            let branches = alternatives
                .iter()
                .map(|alternative| guarded_reads(carried, &alternative.body))
                .max()
                .unwrap_or(0);
            scrutinised + branches
        }
        _ => {
            let mut total = 0;
            for_each_child(expression, &mut |child| total += reads(carried, child));
            total
        }
    }
}

fn spine_reads(carried: Carried<'_>, expression: &Expression, first: bool) -> usize {
    if !borrows_carried(carried, expression) {
        return reads(carried, expression);
    }
    let leading = |expression: &Expression, first: bool| match first {
        true => reads_before_write(carried, expression),
        false => reads(carried, expression),
    };
    match &expression.kind {
        ExpressionKind::Let { bindings, body } => {
            let mut total = 0;
            for binding in bindings.iter().filter(|binding| !binds_alias(carried, binding)) {
                total += leading(&binding.value, first && total == 0);
            }
            total + spine_reads(carried, body, first && total == 0)
        }
        ExpressionKind::If { condition, then, otherwise } => {
            let tested = leading(condition, first);
            let first = first && tested == 0;
            tested + spine_reads(carried, then, first).max(spine_reads(carried, otherwise, first))
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            let destructured = |scrutinee: &Expression| {
                matches!(carried.place, Place::Constructor { .. })
                    && is_accumulator(carried, scrutinee)
            };
            let mut scrutinised = 0;
            for scrutinee in scrutinees.iter().filter(|scrutinee| !destructured(scrutinee)) {
                scrutinised += leading(scrutinee, first && scrutinised == 0);
            }
            let first = first && scrutinised == 0;
            let branches = alternatives
                .iter()
                .map(|alternative| spine_guarded_reads(carried, &alternative.body, first))
                .max()
                .unwrap_or(0);
            scrutinised + branches
        }
        _ => reads(carried, expression),
    }
}

fn spine_guarded_reads(carried: Carried<'_>, guarded: &Guarded, first: bool) -> usize {
    let branches = match guarded {
        Guarded::Unconditional(body) => return spine_reads(carried, body, first),
        Guarded::Guards(branches) => branches,
    };
    let mut tested = 0;
    let mut most = 0;
    for branch in branches {
        for guard in &branch.guards {
            let condition = match guard {
                Guard::Boolean(condition) => condition,
                Guard::Pattern { value, .. } => value,
            };
            tested += match first && tested == 0 {
                true => reads_before_write(carried, condition),
                false => reads(carried, condition),
            };
        }
        most = most.max(tested + spine_reads(carried, &branch.body, first && tested == 0));
    }
    most.max(tested)
}

fn reads_before_write(carried: Carried<'_>, expression: &Expression) -> usize {
    if !borrows_carried(carried, expression) {
        return reads(carried, expression);
    }
    match &expression.kind {
        ExpressionKind::Let { bindings, body } => {
            let bound: usize = bindings
                .iter()
                .filter(|binding| !binds_alias(carried, binding))
                .map(|binding| reads_before_write(carried, &binding.value))
                .sum();
            bound + reads_before_write(carried, body)
        }
        ExpressionKind::Foreign { foreign, arguments } if is_borrowing(foreign) => arguments
            .iter()
            .filter(|argument| !is_carried(carried, argument))
            .map(|argument| reads_before_write(carried, argument))
            .sum(),
        ExpressionKind::Lambda { .. }
        | ExpressionKind::Closure { .. }
        | ExpressionKind::EffectPure(_)
        | ExpressionKind::EffectBind { .. }
        | ExpressionKind::EffectEach { .. } => reads(carried, expression),
        ExpressionKind::If { condition, then, otherwise } => {
            let branches =
                reads_before_write(carried, then).max(reads_before_write(carried, otherwise));
            reads_before_write(carried, condition) + branches
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            let scrutinised: usize =
                scrutinees.iter().map(|scrutinee| reads_before_write(carried, scrutinee)).sum();
            let branches = alternatives
                .iter()
                .map(|alternative| match &alternative.body {
                    Guarded::Unconditional(body) => reads_before_write(carried, body),
                    guarded => guarded_reads(carried, guarded),
                })
                .max()
                .unwrap_or(0);
            scrutinised + branches
        }
        _ => {
            let mut total = 0;
            for_each_child(expression, &mut |child| total += reads_before_write(carried, child));
            total
        }
    }
}

fn borrows_carried(carried: Carried<'_>, expression: &Expression) -> bool {
    let mut borrows = false;
    crate::monomorphic::traversal::visit(expression, &mut |expression| {
        if let ExpressionKind::Foreign { foreign, arguments } = &expression.kind
            && is_borrowing(foreign)
            && arguments.iter().any(|argument| is_carried(carried, argument))
        {
            borrows = true;
        }
    });
    borrows
}

fn overwrites(carried: Carried<'_>, updates: &[RecordUpdate]) -> bool {
    let Place::Field(field, _) = carried.place else { return false };
    updates
        .iter()
        .any(|update| matches!(update, RecordUpdate::Leaf { label, .. } if label == field))
}

fn update_reads(carried: Carried<'_>, update: &RecordUpdate) -> usize {
    match update {
        RecordUpdate::Leaf { value, .. } => reads(carried, value),
        RecordUpdate::Branch { updates, .. } => {
            updates.iter().map(|update| update_reads(carried, update)).sum()
        }
    }
}

fn guarded_reads(carried: Carried<'_>, guarded: &Guarded) -> usize {
    match guarded {
        Guarded::Unconditional(body) => reads(carried, body),
        Guarded::Guards(branches) => {
            let mut tested = 0;
            let mut most = 0;
            for branch in branches {
                for guard in &branch.guards {
                    tested += match guard {
                        Guard::Boolean(condition) => reads(carried, condition),
                        Guard::Pattern { value, .. } => reads(carried, value),
                    };
                }
                most = most.max(tested + reads(carried, &branch.body));
            }
            most.max(tested)
        }
    }
}

fn binds_alias(carried: Carried<'_>, binding: &Binding) -> bool {
    carried.aliases.contains(&binding.local.id) && is_carried(carried, &binding.value)
}

fn branches(expression: &Expression) -> Option<Vec<&Expression>> {
    match &expression.kind {
        ExpressionKind::Let { body, .. } => Some(vec![body]),
        ExpressionKind::If { then, otherwise, .. } => Some(vec![then, otherwise]),
        ExpressionKind::Case { alternatives, .. } => Some(alternative_bodies(alternatives)),
        ExpressionKind::Fail(_) => Some(vec![]),
        _ => None,
    }
}

fn alternative_bodies(alternatives: &[Alternative]) -> Vec<&Expression> {
    let mut bodies = vec![];
    for alternative in alternatives {
        match &alternative.body {
            Guarded::Unconditional(body) => bodies.push(body),
            Guarded::Guards(branches) => bodies.extend(branches.iter().map(|branch| &branch.body)),
        }
    }
    bodies
}
