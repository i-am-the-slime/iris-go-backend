use rustc_hash::FxHashMap;

use super::{
    Alternative, Expression, ExpressionKind, Function, FunctionId, Guard, Guarded, Local, Program,
    RecordUpdate,
};

/// The guards and bodies of a case's alternatives.
pub(crate) fn for_each_alternative_child<'e>(
    alternatives: &'e [Alternative],
    visitor: &mut impl FnMut(&'e Expression),
) {
    for alternative in alternatives {
        for_each_guarded_child(&alternative.body, visitor);
    }
}

/// The guards and bodies of one alternative's right-hand side.
pub(crate) fn for_each_guarded_child<'e>(
    guarded: &'e Guarded,
    visitor: &mut impl FnMut(&'e Expression),
) {
    match guarded {
        Guarded::Unconditional(body) => visitor(body),
        Guarded::Guards(branches) => {
            for branch in branches {
                for guard in &branch.guards {
                    match guard {
                        Guard::Boolean(condition) => visitor(condition),
                        Guard::Pattern { value, .. } => visitor(value),
                    }
                }
                visitor(&branch.body);
            }
        }
    }
}

pub fn visit(expression: &Expression, visitor: &mut impl FnMut(&Expression)) {
    visitor(expression);
    for_each_child(expression, &mut |child| visit(child, visitor));
}

pub fn for_each_child<'e>(expression: &'e Expression, visitor: &mut impl FnMut(&'e Expression)) {
    match &expression.kind {
        ExpressionKind::Literal(_)
        | ExpressionKind::Unit
        | ExpressionKind::Local(_)
        | ExpressionKind::Function(_)
        | ExpressionKind::Fail(_) => {}
        ExpressionKind::Array(elements) => elements.iter().for_each(visitor),
        ExpressionKind::Record(fields) => fields.iter().for_each(|(_, value)| visitor(value)),
        ExpressionKind::Access { record, .. } => visitor(record),
        ExpressionKind::Update { record, updates } => {
            visitor(record);
            for_each_update(updates, visitor);
        }
        ExpressionKind::Construct { arguments, .. }
        | ExpressionKind::Foreign { arguments, .. }
        | ExpressionKind::Closure { captures: arguments, .. } => arguments.iter().for_each(visitor),
        ExpressionKind::Reuse { cell, arguments, .. } => {
            arguments.iter().for_each(&mut *visitor);
            visitor(cell);
        }
        ExpressionKind::Apply { function, arguments } => {
            visitor(function);
            arguments.iter().for_each(visitor);
        }
        ExpressionKind::Lambda { body, .. } => visitor(body),
        ExpressionKind::Let { bindings, body } => {
            bindings.iter().for_each(|binding| visitor(&binding.value));
            visitor(body);
        }
        ExpressionKind::If { condition, then, otherwise } => {
            visitor(condition);
            visitor(then);
            visitor(otherwise);
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees.iter().for_each(&mut *visitor);
            for_each_alternative_child(alternatives, visitor);
        }
        ExpressionKind::EffectPure(value) | ExpressionKind::Coerce(value) => visitor(value),
        ExpressionKind::EffectBind { action: first, body: second, .. }
        | ExpressionKind::EffectEach { array: first, body: second, .. } => {
            visitor(first);
            visitor(second);
        }
    }
}

fn for_each_update<'e>(updates: &'e [RecordUpdate], visitor: &mut impl FnMut(&'e Expression)) {
    for update in updates {
        match update {
            RecordUpdate::Leaf { value, .. } => visitor(value),
            RecordUpdate::Branch { updates, .. } => for_each_update(updates, visitor),
        }
    }
}

pub fn for_each_child_mut(expression: &mut Expression, visitor: &mut impl FnMut(&mut Expression)) {
    match &mut expression.kind {
        ExpressionKind::Literal(_)
        | ExpressionKind::Unit
        | ExpressionKind::Local(_)
        | ExpressionKind::Function(_)
        | ExpressionKind::Fail(_) => {}
        ExpressionKind::Array(elements) => elements.iter_mut().for_each(visitor),
        ExpressionKind::Record(fields) => fields.iter_mut().for_each(|(_, value)| visitor(value)),
        ExpressionKind::Access { record, .. } => visitor(record),
        ExpressionKind::Update { record, updates } => {
            visitor(record);
            for_each_update_mut(updates, visitor);
        }
        ExpressionKind::Construct { arguments, .. }
        | ExpressionKind::Foreign { arguments, .. }
        | ExpressionKind::Closure { captures: arguments, .. } => {
            arguments.iter_mut().for_each(visitor)
        }
        ExpressionKind::Reuse { cell, arguments, .. } => {
            arguments.iter_mut().for_each(&mut *visitor);
            visitor(cell);
        }
        ExpressionKind::Apply { function, arguments } => {
            visitor(function);
            arguments.iter_mut().for_each(visitor);
        }
        ExpressionKind::Lambda { body, .. } => visitor(body),
        ExpressionKind::Let { bindings, body } => {
            bindings.iter_mut().for_each(|binding| visitor(&mut binding.value));
            visitor(body);
        }
        ExpressionKind::If { condition, then, otherwise } => {
            visitor(condition);
            visitor(then);
            visitor(otherwise);
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees.iter_mut().for_each(&mut *visitor);
            for alternative in alternatives {
                match &mut alternative.body {
                    Guarded::Unconditional(body) => visitor(body),
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            branch.guards.iter_mut().for_each(|guard| visitor(guard.value_mut()));
                            visitor(&mut branch.body);
                        }
                    }
                }
            }
        }
        ExpressionKind::EffectPure(value) | ExpressionKind::Coerce(value) => visitor(value),
        ExpressionKind::EffectBind { action: first, body: second, .. }
        | ExpressionKind::EffectEach { array: first, body: second, .. } => {
            visitor(first);
            visitor(second);
        }
    }
}

/// Every local that `expression` binds, to rename them.
pub(crate) fn for_each_binder_mut(expression: &mut Expression, visit: &mut impl FnMut(&mut Local)) {
    match &mut expression.kind {
        ExpressionKind::Lambda { parameters, .. } => parameters.iter_mut().for_each(&mut *visit),
        ExpressionKind::Let { bindings, .. } => {
            bindings.iter_mut().for_each(|binding| visit(&mut binding.local))
        }
        ExpressionKind::EffectBind { local, .. }
        | ExpressionKind::EffectEach { element: local, .. } => visit(local),
        ExpressionKind::Case { alternatives, .. } => {
            for alternative in alternatives {
                for pattern in &mut alternative.patterns {
                    pattern.for_each_local_mut(visit);
                }
                if let Guarded::Guards(branches) = &mut alternative.body {
                    for guard in branches.iter_mut().flat_map(|branch| &mut branch.guards) {
                        if let Guard::Pattern { pattern, .. } = guard {
                            pattern.for_each_local_mut(visit);
                        }
                    }
                }
            }
        }
        _ => {}
    }
    for_each_child_mut(expression, &mut |child| for_each_binder_mut(child, visit));
}

fn for_each_update_mut(updates: &mut [RecordUpdate], visitor: &mut impl FnMut(&mut Expression)) {
    for update in updates {
        match update {
            RecordUpdate::Leaf { value, .. } => visitor(value),
            RecordUpdate::Branch { updates, .. } => for_each_update_mut(updates, visitor),
        }
    }
}

/// The functions the expression refers to, in order of id.
pub(crate) fn function_references(expression: &Expression) -> Vec<FunctionId> {
    let mut references = vec![];
    visit(expression, &mut |node| {
        if let ExpressionKind::Function(id) = node.kind {
            references.push(id);
        }
    });
    references.sort_unstable();
    references.dedup();
    references
}

/// The functions each function refers to, as indices.
pub(crate) fn reference_graph(functions: &[Function]) -> Vec<Vec<usize>> {
    let indices = |function: &Function| {
        function_references(&function.body).iter().map(|id| id.0 as usize).collect()
    };
    functions.iter().map(indices).collect()
}

pub(crate) fn prune_unreachable(
    functions: Vec<Function>,
    entry: FunctionId,
) -> (Program, FxHashMap<FunctionId, FunctionId>) {
    let mut reachable = vec![false; functions.len()];
    let mut pending = vec![entry];
    while let Some(id) = pending.pop() {
        if std::mem::replace(&mut reachable[id.0 as usize], true) {
            continue;
        }
        pending.extend(function_references(&functions[id.0 as usize].body));
    }
    let mut renumbering = FxHashMap::default();
    let mut kept = vec![];
    for (index, function) in functions.into_iter().enumerate() {
        if reachable[index] {
            renumbering.insert(FunctionId(index as u32), FunctionId(kept.len() as u32));
            kept.push(function);
        }
    }
    for function in &mut kept {
        renumber(&mut function.body, &renumbering);
    }
    let entry = renumbering[&entry];
    (Program { functions: kept, entry }, renumbering)
}

fn renumber(expression: &mut Expression, renumbering: &FxHashMap<FunctionId, FunctionId>) {
    if let ExpressionKind::Function(id) = &mut expression.kind {
        *id = renumbering[id];
        return;
    }
    for_each_child_mut(expression, &mut |child| renumber(child, renumbering));
}
