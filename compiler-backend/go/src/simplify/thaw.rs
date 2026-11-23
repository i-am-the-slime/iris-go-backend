use super::short_circuit::mentions;
use crate::foreign::{
    ARRAY_REPLICATE, ARRAY_THAW, ARRAY_THAW_OWNED, Boundary, Foreign, Iteration, Operator,
};
use crate::monomorphic::traversal::{for_each_child, for_each_child_mut};
use crate::monomorphic::{Expression, ExpressionKind, Local, LocalId};
use crate::monotype::{Monotype, Monotypes};

#[derive(Default)]
struct Uses {
    thawed: usize,
    others: usize,
}

pub(super) fn thaw_fresh_arrays_in_place(expression: &mut Expression, monotypes: &Monotypes) {
    for_each_child_mut(expression, &mut |child| thaw_fresh_arrays_in_place(child, monotypes));
    let ExpressionKind::Let { bindings, body } = &mut expression.kind else { return };
    for position in 0..bindings.len() {
        if !is_fresh(&bindings[position].value) {
            continue;
        }
        let local = bindings[position].local.id;
        let later = &mut bindings[position + 1..];
        let mut uses = Uses::default();
        for binding in later.iter() {
            let repeated = runs_later(&binding.value, monotypes);
            count_uses(&binding.value, local, repeated, monotypes, &mut uses);
        }
        count_uses(body, local, false, monotypes, &mut uses);
        if uses.thawed != 1 || uses.others != 0 {
            continue;
        }
        for binding in later.iter_mut() {
            thaw_in_place(&mut binding.value, local);
        }
        thaw_in_place(body, local);
    }
}

fn is_fresh(value: &Expression) -> bool {
    matches!(&value.kind, ExpressionKind::Foreign { foreign, .. } if foreign.calls(ARRAY_REPLICATE))
}

fn count_uses(
    expression: &Expression,
    local: LocalId,
    repeated: bool,
    monotypes: &Monotypes,
    uses: &mut Uses,
) {
    let mut recurse = |child: &Expression, repeated: bool| {
        count_uses(child, local, repeated, monotypes, uses);
    };
    match &expression.kind {
        ExpressionKind::Local(id) if *id == local => uses.others += 1,
        ExpressionKind::Foreign { foreign, arguments } if is_thaw_of(foreign, arguments, local) => {
            match repeated {
                true => uses.others += 1,
                false => uses.thawed += 1,
            }
        }
        ExpressionKind::Foreign { foreign, arguments } => {
            match length_only_callback(foreign, arguments, local) {
                Some(Some(callback)) => recurse(callback, true),
                Some(None) => {}
                None if matches!(foreign, Foreign::RunEffect) => {
                    arguments.iter().for_each(|argument| recurse(argument, repeated));
                }
                None => arguments.iter().for_each(|argument| {
                    recurse(argument, repeated || runs_later(argument, monotypes));
                }),
            }
        }
        ExpressionKind::If { .. } | ExpressionKind::Case { .. } => {
            for_each_child(expression, &mut |child| recurse(child, repeated));
        }
        ExpressionKind::EffectBind { action, body, .. } => {
            recurse(action, repeated);
            recurse(body, repeated);
        }
        ExpressionKind::Let { bindings, body } => {
            for binding in bindings {
                recurse(&binding.value, repeated || runs_later(&binding.value, monotypes));
            }
            recurse(body, repeated);
        }
        ExpressionKind::EffectEach { array, element, body, .. } => {
            if !is_local(array, local) || mentions(body, element.id) {
                recurse(array, repeated);
            }
            recurse(body, true);
        }
        ExpressionKind::Lambda { body, .. } => recurse(body, true),
        _ => for_each_child(expression, &mut |child| {
            recurse(child, repeated || runs_later(child, monotypes));
        }),
    }
}

fn runs_later(value: &Expression, monotypes: &Monotypes) -> bool {
    matches!(monotypes.get(value.monotype), Monotype::Effect(_) | Monotype::Function(..))
}

fn is_thaw_of(foreign: &Foreign, arguments: &[Expression], local: LocalId) -> bool {
    let Foreign::Perform { function, .. } = foreign else { return false };
    let Foreign::Perform { function: thaw, .. } = ARRAY_THAW else { return false };
    *function == thaw && matches!(arguments, [array] if is_local(array, local))
}

fn length_only_callback<'e>(
    foreign: &Foreign,
    arguments: &'e [Expression],
    local: LocalId,
) -> Option<Option<&'e Expression>> {
    match (foreign, arguments) {
        (Foreign::Operator(Operator::ArrayLength), [array]) if is_local(array, local) => Some(None),
        (
            Foreign::Call { boundary: Boundary { iteration: Some(iteration), .. }, .. },
            [callback, array],
        ) if is_local(array, local) => {
            let (arity, element) = match iteration {
                Iteration::Map => (1, 0),
                Iteration::MapWithIndex => (2, 1),
                _ => return None,
            };
            let (parameters, body) = lambda_parameters(callback, arity)?;
            (!mentions(body, parameters[element].id)).then_some(Some(callback))
        }
        _ => None,
    }
}

fn lambda_parameters(callback: &Expression, arity: usize) -> Option<(Vec<&Local>, &Expression)> {
    let mut parameters = vec![];
    let mut body = callback;
    while parameters.len() < arity {
        let ExpressionKind::Lambda { parameters: more, body: inner } = &body.kind else {
            return None;
        };
        parameters.extend(more.iter());
        body = inner;
    }
    (parameters.len() == arity).then_some((parameters, body))
}

fn is_local(expression: &Expression, local: LocalId) -> bool {
    matches!(expression.kind, ExpressionKind::Local(id) if id == local)
}

fn thaw_in_place(expression: &mut Expression, local: LocalId) {
    if let ExpressionKind::Foreign { foreign, arguments } = &mut expression.kind
        && is_thaw_of(foreign, arguments, local)
    {
        *foreign = &ARRAY_THAW_OWNED;
        return;
    }
    for_each_child_mut(expression, &mut |child| thaw_in_place(child, local));
}
