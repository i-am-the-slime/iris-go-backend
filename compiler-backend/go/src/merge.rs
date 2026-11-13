//! Merges functions that are the same up to the names of their locals.
//! Specialization at types that share one representation, and lifting a local
//! function out of every copy an inlining made of its parent, both leave many
//! such functions behind; each copy would otherwise be compiled again by Go.

use std::collections::BTreeSet;
use std::hash::{Hash, Hasher};

use rustc_hash::{FxHashMap, FxHasher};

use crate::mono::{
    Expression, ExpressionKind, Function, FunctionId, Guard, Guarded, Local, LocalId, Pattern,
    PatternKind, Program,
};
use crate::monotype::MonotypeId;
use crate::simplify::{for_each_child_mut, prune_unreachable, visit};

/// Calls to a function are redirected to the first function with the same
/// shape, until no two functions share one; merging two functions can make
/// their callers the same in turn, so the callers of merged functions are
/// compared again. Constants are never merged, because each top-level value is
/// its own value (two `Ref`s created alike stay distinct), and neither is the
/// entry point.
pub fn merge_identical_functions(program: Program) -> Program {
    let Program { mut functions, entry } = program;
    let mut callers = callers(&functions);
    let mut shapes: Vec<Option<HashedShape>> = functions
        .iter()
        .enumerate()
        .map(|(index, function)| {
            let id = FunctionId(index as u32);
            let mergeable = id != entry && !function.parameters.is_empty();
            mergeable.then(|| HashedShape::of(function, id))
        })
        .collect();
    loop {
        let redirections = redirections(&shapes);
        if redirections.is_empty() {
            break;
        }
        let mut changed = BTreeSet::new();
        for (&merged, &representative) in &redirections {
            shapes[merged.0 as usize] = None;
            let moved = std::mem::take(&mut callers[merged.0 as usize]);
            changed.extend(moved.iter().copied());
            callers[representative.0 as usize].extend(moved);
        }
        for caller in changed {
            let function = &mut functions[caller.0 as usize];
            redirect(&mut function.body, &redirections);
            if shapes[caller.0 as usize].is_some() {
                shapes[caller.0 as usize] = Some(HashedShape::of(function, caller));
            }
        }
    }
    prune_unreachable(functions, entry).0
}

/// Each function whose shape an earlier function has, mapped to the first such.
fn redirections(shapes: &[Option<HashedShape>]) -> FxHashMap<FunctionId, FunctionId> {
    let mut representatives: FxHashMap<u64, Vec<usize>> = FxHashMap::default();
    let mut redirections = FxHashMap::default();
    for (index, shape) in shapes.iter().enumerate() {
        let Some(shape) = shape else { continue };
        let candidates = representatives.entry(shape.hash).or_default();
        let same = candidates.iter().find(|&&candidate| {
            shapes[candidate].as_ref().is_some_and(|candidate| candidate.shape == shape.shape)
        });
        match same {
            Some(&representative) => {
                redirections.insert(FunctionId(index as u32), FunctionId(representative as u32));
            }
            None => candidates.push(index),
        }
    }
    redirections
}

fn callers(functions: &[Function]) -> Vec<Vec<FunctionId>> {
    let mut callers = vec![vec![]; functions.len()];
    for (index, function) in functions.iter().enumerate() {
        let caller = FunctionId(index as u32);
        visit(&function.body, &mut |expression| {
            if let ExpressionKind::Function(callee) = expression.kind {
                let callers = &mut callers[callee.0 as usize];
                if callers.last() != Some(&caller) {
                    callers.push(caller);
                }
            }
        });
    }
    callers
}

struct HashedShape {
    hash: u64,
    shape: Shape,
}

impl HashedShape {
    fn of(function: &Function, id: FunctionId) -> HashedShape {
        let shape = shape(function, id);
        let mut hasher = FxHasher::default();
        shape.hash(&mut hasher);
        HashedShape { hash: hasher.finish(), shape }
    }
}

#[derive(PartialEq, Eq, Hash)]
struct Shape {
    parameters: Vec<Local>,
    result: MonotypeId,
    body: Expression,
}

/// The function with its locals numbered in order of appearance and their
/// names dropped, and calls to itself made anonymous, so that two functions
/// have one shape exactly when they differ only in those.
fn shape(function: &Function, id: FunctionId) -> Shape {
    let mut numbering = FxHashMap::default();
    let mut parameters = function.parameters.clone();
    for parameter in &mut parameters {
        canonical_local(parameter, &mut numbering);
    }
    let mut body = function.body.clone();
    canonical_expression(&mut body, id, &mut numbering);
    Shape { parameters, result: function.result, body }
}

fn canonical_id(id: &mut LocalId, numbering: &mut FxHashMap<LocalId, LocalId>) {
    let next = LocalId(numbering.len() as u32);
    *id = *numbering.entry(*id).or_insert(next);
}

fn canonical_local(local: &mut Local, numbering: &mut FxHashMap<LocalId, LocalId>) {
    canonical_id(&mut local.id, numbering);
    local.name = Default::default();
}

fn canonical_expression(
    expression: &mut Expression,
    itself: FunctionId,
    numbering: &mut FxHashMap<LocalId, LocalId>,
) {
    match &mut expression.kind {
        ExpressionKind::Local(id) => canonical_id(id, numbering),
        ExpressionKind::Function(id) if *id == itself => *id = FunctionId(u32::MAX),
        ExpressionKind::Lambda { parameters, .. } => {
            for parameter in parameters {
                canonical_local(parameter, numbering);
            }
        }
        ExpressionKind::Let { bindings, .. } => {
            for binding in bindings {
                canonical_local(&mut binding.local, numbering);
            }
        }
        ExpressionKind::EffectBind { local, .. }
        | ExpressionKind::EffectEach { element: local, .. } => {
            canonical_local(local, numbering);
        }
        ExpressionKind::Case { alternatives, .. } => {
            for alternative in alternatives {
                for pattern in &mut alternative.patterns {
                    canonical_pattern(pattern, numbering);
                }
                let Guarded::Guards(branches) = &mut alternative.body else { continue };
                for guard in branches.iter_mut().flat_map(|branch| &mut branch.guards) {
                    if let Guard::Pattern { pattern, .. } = guard {
                        canonical_pattern(pattern, numbering);
                    }
                }
            }
        }
        _ => {}
    }
    for_each_child_mut(expression, &mut |child| canonical_expression(child, itself, numbering));
}

fn canonical_pattern(pattern: &mut Pattern, numbering: &mut FxHashMap<LocalId, LocalId>) {
    match &mut pattern.kind {
        PatternKind::Wildcard | PatternKind::Literal(_) => {}
        PatternKind::Variable(local) => canonical_local(local, numbering),
        PatternKind::Named { local, pattern } => {
            canonical_local(local, numbering);
            canonical_pattern(pattern, numbering);
        }
        PatternKind::Array(elements) => {
            elements.iter_mut().for_each(|element| canonical_pattern(element, numbering))
        }
        PatternKind::Record(fields) => {
            fields.iter_mut().for_each(|(_, field)| canonical_pattern(field, numbering))
        }
        PatternKind::Constructor { arguments, .. } => {
            arguments.iter_mut().for_each(|argument| canonical_pattern(argument, numbering))
        }
    }
}

fn redirect(expression: &mut Expression, redirections: &FxHashMap<FunctionId, FunctionId>) {
    if let ExpressionKind::Function(id) = &mut expression.kind {
        if let Some(&target) = redirections.get(id) {
            *id = target;
        }
        return;
    }
    for_each_child_mut(expression, &mut |child| redirect(child, redirections));
}
