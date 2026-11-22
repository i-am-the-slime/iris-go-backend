//! Merges functions that are the same up to the names of their locals.
//! Specialization at types that share one representation, and lifting a local
//! function out of every copy an inlining made of its parent, both leave many
//! such functions behind; each copy would otherwise be compiled again by Go.

use std::collections::BTreeSet;
use std::hash::{Hash, Hasher};

use files::FileId;
use rustc_hash::{FxHashMap, FxHasher};

use crate::modules::Modules;
use crate::monomorphic::traversal::{for_each_child_mut, prune_unreachable, visit};
use crate::monomorphic::{
    Expression, ExpressionKind, Function, FunctionId, Guard, Guarded, Local, LocalId, Pattern,
    PatternKind, Program,
};
use crate::monotype::{MonotypeId, Monotypes};

/// Calls to a function are redirected to the first function with the same
/// shape, until no two functions share one; merging two functions can make
/// their callers the same in turn, so the callers of merged functions are
/// compared again. Constants are never merged, because each top-level value is
/// its own value (two `Ref`s created alike stay distinct), and neither is the
/// entry point.
pub fn merge_identical_functions(
    program: Program,
    modules: &Modules,
    monotypes: &mut Monotypes,
) -> Program {
    let Program { mut functions, entry } = program;
    let collapsed: FxHashMap<MonotypeId, MonotypeId> =
        monotypes.ids().map(|monotype| (monotype, monotypes.without_causes(monotype))).collect();
    let mut callers = callers(&functions);
    // The origins of the functions each function stands for.
    let mut origins: Vec<Vec<Option<FileId>>> =
        functions.iter().map(|function| vec![function.origin]).collect();
    let mut shapes: Vec<Option<HashedShape>> = functions
        .iter()
        .enumerate()
        .map(|(index, function)| {
            let id = FunctionId(index as u32);
            let mergeable = id != entry && !function.parameters.is_empty();
            mergeable.then(|| HashedShape::of(function, id, &collapsed))
        })
        .collect();
    loop {
        let redirections = redirections(&shapes);
        if redirections.is_empty() {
            break;
        }
        let mut changed = BTreeSet::new();
        for (&merged, &representative) in &redirections {
            let merged_origins = std::mem::take(&mut origins[merged.0 as usize]);
            origins[representative.0 as usize].extend(merged_origins);
            shapes[merged.0 as usize] = None;
            let moved = std::mem::take(&mut callers[merged.0 as usize]);
            changed.extend(moved.iter().copied());
            callers[representative.0 as usize].extend(moved);
        }
        for caller in changed {
            let function = &mut functions[caller.0 as usize];
            redirect(&mut function.body, &redirections);
            if shapes[caller.0 as usize].is_some() {
                shapes[caller.0 as usize] = Some(HashedShape::of(function, caller, &collapsed));
            }
        }
    }
    for (function, origins) in functions.iter_mut().zip(origins) {
        if origins.len() > 1 {
            function.origin = common_origin(&origins, modules);
        }
    }
    prune_unreachable(functions, entry).0
}

/// The origin of a function that stands for functions of these origins.
fn common_origin(origins: &[Option<FileId>], modules: &Modules) -> Option<FileId> {
    let homes: Vec<Option<_>> =
        origins.iter().map(|origin| origin.and_then(|file| modules.index(file))).collect();
    modules.common_home(&homes).map(|home| modules.file(home))
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
    fn of(
        function: &Function,
        id: FunctionId,
        collapsed: &FxHashMap<MonotypeId, MonotypeId>,
    ) -> HashedShape {
        let shape = shape(function, id, collapsed);
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
fn shape(
    function: &Function,
    id: FunctionId,
    collapsed: &FxHashMap<MonotypeId, MonotypeId>,
) -> Shape {
    let mut canonical = Canonical { numbering: FxHashMap::default(), collapsed };
    let mut parameters = function.parameters.clone();
    for parameter in &mut parameters {
        canonical.local(parameter);
    }
    let mut body = function.body.clone();
    canonical.expression(&mut body, id);
    Shape { parameters, result: collapsed[&function.result], body }
}

struct Canonical<'c> {
    numbering: FxHashMap<LocalId, LocalId>,
    collapsed: &'c FxHashMap<MonotypeId, MonotypeId>,
}

impl Canonical<'_> {
    fn id(&mut self, id: &mut LocalId) {
        let next = LocalId(self.numbering.len() as u32);
        *id = *self.numbering.entry(*id).or_insert(next);
    }

    fn local(&mut self, local: &mut Local) {
        self.id(&mut local.id);
        local.name = Default::default();
        local.monotype = self.collapsed[&local.monotype];
    }

    fn expression(&mut self, expression: &mut Expression, itself: FunctionId) {
        expression.monotype = self.collapsed[&expression.monotype];
        match &mut expression.kind {
            ExpressionKind::Local(id) => self.id(id),
            ExpressionKind::Function(id) if *id == itself => *id = FunctionId(u32::MAX),
            ExpressionKind::Lambda { parameters, .. } => {
                for parameter in parameters {
                    self.local(parameter);
                }
            }
            ExpressionKind::Let { bindings, .. } => {
                for binding in bindings {
                    self.local(&mut binding.local);
                }
            }
            ExpressionKind::EffectBind { local, .. }
            | ExpressionKind::EffectEach { element: local, .. } => {
                self.local(local);
            }
            ExpressionKind::Case { alternatives, .. } => {
                for alternative in alternatives {
                    for pattern in &mut alternative.patterns {
                        self.pattern(pattern);
                    }
                    let Guarded::Guards(branches) = &mut alternative.body else { continue };
                    for guard in branches.iter_mut().flat_map(|branch| &mut branch.guards) {
                        if let Guard::Pattern { pattern, .. } = guard {
                            self.pattern(pattern);
                        }
                    }
                }
            }
            _ => {}
        }
        for_each_child_mut(expression, &mut |child| self.expression(child, itself));
    }

    fn pattern(&mut self, pattern: &mut Pattern) {
        pattern.monotype = self.collapsed[&pattern.monotype];
        match &mut pattern.kind {
            PatternKind::Wildcard | PatternKind::Literal(_) => {}
            PatternKind::Variable(local) => self.local(local),
            PatternKind::Named { local, pattern } => {
                self.local(local);
                self.pattern(pattern);
            }
            PatternKind::Array(patterns)
            | PatternKind::Constructor { arguments: patterns, .. }
            | PatternKind::Closure { captures: patterns, .. } => {
                patterns.iter_mut().for_each(|pattern| self.pattern(pattern))
            }
            PatternKind::Record(fields) => {
                fields.iter_mut().for_each(|(_, pattern)| self.pattern(pattern))
            }
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
