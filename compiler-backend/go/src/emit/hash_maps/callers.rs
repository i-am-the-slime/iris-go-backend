//! Variants of functions for the callers that hand them Go maps.
//!
//! A parameter is one node of its web for every caller, so a single caller that passes a tree, or
//! that shares the map it passes, makes the parameter a tree for all of them. Callers that pass
//! Go maps call a variant of the function instead: a copy whose parameters only those callers
//! reach, which may take Go maps and give them back. The variant is chosen by the
//! representation of every map the caller passes, so that each caller calls the copy made for
//! what it has, and a caller that passes trees keeps the function itself.
//!
//! The program is analysed again with its variants until no caller wants another, and a variant
//! that takes and gives what its function does is folded back into it. Nothing changes where no
//! variant takes or gives a Go map that its function does not.

use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use super::{CallSite, Decided, Hopes, MapShape, Natives, Node, analyse, analyse_hopefully};
use crate::maps::MapOperation;
use crate::monomorphic::traversal::for_each_child_mut;
use crate::monomorphic::{
    Expression, ExpressionKind, Function, FunctionId, Guard, Guarded, Local, LocalId, Program,
};
use crate::monotype::{MonotypeId, Monotypes};

/// What a variant's name adds to its function's name.
pub(in crate::emit) const HASHED: &str = "Hashed";

/// How often the program is analysed again for the variants its callers want.
const ROUNDS: usize = 6;

/// How many variants the program may gain.
const VARIANT_LIMIT: usize = 64;

/// The program's maps as decided, with the variants that some callers call.
pub(super) enum Specialised {
    Unchanged(Decided),
    Variants(Program, Decided),
}

/// The program with a variant of each function for each representation of the maps its callers
/// pass, as far as a variant takes or gives a Go map that its function does not.
pub(super) fn specialise(
    program: &Program,
    monotypes: &Monotypes,
    operations: &FxHashMap<FunctionId, MapOperation>,
    shapes: &FxHashMap<MonotypeId, MapShape>,
) -> Specialised {
    let (original, hopes) = analyse_hopefully(program, monotypes, operations, shapes);
    let wanted = Versions::new(program).wanted(program, &original, &hopes);
    if wanted.is_empty() {
        return Specialised::Unchanged(original);
    }
    let mut versions = Versions::new(program);
    let mut specialised = Program { functions: program.functions.clone(), entry: program.entry };
    let mut redirects = wanted;
    for _ in 0..ROUNDS {
        if redirects.is_empty() || versions.variants.len() >= VARIANT_LIMIT {
            break;
        }
        versions.redirect(&mut specialised, redirects);
        let (decided, hopes) = analyse_hopefully(&specialised, monotypes, operations, shapes);
        redirects = versions.wanted(&specialised, &decided, &hopes);
    }
    loop {
        let decided = analyse(&specialised, monotypes, operations, shapes);
        let folded = versions.alike(&specialised, &decided);
        if folded.is_empty() {
            if versions.variants.is_empty() {
                return Specialised::Unchanged(original);
            }
            return Specialised::Variants(specialised, decided);
        }
        versions.fold(&mut specialised, &folded);
    }
}

/// A call to send to another version of its function, by the call's address.
type Redirect = (*const Expression, Version);

/// A version of a function: the function itself, or the variant for the representation of the
/// maps its parameters are passed.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Version {
    Original(FunctionId),
    Variant(FunctionId, Natives),
}

/// The variants made so far, each with the function it copies.
struct Versions {
    originals: usize,
    variants: FxHashMap<(FunctionId, Natives), FunctionId>,
    bases: FxHashMap<FunctionId, FunctionId>,
    next_local: u32,
}

impl Versions {
    fn new(program: &Program) -> Versions {
        Versions {
            originals: program.functions.len(),
            variants: FxHashMap::default(),
            bases: FxHashMap::default(),
            next_local: crate::emit::reuse::first_unused_local(program),
        }
    }

    fn base(&self, id: FunctionId) -> FunctionId {
        self.bases.get(&id).copied().unwrap_or(id)
    }

    /// The calls that could pass Go maps where their callee takes trees, each with the version
    /// of the callee for what the call could pass: what it passes if no call's result were a
    /// tree but by its callee's doing, where the callee could take a Go map if no caller passed
    /// it a tree.
    fn wanted(&self, program: &Program, decided: &Decided, hopes: &Hopes) -> Vec<Redirect> {
        let real = |slots: &[Node]| decided.natives(slots);
        let results = |slots: &[Node]| hoped(decided, &hopes.results, slots);
        let calls = |slots: &[Node]| hoped(decided, &hopes.calls, slots);
        let mut wanted = vec![];
        for site in &decided.sites {
            let base = self.base(site.callee);
            let could_take: Natives = taken_by(program, decided, base, calls)
                .into_iter()
                .zip(taken_by(program, decided, site.callee, real))
                .map(|(could, takes)| could || takes)
                .collect();
            let wants: Natives = passed(program, decided, site, results)
                .into_iter()
                .zip(&could_take)
                .map(|(passes, &takes)| passes && takes)
                .collect();
            if wants == taken_by(program, decided, site.callee, real) {
                continue;
            }
            let version =
                if !wants.contains(&true) || taken_by(program, decided, base, real) == wants {
                    Version::Original(base)
                } else {
                    Version::Variant(base, wants)
                };
            if self.id(&version) != Some(site.callee) {
                wanted.push((site.call, version));
            }
        }
        wanted
    }

    fn id(&self, version: &Version) -> Option<FunctionId> {
        match version {
            Version::Original(id) => Some(*id),
            Version::Variant(base, natives) => {
                self.variants.get(&(*base, natives.clone())).copied()
            }
        }
    }

    /// Sends each call to its version, making the variants that do not exist yet as copies of
    /// their functions.
    fn redirect(&mut self, program: &mut Program, redirects: Vec<Redirect>) {
        let mut made = vec![];
        let mut targets: FxHashMap<*const Expression, FunctionId> = FxHashMap::default();
        for (call, version) in redirects {
            let id = match self.id(&version) {
                Some(id) => id,
                None => {
                    let Version::Variant(base, natives) = version else {
                        unreachable!("invariant violated: an original that is not one")
                    };
                    let id = FunctionId((program.functions.len() + made.len()) as u32);
                    self.variants.insert((base, natives), id);
                    self.bases.insert(id, base);
                    made.push(base);
                    id
                }
            };
            targets.insert(call, id);
        }
        for function in &mut program.functions {
            redirect_calls(&mut function.body, &targets);
        }
        for base in made {
            let variant = self.copy(program.function(base));
            program.functions.push(variant);
        }
    }

    /// A copy of a function, its locals renamed apart from the function's.
    fn copy(&mut self, function: &Function) -> Function {
        let mut copy = function.clone();
        copy.name = SmolStr::new(format!("{}{HASHED}", function.name));
        let mut renaming = FxHashMap::default();
        for parameter in &mut copy.parameters {
            rename_binder(parameter, &mut renaming, &mut self.next_local);
        }
        rename(&mut copy.body, &mut renaming, &mut self.next_local);
        copy
    }

    /// The variants that take and give the maps their functions do.
    fn alike(&self, program: &Program, decided: &Decided) -> Vec<FunctionId> {
        let mut alike: Vec<FunctionId> = self
            .bases
            .iter()
            .filter(|&(&variant, &base)| {
                let real = |slots: &[Node]| decided.natives(slots);
                taken_by(program, decided, variant, real) == taken_by(program, decided, base, real)
                    && given_by(decided, variant) == given_by(decided, base)
            })
            .map(|(&variant, _)| variant)
            .collect();
        alike.sort_unstable();
        alike
    }

    /// Folds the variants back into their functions: their calls call the functions, and they
    /// leave the program.
    fn fold(&mut self, program: &mut Program, folded: &[FunctionId]) {
        let mut renumbered: FxHashMap<FunctionId, FunctionId> =
            folded.iter().map(|&variant| (variant, self.base(variant))).collect();
        let mut functions = std::mem::take(&mut program.functions);
        let variants = functions.split_off(self.originals);
        for (offset, variant) in variants.into_iter().enumerate() {
            let id = FunctionId((self.originals + offset) as u32);
            if !folded.contains(&id) {
                renumbered.insert(id, FunctionId(functions.len() as u32));
                functions.push(variant);
            }
        }
        for function in &mut functions {
            renumber_calls(&mut function.body, &renumbered);
        }
        program.functions = functions;
        self.variants = std::mem::take(&mut self.variants)
            .into_iter()
            .filter(|(_, id)| !folded.contains(id))
            .map(|(key, id)| (key, renumbered[&id]))
            .collect();
        self.bases = std::mem::take(&mut self.bases)
            .into_iter()
            .filter(|(id, _)| !folded.contains(id))
            .map(|(id, base)| (renumbered[&id], base))
            .collect();
    }
}

/// The representation of the maps a call passes, slot by slot of the callee's parameters, as
/// `view` sees the program: an argument that does not hand its maps on passes trees.
fn passed(
    program: &Program,
    decided: &Decided,
    site: &CallSite,
    view: impl Fn(&[Node]) -> Natives,
) -> Natives {
    let parameters = &program.function(site.callee).parameters;
    let mut natives = vec![];
    for (parameter, argument) in parameters.iter().zip(&site.arguments) {
        let Some(slots) = decided.locals.get(&parameter.id) else { continue };
        match argument {
            Some(from) => natives.extend(view(from)),
            None => natives.extend(std::iter::repeat_n(false, slots.len())),
        }
    }
    natives
}

/// The representation of the maps a function's parameters take, slot by slot, as `view` sees
/// the program.
fn taken_by(
    program: &Program,
    decided: &Decided,
    id: FunctionId,
    view: impl Fn(&[Node]) -> Natives,
) -> Natives {
    let mut natives = vec![];
    for parameter in &program.function(id).parameters {
        if let Some(slots) = decided.locals.get(&parameter.id) {
            natives.extend(view(slots));
        }
    }
    natives
}

/// The representation of the slots where `tree` says which webs are trees.
fn hoped(decided: &Decided, tree: &[bool], slots: &[Node]) -> Natives {
    slots.iter().map(|&node| !tree[decided.root(node)]).collect()
}

/// The representation of the maps a function's result gives.
fn given_by(decided: &Decided, id: FunctionId) -> Natives {
    decided.results.get(&id).map(|slots| decided.natives(slots)).unwrap_or_default()
}

fn redirect_calls(expression: &mut Expression, targets: &FxHashMap<*const Expression, FunctionId>) {
    if let Some(&target) = targets.get(&std::ptr::from_ref(expression))
        && let ExpressionKind::Apply { function, .. } = &mut expression.kind
    {
        function.kind = ExpressionKind::Function(target);
    }
    for_each_child_mut(expression, &mut |child| redirect_calls(child, targets));
}

fn renumber_calls(expression: &mut Expression, renumbered: &FxHashMap<FunctionId, FunctionId>) {
    if let ExpressionKind::Function(id) = &mut expression.kind
        && let Some(&renumber) = renumbered.get(id)
    {
        *id = renumber;
    }
    for_each_child_mut(expression, &mut |child| renumber_calls(child, renumbered));
}

fn rename_binder(local: &mut Local, renaming: &mut FxHashMap<LocalId, LocalId>, next: &mut u32) {
    let fresh = LocalId(*next);
    *next += 1;
    renaming.insert(local.id, fresh);
    local.id = fresh;
}

/// Gives every local the expression binds a fresh identity, and every use of it that identity.
fn rename(expression: &mut Expression, renaming: &mut FxHashMap<LocalId, LocalId>, next: &mut u32) {
    match &mut expression.kind {
        ExpressionKind::Local(id) => {
            if let Some(&renamed) = renaming.get(id) {
                *id = renamed;
            }
            return;
        }
        ExpressionKind::Lambda { parameters, .. } => {
            for parameter in parameters {
                rename_binder(parameter, renaming, next);
            }
        }
        ExpressionKind::Let { bindings, .. } => {
            for binding in bindings {
                rename_binder(&mut binding.local, renaming, next);
            }
        }
        ExpressionKind::EffectBind { local, .. }
        | ExpressionKind::EffectEach { element: local, .. } => {
            rename_binder(local, renaming, next);
        }
        ExpressionKind::Case { alternatives, .. } => {
            for alternative in alternatives.iter_mut() {
                for pattern in &mut alternative.patterns {
                    pattern.for_each_local_mut(&mut |local| rename_binder(local, renaming, next));
                }
                if let Guarded::Guards(branches) = &mut alternative.body {
                    for guard in branches.iter_mut().flat_map(|branch| &mut branch.guards) {
                        if let Guard::Pattern { pattern, .. } = guard {
                            pattern.for_each_local_mut(&mut |local| {
                                rename_binder(local, renaming, next)
                            });
                        }
                    }
                }
            }
        }
        _ => {}
    }
    for_each_child_mut(expression, &mut |child| rename(child, renaming, next));
}
