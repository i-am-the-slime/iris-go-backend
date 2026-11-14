//! Merges Go declarations that read the same apart from their own names.
//!
//! The monomorphic merge compares functions by their monotypes, but distinct
//! monotypes can share one Go type: specializations that differ only in what
//! erasure or representation forgets come out as the same Go code under two
//! names, which Go then compiles twice. Here every reference to a duplicate is
//! redirected to the first declaration of its text, until no two declarations
//! share one; redirecting can make the callers of merged declarations the same
//! in turn, so their texts are compared again.

use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::syntax::{GoDeclaration, GoExpression, GoType, Name};

/// What a declaration's own name reads as when it is compared, so that a
/// recursive function matches its copies. No Go identifier contains it.
const ITSELF: &str = "\u{0}itself";

/// `on_merge(merged, representative)` hears of each merge, so that the
/// representative's package can be chosen to suit the users of both.
pub(super) fn merge_identical_declarations(
    declarations: Vec<GoDeclaration>,
    on_merge: &mut dyn FnMut(&str, &str),
) -> Vec<GoDeclaration> {
    let mut merging = Merging::new(declarations);
    let mut changed: Vec<usize> = merging.candidates.iter().copied().collect();
    while !changed.is_empty() {
        changed.sort_unstable();
        changed.retain(|index| merging.candidates.contains(index));
        let texts: Vec<String> = changed
            .par_iter()
            .map(|&index| {
                let declaration = merging.declarations[index].as_ref();
                comparable_text(
                    declaration.expect("invariant violated: changed declaration removed"),
                )
            })
            .collect();
        let mut merges = vec![];
        for (index, text) in changed.into_iter().zip(texts) {
            if let Some(representative) = merging.classify(index, text) {
                merges.push((index, representative));
            }
        }
        changed = merging.redirect(merges, on_merge);
    }
    merging.declarations.into_iter().flatten().collect()
}

struct Merging {
    declarations: Vec<Option<GoDeclaration>>,
    /// Declarations whose code is free to share: functions, and variables
    /// whose initializer only builds a value, so that no two values that
    /// differ in identity become one.
    candidates: FxHashSet<usize>,
    index_of: FxHashMap<String, usize>,
    /// The declarations that refer to each name.
    users: FxHashMap<String, FxHashSet<usize>>,
    text_of: FxHashMap<usize, String>,
    by_text: FxHashMap<String, usize>,
}

impl Merging {
    fn new(declarations: Vec<GoDeclaration>) -> Merging {
        let mut declarations: Vec<Option<GoDeclaration>> =
            declarations.into_iter().map(Some).collect();
        let mut candidates = FxHashSet::default();
        let mut index_of = FxHashMap::default();
        for (index, declaration) in declarations.iter().enumerate() {
            let Some(declaration) = declaration else { continue };
            let Some(name) = declaration.name() else { continue };
            index_of.insert(name.to_string(), index);
            let shareable = match declaration {
                GoDeclaration::Function { name, .. } => name != "main",
                GoDeclaration::Variable { value, .. } => builds_value(value),
                _ => false,
            };
            if shareable {
                candidates.insert(index);
            }
        }
        let references: Vec<Vec<String>> = declarations
            .par_iter_mut()
            .map(|declaration| {
                let Some(declaration) = declaration else { return vec![] };
                let binders = binders(declaration);
                let mut references = vec![];
                declaration.for_each_name_mut(&mut |name| {
                    if let Name::Reference(name) = name
                        && !binders.contains(name.as_str())
                        && index_of.contains_key(name.as_str())
                    {
                        references.push(name.clone());
                    }
                });
                references
            })
            .collect();
        let mut users: FxHashMap<String, FxHashSet<usize>> = FxHashMap::default();
        for (index, names) in references.into_iter().enumerate() {
            for name in names {
                users.entry(name).or_default().insert(index);
            }
        }
        Merging {
            declarations,
            candidates,
            index_of,
            users,
            text_of: FxHashMap::default(),
            by_text: FxHashMap::default(),
        }
    }

    /// Records a declaration's current text, and returns the declaration that
    /// already has it.
    fn classify(&mut self, index: usize, text: String) -> Option<usize> {
        if let Some(previous) = self.text_of.remove(&index)
            && self.by_text.get(&previous) == Some(&index)
        {
            self.by_text.remove(&previous);
        }
        if let Some(&representative) = self.by_text.get(&text)
            && representative != index
            && self.declarations[representative].is_some()
        {
            return Some(representative);
        }
        self.by_text.insert(text.clone(), index);
        self.text_of.insert(index, text);
        None
    }

    /// Removes each merged declaration and points its users at the
    /// representative; returns the users, whose texts have changed.
    fn redirect(
        &mut self,
        merges: Vec<(usize, usize)>,
        on_merge: &mut dyn FnMut(&str, &str),
    ) -> Vec<usize> {
        let mut changed = FxHashSet::default();
        for (merged, representative) in merges {
            let Some(declaration) = self.declarations[merged].take() else { continue };
            self.text_of.remove(&merged);
            let from = declaration.name().expect("invariant violated: merged unnamed").to_string();
            let to = self.declarations[representative]
                .as_ref()
                .and_then(GoDeclaration::name)
                .expect("invariant violated: representative removed")
                .to_string();
            on_merge(&from, &to);
            self.index_of.remove(&from);
            let users = self.users.remove(&from).unwrap_or_default();
            for &user in &users {
                let Some(declaration) = self.declarations[user].as_mut() else { continue };
                let binders = binders(declaration);
                if binders.contains(from.as_str()) {
                    continue;
                }
                declaration.for_each_name_mut(&mut |name| {
                    if let Name::Reference(name) = name
                        && *name == from
                    {
                        *name = to.clone();
                    }
                });
                changed.insert(user);
            }
            self.users.entry(to).or_default().extend(users);
        }
        changed.into_iter().filter(|&index| self.declarations[index].is_some()).collect()
    }
}

/// The declaration as Go reads it, with its locals numbered in order of
/// appearance and its own name, wherever it refers to itself, made anonymous.
/// Locals never shadow a declaration, so each name is one or the other.
fn comparable_text(declaration: &GoDeclaration) -> String {
    let mut declaration = declaration.clone();
    let own = declaration.name().expect("invariant violated: candidate unnamed").to_string();
    let mut locals: FxHashMap<String, String> = FxHashMap::default();
    let number = |name: &mut String, locals: &mut FxHashMap<String, String>| {
        if name == "_" {
            return;
        }
        let next = format!("\u{0}local{}", locals.len());
        *name = locals.entry(std::mem::take(name)).or_insert(next).clone();
    };
    declaration.for_each_name_mut(&mut |name| match name {
        Name::Binder(name) => number(name, &mut locals),
        Name::Reference(name) if locals.contains_key(name.as_str()) => number(name, &mut locals),
        Name::Reference(name) if *name == own => *name = ITSELF.to_string(),
        Name::Reference(_) => {}
    });
    match &mut declaration {
        GoDeclaration::Function { name, .. } | GoDeclaration::Variable { name, .. } => {
            *name = ITSELF.to_string();
        }
        _ => {}
    }
    declaration.render()
}

fn binders(declaration: &mut GoDeclaration) -> FxHashSet<String> {
    let mut binders = FxHashSet::default();
    declaration.for_each_name_mut(&mut |name| {
        if let Name::Binder(name) = name {
            binders.insert(name.clone());
        }
    });
    binders
}

/// Whether evaluating the expression only builds a value from closures,
/// literals and names, without calling anything or taking an address, so
/// that sharing it is not observable.
fn builds_value(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_)
        | GoExpression::Function { .. } => true,
        // A slice shares its elements, which reuse may update in place.
        GoExpression::Composite { type_: GoType::Slice(_), .. } => false,
        GoExpression::Composite { fields, .. } => {
            fields.iter().all(|(_, value)| builds_value(value))
        }
        _ => false,
    }
}
