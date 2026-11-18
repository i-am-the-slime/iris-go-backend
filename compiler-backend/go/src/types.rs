use std::cell::{Cell, OnceCell, RefCell};
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::sync::Arc;

use checking::TypeId;
use checking::core::{Depth, ForallBinderId, Name, RowField, RowType, Type};
use rustc_hash::{FxHashMap, FxHasher};

use crate::erasure::Erasure;

pub type Substitution = FxHashMap<Name, TypeId>;

/// Erased stand-ins are rigid variables numbered down from here, clear of the
/// scheme placeholders just below `u32::MAX`.
const ERASED_UNIQUE: u32 = u32::MAX - 4096;
/// The phantom stand-in, below every erased one.
const PHANTOM_UNIQUE: u32 = ERASED_UNIQUE - 1024;
const CONS_LIST_UNIQUE: u32 = PHANTOM_UNIQUE - 1;

pub struct TypeOperations<'q, Q> {
    queries: &'q Q,
    substituted: Substituted,
    erased: RefCell<FxHashMap<Erasure, TypeId>>,
    collapsed_causes: OnceCell<(Substitution, u64)>,
    without_causes: RefCell<FxHashMap<TypeId, TypeId>>,
    phantom: Cell<Option<TypeId>>,
    cons_list: Cell<Option<TypeId>>,
    placeholders: RefCell<Vec<TypeId>>,
}

/// The answers of `substitute`, by substitution and then by type. They hold for
/// every `TypeOperations` over the same queries, so a pass that starts over
/// keeps them.
#[derive(Clone, Default)]
pub struct Substituted(Rc<RefCell<FxHashMap<u64, SubstitutionAnswers>>>);

#[derive(Default)]
struct SubstitutionAnswers {
    entries: Vec<(Name, TypeId)>,
    by_type: FxHashMap<TypeId, TypeId>,
}

impl Substituted {
    fn answer(
        &self,
        fingerprint: u64,
        substitution: &Substitution,
        type_id: TypeId,
    ) -> Option<TypeId> {
        let answers = self.0.borrow();
        let answers = answers.get(&fingerprint)?;
        if !answers.is_of(substitution) {
            return None;
        }
        answers.by_type.get(&type_id).copied()
    }

    fn remember(
        &self,
        fingerprint: u64,
        substitution: &Substitution,
        type_id: TypeId,
        answer: TypeId,
    ) {
        let mut answers = self.0.borrow_mut();
        let answers = answers.entry(fingerprint).or_insert_with(|| SubstitutionAnswers {
            entries: substitution.iter().map(|(&name, &type_id)| (name, type_id)).collect(),
            by_type: FxHashMap::default(),
        });
        if answers.is_of(substitution) {
            answers.by_type.insert(type_id, answer);
        }
    }
}

impl SubstitutionAnswers {
    fn is_of(&self, substitution: &Substitution) -> bool {
        self.entries.len() == substitution.len()
            && self.entries.iter().all(|(name, type_id)| substitution.get(name) == Some(type_id))
    }
}

/// The same for the same entries in whichever order the map holds them.
fn fingerprint(substitution: &Substitution) -> u64 {
    substitution.iter().fold(0u64, |fingerprint, entry| {
        let mut hasher = FxHasher::default();
        entry.hash(&mut hasher);
        fingerprint.wrapping_add(hasher.finish())
    })
}

impl<'q, Q> TypeOperations<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub fn sharing(queries: &'q Q, substituted: Substituted) -> TypeOperations<'q, Q> {
        TypeOperations {
            queries,
            substituted,
            erased: RefCell::default(),
            collapsed_causes: OnceCell::new(),
            without_causes: RefCell::default(),
            phantom: Cell::default(),
            cons_list: Cell::default(),
            placeholders: RefCell::default(),
        }
    }

    /// A closed stand-in for a type the program cannot specialize on, such as the
    /// element type under polymorphic recursion. It becomes Go `any`, and
    /// remembers why for the `any` census.
    pub fn erased(&self, erasure: Erasure) -> TypeId {
        if let Some(&erased) = self.erased.borrow().get(&erasure) {
            return erased;
        }
        let erased = self.stand_in(ERASED_UNIQUE - erasure.code());
        self.erased.borrow_mut().insert(erasure, erased);
        erased
    }

    /// The stand-in for the argument of a phantom parameter, which no
    /// representation mentions. It is no erasure: nothing holds a value of it.
    pub fn phantom(&self) -> TypeId {
        if let Some(phantom) = self.phantom.get() {
            return phantom;
        }
        let phantom = self.stand_in(PHANTOM_UNIQUE);
        self.phantom.set(Some(phantom));
        phantom
    }

    pub fn cons_list(&self) -> TypeId {
        if let Some(cons_list) = self.cons_list.get() {
            return cons_list;
        }
        let cons_list = self.stand_in(CONS_LIST_UNIQUE);
        self.cons_list.set(Some(cons_list));
        cons_list
    }

    pub fn is_cons_list(&self, type_id: TypeId) -> bool {
        self.cons_list.get() == Some(self.strip_annotations(type_id))
    }

    pub fn is_cons_list_name(&self, name: Name) -> bool {
        name.file == self.queries.prim_id() && !name.scoped && name.unique == CONS_LIST_UNIQUE
    }

    /// The stand-in for the quantified variable at a position of a scheme, so
    /// that every scheme's key spells its variables the same way.
    pub fn placeholder(&self, position: usize) -> TypeId {
        if let Some(&placeholder) = self.placeholders.borrow().get(position) {
            return placeholder;
        }
        let placeholder = self.stand_in(u32::MAX - 1 - position as u32);
        let mut placeholders = self.placeholders.borrow_mut();
        let length = placeholders.len().max(position + 1);
        placeholders.resize(length, placeholder);
        placeholders[position] = placeholder;
        placeholder
    }

    fn stand_in(&self, unique: u32) -> TypeId {
        let name = Name { file: self.queries.prim_id(), unique, scoped: false };
        let kind = self.queries.intern_type(Type::Unification(u32::MAX));
        self.queries.intern_type(Type::Rigid(name, Depth(0), kind))
    }

    pub fn without_causes(&self, type_id: TypeId) -> TypeId {
        if let Some(&collapsed) = self.without_causes.borrow().get(&type_id) {
            return collapsed;
        }
        let (substitution, fingerprint) = self.collapsed_causes.get_or_init(|| {
            let untracked = self.erased(Erasure::TypeVariable);
            let mut substitution = Substitution::default();
            for erasure in Erasure::ALL {
                let erased = self.erased(erasure);
                if erased != untracked
                    && let Type::Rigid(name, _, _) = self.lookup(erased)
                {
                    substitution.insert(*name, untracked);
                }
            }
            let fingerprint = fingerprint(&substitution);
            (substitution, fingerprint)
        });
        let collapsed = self.substitute_fingerprinted(type_id, substitution, *fingerprint);
        self.without_causes.borrow_mut().insert(type_id, collapsed);
        collapsed
    }

    /// The cause of an erased stand-in type.
    pub fn erasure(&self, type_id: TypeId) -> Option<Erasure> {
        let Type::Rigid(name, _, _) = self.lookup(self.strip_annotations(type_id)) else {
            return None;
        };
        self.name_erasure(*name)
    }

    /// The cause of an erased stand-in, by the name of its variable.
    pub fn name_erasure(&self, name: Name) -> Option<Erasure> {
        if name.file != self.queries.prim_id() || name.scoped {
            return None;
        }
        Erasure::from_code(ERASED_UNIQUE.checked_sub(name.unique)?)
    }

    /// Whether a type mentions an erased stand-in anywhere.
    pub fn contains_erased(&self, outer: TypeId) -> bool {
        let outer = self.strip_annotations(outer);
        if self.erasure(outer).is_some() {
            return true;
        }
        match self.lookup(outer) {
            Type::Application(function, argument) | Type::Function(function, argument) => {
                self.contains_erased(*function) || self.contains_erased(*argument)
            }
            Type::Row(row) => {
                let row = self.queries.lookup_row_type(*row);
                row.fields.iter().any(|field| self.contains_erased(field.id))
            }
            _ => false,
        }
    }

    pub fn grows(&self, requested: TypeId, enclosing: TypeId) -> bool {
        let requested = self.without_causes(requested);
        let enclosing = self.without_causes(enclosing);
        requested != enclosing && self.contains(requested, enclosing)
    }

    pub fn contains(&self, outer: TypeId, inner: TypeId) -> bool {
        let outer = self.strip_annotations(outer);
        if outer == self.strip_annotations(inner) {
            return true;
        }
        match self.lookup(outer) {
            Type::Application(function, argument) | Type::Function(function, argument) => {
                self.contains(*function, inner) || self.contains(*argument, inner)
            }
            Type::Row(row) => {
                let row = self.queries.lookup_row_type(*row);
                row.fields.iter().any(|field| self.contains(field.id, inner))
            }
            _ => false,
        }
    }

    pub fn rigid_names(&self, type_id: TypeId, names: &mut Vec<Name>) {
        self.rigid_names_outside(type_id, None, names);
    }

    pub fn rigid_names_outside(
        &self,
        type_id: TypeId,
        excluded: Option<TypeId>,
        names: &mut Vec<Name>,
    ) {
        if !self.queries.lookup_type_flags(type_id).has_rigid() || Some(type_id) == excluded {
            return;
        }
        match self.lookup(type_id) {
            Type::Rigid(name, _, _) => {
                if !names.contains(name) {
                    names.push(*name);
                }
            }
            Type::Application(function, argument) | Type::Function(function, argument) => {
                self.rigid_names_outside(*function, excluded, names);
                self.rigid_names_outside(*argument, excluded, names);
            }
            Type::Constrained(constraint, inner) => {
                self.rigid_names_outside(*constraint, excluded, names);
                self.rigid_names_outside(*inner, excluded, names);
            }
            Type::Forall(_, inner)
            | Type::Kinded(inner, _)
            | Type::ConstraintOrigin(inner, _)
            | Type::KindApplication(inner, _) => self.rigid_names_outside(*inner, excluded, names),
            Type::Row(row) => {
                let row = self.queries.lookup_row_type(*row);
                for field in row.fields.iter() {
                    self.rigid_names_outside(field.id, excluded, names);
                }
                if let Some(tail) = row.tail {
                    self.rigid_names_outside(tail, excluded, names);
                }
            }
            _ => {}
        }
    }

    pub fn lookup(&self, type_id: TypeId) -> &'q Type {
        self.queries.lookup_type(type_id)
    }

    /// The type with its rigid variables replaced. Specialization substitutes
    /// the same types under the same substitutions over and over, so each answer
    /// is kept.
    pub fn substitute(&self, type_id: TypeId, substitution: &Substitution) -> TypeId {
        if substitution.is_empty() || !self.queries.lookup_type_flags(type_id).has_rigid() {
            return type_id;
        }
        self.substitute_fingerprinted(type_id, substitution, fingerprint(substitution))
    }

    fn substitute_fingerprinted(
        &self,
        type_id: TypeId,
        substitution: &Substitution,
        fingerprint: u64,
    ) -> TypeId {
        if substitution.is_empty() || !self.queries.lookup_type_flags(type_id).has_rigid() {
            return type_id;
        }
        if let Some(substituted) = self.substituted.answer(fingerprint, substitution, type_id) {
            return substituted;
        }
        let substituted = self.substitute_nodes(type_id, substitution);
        self.substituted.remember(fingerprint, substitution, type_id, substituted);
        substituted
    }

    fn substitute_nodes(&self, type_id: TypeId, substitution: &Substitution) -> TypeId {
        if substitution.is_empty() || !self.queries.lookup_type_flags(type_id).has_rigid() {
            return type_id;
        }
        let substituted = match self.lookup(type_id).clone() {
            Type::Rigid(name, _, _) => return substitution.get(&name).copied().unwrap_or(type_id),
            Type::Application(function, argument) => {
                let substituted_function = self.substitute_nodes(function, substitution);
                let substituted_argument = self.substitute_nodes(argument, substitution);
                if substituted_function == function && substituted_argument == argument {
                    return type_id;
                }
                Type::Application(substituted_function, substituted_argument)
            }
            Type::KindApplication(function, _) => return self.substitute_nodes(function, substitution),
            Type::Kinded(inner, _) => return self.substitute_nodes(inner, substitution),
            Type::Forall(binder, inner) => {
                let substituted_inner = self.substitute_under_binder(binder, inner, substitution);
                if substituted_inner == inner {
                    return type_id;
                }
                Type::Forall(binder, substituted_inner)
            }
            Type::Constrained(constraint, inner) => {
                let substituted_constraint = self.substitute_nodes(constraint, substitution);
                let substituted_inner = self.substitute_nodes(inner, substitution);
                if substituted_constraint == constraint && substituted_inner == inner {
                    return type_id;
                }
                Type::Constrained(substituted_constraint, substituted_inner)
            }
            Type::ConstraintOrigin(constraint, _) => {
                return self.substitute_nodes(constraint, substitution);
            }
            Type::Function(argument, result) => {
                let substituted_argument = self.substitute_nodes(argument, substitution);
                let substituted_result = self.substitute_nodes(result, substitution);
                if substituted_argument == argument && substituted_result == result {
                    return type_id;
                }
                Type::Function(substituted_argument, substituted_result)
            }
            Type::Row(row) => {
                let row = self.queries.lookup_row_type(row).clone();
                return self.substitute_row(type_id, row, substitution);
            }
            Type::Constructor(..)
            | Type::Synonym(..)
            | Type::Integer(_)
            | Type::String(..)
            | Type::Unification(_)
            | Type::Free(_)
            | Type::Unknown(_) => return type_id,
        };
        self.queries.intern_type(substituted)
    }

    /// A synonym's quantifier keeps its name in every expansion, so
    /// `(f ~> m) -> Free f ~> m` binds the same `a` twice; the inner binder
    /// shadows the outer one. The substituted types are closed, so they cannot
    /// capture the binder.
    /// Closes the instantiations recorded on one reference over each other. A reference under an
    /// annotation, `(f :: forall a. T)`, instantiates f's quantifiers at the annotation's `a`,
    /// and the same node records the instantiation of `a` itself.
    pub fn close(&self, substitution: &mut Substitution) {
        for _ in 0..substitution.len() {
            let mut changed = false;
            let names: Vec<Name> = substitution.keys().copied().collect();
            for name in names {
                let argument = substitution[&name];
                let closed = self.substitute(argument, substitution);
                if closed != argument {
                    substitution.insert(name, closed);
                    changed = true;
                }
            }
            if !changed {
                return;
            }
        }
    }

    fn substitute_under_binder(
        &self,
        binder: ForallBinderId,
        inner: TypeId,
        substitution: &Substitution,
    ) -> TypeId {
        let name = self.queries.lookup_forall_binder(binder).name;
        if !substitution.contains_key(&name) {
            return self.substitute_nodes(inner, substitution);
        }
        let mut shadowed = substitution.clone();
        shadowed.remove(&name);
        self.substitute_nodes(inner, &shadowed)
    }

    fn substitute_row(&self, type_id: TypeId, row: RowType, substitution: &Substitution) -> TypeId {
        let mut fields: Vec<RowField> = row
            .fields
            .iter()
            .map(|field| RowField {
                label: field.label.clone(),
                id: self.substitute_nodes(field.id, substitution),
            })
            .collect();
        let mut tail = row.tail.map(|tail| self.substitute_nodes(tail, substitution));
        if self.is_same_row(&row, &fields, tail) {
            return type_id;
        }
        while let Some(tail_id) = tail {
            let Type::Row(tail_row) = self.strip(tail_id) else { break };
            let tail_row = self.queries.lookup_row_type(*tail_row).clone();
            fields.extend(tail_row.fields.iter().cloned());
            tail = tail_row.tail;
        }
        fields.sort_by(|left, right| left.label.cmp(&right.label));
        let row = RowType { fields: Arc::from(fields), tail };
        let row = self.queries.intern_row_type(row);
        self.queries.intern_type(Type::Row(row))
    }

    /// Whether substituting left the row as it is, and sorting and flattening
    /// it would too: its fields are sorted and its tail is no row.
    fn is_same_row(&self, row: &RowType, fields: &[RowField], tail: Option<TypeId>) -> bool {
        tail == row.tail
            && !tail.is_some_and(|tail| matches!(self.strip(tail), Type::Row(_)))
            && row.fields.iter().zip(fields).all(|(before, after)| before.id == after.id)
            && fields.windows(2).all(|pair| pair[0].label <= pair[1].label)
    }

    fn strip(&self, mut type_id: TypeId) -> &'q Type {
        loop {
            match self.lookup(type_id) {
                Type::Kinded(inner, _) | Type::ConstraintOrigin(inner, _) => type_id = *inner,
                Type::KindApplication(function, _) => type_id = *function,
                other => return other,
            }
        }
    }

    pub fn strip_annotations(&self, mut type_id: TypeId) -> TypeId {
        loop {
            match self.lookup(type_id) {
                Type::Kinded(inner, _) | Type::ConstraintOrigin(inner, _) => type_id = *inner,
                Type::KindApplication(function, _) => type_id = *function,
                _ => return type_id,
            }
        }
    }

    pub fn spine(&self, type_id: TypeId) -> (TypeId, Vec<TypeId>) {
        let mut arguments = vec![];
        let mut current = self.strip_annotations(type_id);
        while let Type::Application(function, argument) = self.lookup(current) {
            arguments.push(*argument);
            current = self.strip_annotations(*function);
        }
        arguments.reverse();
        (current, arguments)
    }

    pub fn peel_quantifiers(&self, mut type_id: TypeId) -> (Vec<Name>, TypeId) {
        let mut names = vec![];
        loop {
            match self.lookup(type_id) {
                Type::Forall(binder, inner) => {
                    names.push(self.queries.lookup_forall_binder(*binder).name);
                    type_id = *inner;
                }
                Type::Kinded(inner, _) | Type::ConstraintOrigin(inner, _) => type_id = *inner,
                _ => return (names, type_id),
            }
        }
    }

    pub fn peel_constraints(&self, mut type_id: TypeId) -> (Vec<TypeId>, TypeId) {
        let mut constraints = vec![];
        loop {
            match self.lookup(type_id) {
                Type::Constrained(constraint, inner) => {
                    constraints.push(*constraint);
                    type_id = *inner;
                }
                Type::Kinded(inner, _) | Type::ConstraintOrigin(inner, _) => type_id = *inner,
                _ => return (constraints, type_id),
            }
        }
    }

    pub fn function_parts(&self, type_id: TypeId) -> Option<(TypeId, TypeId)> {
        match self.strip(type_id) {
            Type::Function(argument, result) => Some((*argument, *result)),
            Type::Application(function_argument, result) => {
                let Type::Application(constructor, argument) = self.strip(*function_argument)
                else {
                    return None;
                };
                let Type::Constructor(file_id, item) = self.strip(*constructor) else {
                    return None;
                };
                let is_function = *file_id == self.queries.prim_id()
                    && self.queries.indexed(*file_id).ok().is_some_and(|indexed| {
                        indexed.items[*item].name.as_deref() == Some("Function")
                    });
                is_function.then_some((*argument, *result))
            }
            _ => None,
        }
    }

    /// `Prim.Function`, the constructor that `a -> b` applies.
    fn function_constructor(&self) -> Option<TypeId> {
        let prim = self.queries.prim_id();
        let indexed = self.queries.indexed(prim).ok()?;
        let (item, _) =
            indexed.items.iter_types().find(|(_, item)| item.name.as_deref() == Some("Function"))?;
        Some(self.queries.intern_type(Type::Constructor(prim, item)))
    }

    /// Matches `pattern`, whose variables in `variables` are pattern variables, against
    /// `target`. Type-class resolution already happened in the checker; matching only
    /// recovers which types the chosen declaration's variables stand for.
    pub fn match_type(
        &self,
        pattern: TypeId,
        target: TypeId,
        variables: &[Name],
        bindings: &mut Substitution,
    ) -> bool {
        let pattern = self.strip_annotations(pattern);
        let target = self.strip_annotations(target);
        if pattern == target {
            return true;
        }
        match (self.lookup(pattern), self.lookup(target)) {
            (Type::Rigid(name, _, _), _) if variables.contains(name) => match bindings.get(name) {
                Some(&bound) => bound == target || self.equivalent(bound, target),
                None => {
                    bindings.insert(*name, target);
                    true
                }
            },
            (Type::Application(pattern_function, pattern_argument), Type::Application(..)) => {
                let (pattern_function, pattern_argument) = (*pattern_function, *pattern_argument);
                let Type::Application(target_function, target_argument) = *self.lookup(target)
                else {
                    return false;
                };
                self.match_type(pattern_function, target_function, variables, bindings)
                    && self.match_type(pattern_argument, target_argument, variables, bindings)
            }
            (Type::Function(pattern_argument, pattern_result), Type::Function(..)) => {
                let (pattern_argument, pattern_result) = (*pattern_argument, *pattern_result);
                let Type::Function(target_argument, target_result) = *self.lookup(target) else {
                    return false;
                };
                self.match_type(pattern_argument, target_argument, variables, bindings)
                    && self.match_type(pattern_result, target_result, variables, bindings)
            }
            // `c a a` in `instance Newtype (Endo c a) (c a a)` against `a -> a`.
            (Type::Application(..), Type::Function(argument, result))
                if self.function_parts(pattern).is_none() =>
            {
                let (argument, result) = (*argument, *result);
                let Some(function) = self.function_constructor() else { return false };
                let applied = self.queries.intern_type(Type::Application(function, argument));
                let spelled = self.queries.intern_type(Type::Application(applied, result));
                self.match_type(pattern, spelled, variables, bindings)
            }
            (Type::Function(..), _) | (_, Type::Function(..)) => {
                let (Some(pattern_parts), Some(target_parts)) =
                    (self.function_parts(pattern), self.function_parts(target))
                else {
                    return false;
                };
                self.match_type(pattern_parts.0, target_parts.0, variables, bindings)
                    && self.match_type(pattern_parts.1, target_parts.1, variables, bindings)
            }
            (Type::Row(pattern_row), Type::Row(target_row)) => {
                let pattern_row = self.queries.lookup_row_type(*pattern_row).clone();
                let target_row = self.queries.lookup_row_type(*target_row).clone();
                self.match_row(pattern_row, target_row, variables, bindings)
            }
            (Type::Constructor(..), Type::Constructor(..)) => false,
            (Type::Forall(binder, pattern_inner), Type::Forall(_, target_inner)) => {
                let bound = self.queries.lookup_forall_binder(*binder).name;
                if !variables.contains(&bound) {
                    return self.match_type(*pattern_inner, *target_inner, variables, bindings);
                }
                let free: Vec<Name> =
                    variables.iter().copied().filter(|&name| name != bound).collect();
                self.match_type(*pattern_inner, *target_inner, &free, bindings)
            }
            _ => self.equivalent(pattern, target),
        }
    }

    fn match_row(
        &self,
        pattern: RowType,
        target: RowType,
        variables: &[Name],
        bindings: &mut Substitution,
    ) -> bool {
        let mut remaining: Vec<RowField> = target.fields.to_vec();
        for field in pattern.fields.iter() {
            let Some(position) = remaining.iter().position(|other| other.label == field.label)
            else {
                return false;
            };
            let other = remaining.remove(position);
            if !self.match_type(field.id, other.id, variables, bindings) {
                return false;
            }
        }
        match pattern.tail {
            Some(tail) => {
                let rest = RowType { fields: Arc::from(remaining), tail: target.tail };
                let rest = self.queries.intern_row_type(rest);
                let rest = self.queries.intern_type(Type::Row(rest));
                self.match_type(tail, rest, variables, bindings)
            }
            None => remaining.is_empty() && target.tail.is_none(),
        }
    }

    fn equivalent(&self, left: TypeId, right: TypeId) -> bool {
        self.strip_annotations(left) == self.strip_annotations(right)
    }
}
