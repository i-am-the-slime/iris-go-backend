use std::sync::Arc;

use checking::TypeId;
use checking::core::{ForallBinderId, Name, RowField, RowType, Type};
use rustc_hash::FxHashMap;

use crate::erasure::Erasure;

pub type Substitution = FxHashMap<Name, TypeId>;

/// Erased stand-ins are rigid variables numbered down from here, clear of the
/// scheme placeholders just below `u32::MAX`.
const ERASED_UNIQUE: u32 = u32::MAX - 4096;

pub struct TypeOperations<'q, Q> {
    queries: &'q Q,
}

impl<'q, Q> TypeOperations<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub fn new(queries: &'q Q) -> TypeOperations<'q, Q> {
        TypeOperations { queries }
    }

    /// A closed stand-in for a type the program cannot specialize on, such as the
    /// element type under polymorphic recursion. It becomes Go `any`, and
    /// remembers why for the `any` census.
    pub fn erased(&self, erasure: Erasure) -> TypeId {
        let unique = ERASED_UNIQUE - erasure.tracked().code();
        let name = Name { file: self.queries.prim_id(), unique, scoped: false };
        let kind = self.queries.intern_type(Type::Unification(u32::MAX));
        self.queries.intern_type(Type::Rigid(name, checking::core::Depth(0), kind))
    }

    /// The cause of an erased stand-in type.
    pub fn erasure(&self, type_id: TypeId) -> Option<Erasure> {
        let Type::Rigid(name, _, _) = self.lookup(self.strip_annotations(type_id)) else {
            return None;
        };
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
        if !self.queries.lookup_type_flags(type_id).has_rigid() {
            return;
        }
        match self.lookup(type_id) {
            Type::Rigid(name, _, _) => {
                if !names.contains(name) {
                    names.push(*name);
                }
            }
            Type::Application(function, argument) | Type::Function(function, argument) => {
                self.rigid_names(*function, names);
                self.rigid_names(*argument, names);
            }
            Type::Constrained(constraint, inner) => {
                self.rigid_names(*constraint, names);
                self.rigid_names(*inner, names);
            }
            Type::Forall(_, inner)
            | Type::Kinded(inner, _)
            | Type::ConstraintOrigin(inner, _)
            | Type::KindApplication(inner, _) => self.rigid_names(*inner, names),
            Type::Row(row) => {
                let row = self.queries.lookup_row_type(*row);
                for field in row.fields.iter() {
                    self.rigid_names(field.id, names);
                }
                if let Some(tail) = row.tail {
                    self.rigid_names(tail, names);
                }
            }
            _ => {}
        }
    }

    pub fn lookup(&self, type_id: TypeId) -> &'q Type {
        self.queries.lookup_type(type_id)
    }

    pub fn substitute(&self, type_id: TypeId, substitution: &Substitution) -> TypeId {
        if substitution.is_empty() || !self.queries.lookup_type_flags(type_id).has_rigid() {
            return type_id;
        }
        let substituted = match self.lookup(type_id).clone() {
            Type::Rigid(name, _, _) => return substitution.get(&name).copied().unwrap_or(type_id),
            Type::Application(function, argument) => Type::Application(
                self.substitute(function, substitution),
                self.substitute(argument, substitution),
            ),
            Type::KindApplication(function, _) => return self.substitute(function, substitution),
            Type::Kinded(inner, _) => return self.substitute(inner, substitution),
            Type::Forall(binder, inner) => {
                Type::Forall(binder, self.substitute_under_binder(binder, inner, substitution))
            }
            Type::Constrained(constraint, inner) => Type::Constrained(
                self.substitute(constraint, substitution),
                self.substitute(inner, substitution),
            ),
            Type::ConstraintOrigin(constraint, _) => {
                return self.substitute(constraint, substitution);
            }
            Type::Function(argument, result) => Type::Function(
                self.substitute(argument, substitution),
                self.substitute(result, substitution),
            ),
            Type::Row(row) => {
                let row = self.queries.lookup_row_type(row).clone();
                return self.substitute_row(row, substitution);
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
    fn substitute_under_binder(
        &self,
        binder: ForallBinderId,
        inner: TypeId,
        substitution: &Substitution,
    ) -> TypeId {
        let name = self.queries.lookup_forall_binder(binder).name;
        if !substitution.contains_key(&name) {
            return self.substitute(inner, substitution);
        }
        let mut shadowed = substitution.clone();
        shadowed.remove(&name);
        self.substitute(inner, &shadowed)
    }

    fn substitute_row(&self, row: RowType, substitution: &Substitution) -> TypeId {
        let mut fields: Vec<RowField> = row
            .fields
            .iter()
            .map(|field| RowField {
                label: field.label.clone(),
                id: self.substitute(field.id, substitution),
            })
            .collect();
        let mut tail = row.tail.map(|tail| self.substitute(tail, substitution));
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
