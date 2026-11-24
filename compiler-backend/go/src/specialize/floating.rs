use checking::TypeId;
use checking::core::Type;
use checking::evidence::EvidenceVarId;
use files::FileId;
use indexing::TermItemId;

use super::{Scope, Specializer};
use crate::dictionary::Dictionary;
use crate::error::{GoResult, UnsupportedState};
use crate::types::Substitution;

type AppliedEvidence = (EvidenceVarId, TypeId);

/// `apply policy f dict`: `policy` returns `forall m. Monad m => Policy m`, and
/// through `$` the checker instantiates `apply`'s result at the constrained
/// `Monad m => Policy m`, applying the evidence to the whole application. Once
/// the constraint is closed its dictionary is known, so the application is
/// specialized as if the evidence were applied where the constrained value is
/// made: the instantiations lose the constraint, and the references inside the
/// arguments that still lack its dictionary take the trailing one.
impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn with_floating_scope<T>(
        &mut self,
        specialize: impl FnOnce(&mut Self) -> GoResult<T>,
    ) -> GoResult<T> {
        let depth = self.floating.len();
        let specialized = specialize(self);
        self.floating.truncate(depth);
        specialized
    }

    /// Moves the trailing evidence that belongs to a constrained instantiation
    /// out of the application, and drops the constraint from the instantiations.
    pub(super) fn float_instantiated_evidence(
        &mut self,
        scope: &Scope,
        (instantiations, head_instantiations): (&mut Substitution, &Substitution),
        mut evidence: Vec<AppliedEvidence>,
        mut trailing: Vec<Dictionary>,
    ) -> GoResult<(Vec<AppliedEvidence>, Vec<Dictionary>)> {
        let mut constraints = vec![];
        for &value in instantiations.values().chain(head_instantiations.values()) {
            self.constraints_inside(value, &mut constraints);
        }
        if constraints.is_empty() {
            return Ok((evidence, trailing));
        }
        let floated = self.floating.len();
        let unfloated = (evidence.clone(), trailing.clone());
        while let Some(&(_, applied)) = evidence.last()
            && let Some(dictionary) = trailing.last()
        {
            let applied = self.context.types.substitute(applied, &scope.substitution);
            if !constraints.iter().any(|&constraint| self.same_type(constraint, applied)) {
                break;
            }
            self.floating.push((applied, dictionary.clone()));
            evidence.pop();
            trailing.pop();
        }
        if !self.floats_every_constraint(&constraints, floated) {
            self.floating.truncate(floated);
            return Ok(unfloated);
        }
        if self.floating[floated..].iter().any(|&(constraint, _)| !self.is_closed(constraint)) {
            return Err(self.unsupported(
                scope,
                UnsupportedState::Construct {
                    construct: "polymorphic functions instantiated at a constrained type whose constraint stays polymorphic",
                },
            ));
        }
        for value in instantiations.values_mut() {
            *value = self.without_floating_constraints(*value);
        }
        Ok((evidence, trailing))
    }

    /// A type without the constraints whose evidence an enclosing application
    /// floats: `Monad Effect => Policy Effect` stands as `Policy Effect`.
    pub(super) fn without_floating_constraints(&self, type_id: TypeId) -> TypeId {
        if self.floating.is_empty() {
            return type_id;
        }
        let stripped = self.context.types.strip_annotations(type_id);
        let rebuilt = match *self.context.types.lookup(stripped) {
            Type::Constrained(constraint, inner) => {
                let inner = self.without_floating_constraints(inner);
                if self.floating_dictionary(constraint).is_some() {
                    return inner;
                }
                Type::Constrained(constraint, inner)
            }
            Type::Function(argument, result) => Type::Function(
                self.without_floating_constraints(argument),
                self.without_floating_constraints(result),
            ),
            Type::Application(function, argument) => Type::Application(
                self.without_floating_constraints(function),
                self.without_floating_constraints(argument),
            ),
            _ => return type_id,
        };
        if *self.context.types.lookup(stripped) == rebuilt {
            return type_id;
        }
        self.context.queries.intern_type(rebuilt)
    }

    pub(super) fn floating_dictionary(&self, constraint: TypeId) -> Option<Dictionary> {
        self.floating
            .iter()
            .rev()
            .find(|(floated, _)| self.same_type(*floated, constraint))
            .map(|(_, dictionary)| dictionary.clone())
    }

    /// The dictionaries a reference inside a floating application's arguments
    /// still lacks: `policy` passed to `$` is instantiated but its result's
    /// `Monad m` is discharged only after `$`.
    pub(super) fn add_floating_dictionaries(
        &mut self,
        (file_id, term): (FileId, TermItemId),
        instantiations: &Substitution,
        dictionaries: &mut Vec<Dictionary>,
    ) -> GoResult<()> {
        if self.floating.is_empty() {
            return Ok(());
        }
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else {
            return Ok(());
        };
        let constraints = self.constraints_along_results(declared)?;
        for constraint in constraints.into_iter().skip(dictionaries.len()) {
            let constraint = self.context.types.substitute(constraint, instantiations);
            match self.floating_dictionary(constraint) {
                Some(dictionary) => dictionaries.push(dictionary),
                None => break,
            }
        }
        Ok(())
    }

    fn constraints_along_results(&mut self, declared: TypeId) -> GoResult<Vec<TypeId>> {
        let mut constraints = vec![];
        let mut current = declared;
        loop {
            current = crate::monotype::expand_synonyms(&mut self.context, current)?;
            let (_, inner) = self.context.types.peel_quantifiers(current);
            let (found, inner) = self.context.types.peel_constraints(inner);
            constraints.extend(found);
            let inner = self.context.types.strip_annotations(inner);
            if matches!(self.context.types.lookup(inner), Type::Forall(..) | Type::Constrained(..))
            {
                current = inner;
                continue;
            }
            match self.context.types.function_parts(inner) {
                Some((_, result)) => current = result,
                None => return Ok(constraints),
            }
        }
    }

    fn constraints_inside(&self, type_id: TypeId, constraints: &mut Vec<TypeId>) {
        let type_id = self.context.types.strip_annotations(type_id);
        match *self.context.types.lookup(type_id) {
            Type::Constrained(constraint, inner) => {
                constraints.push(constraint);
                self.constraints_inside(inner, constraints);
            }
            Type::Function(left, right) | Type::Application(left, right) => {
                self.constraints_inside(left, constraints);
                self.constraints_inside(right, constraints);
            }
            _ => {}
        }
    }

    /// Whether the evidence after the application discharges every constraint
    /// the instantiations hold. A constraint it leaves, `Show b` of the
    /// `forall b. Show b => …` that `unsafeCoerce` relabels, belongs to a
    /// polymorphic value passed as it is, so nothing floats.
    fn floats_every_constraint(&self, constraints: &[TypeId], floated: usize) -> bool {
        constraints.iter().all(|&constraint| {
            self.floating[floated..].iter().any(|&(applied, _)| self.same_type(constraint, applied))
        })
    }

    fn is_closed(&self, type_id: TypeId) -> bool {
        let mut names = vec![];
        self.context.types.rigid_names(type_id, &mut names);
        names.into_iter().all(|name| self.context.types.name_erasure(name).is_some())
    }

    /// Whether two closed types are the same up to kind annotations, which the
    /// checker spells at some occurrences of a constraint and not at others.
    fn same_type(&self, left: TypeId, right: TypeId) -> bool {
        let left = self.context.types.strip_annotations(left);
        let right = self.context.types.strip_annotations(right);
        if left == right {
            return true;
        }
        match (self.context.types.lookup(left), self.context.types.lookup(right)) {
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            )
            | (
                Type::Function(left_function, left_argument),
                Type::Function(right_function, right_argument),
            ) => {
                self.same_type(*left_function, *right_function)
                    && self.same_type(*left_argument, *right_argument)
            }
            _ => false,
        }
    }
}
