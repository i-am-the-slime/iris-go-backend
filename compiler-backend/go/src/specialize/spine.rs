use checking::core::{Name, Type};
use checking::evidence::EvidenceVarId;
use checking::{TypeId, tree};

use super::{Scope, Specializer};
use crate::dictionary::Dictionary;
use crate::error::{GoResult, UnsupportedState};
use crate::foreign::{self, Foreign};
use crate::monomorphic::{Expression, ExpressionKind};
use crate::monotype::MonotypeId;
use crate::types::Substitution;

pub(super) struct ApplicationSpine {
    pub head: tree::ExpressionId,
    pub arguments: Vec<tree::ExpressionId>,
    pub trailing: Vec<(EvidenceVarId, TypeId)>,
    pub instantiations: Substitution,
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn application_spine(
        &mut self,
        scope: &Scope,
        id: tree::ExpressionId,
    ) -> ApplicationSpine {
        let tree = &scope.module.checked.tree;
        let mut arguments = vec![];
        let mut trailing = vec![];
        let mut pending = vec![];
        let mut instantiations = Substitution::default();
        let mut current = id;
        loop {
            match tree[current].kind {
                tree::ExpressionKind::TermApplication { function, argument } => {
                    for &node in pending.iter().chain([&current]) {
                        for instantiation in tree.lookup_instantiations(node) {
                            let closed = self
                                .context
                                .types
                                .substitute(instantiation.argument, &scope.substitution);
                            instantiations.insert(instantiation.name, closed);
                        }
                    }
                    trailing.extend(pending.drain(..).map(|node| match tree[node].kind {
                        tree::ExpressionKind::EvidenceApplication {
                            evidence, constraint, ..
                        } => (evidence, constraint),
                        _ => unreachable!("invariant violated: pending nodes apply evidence"),
                    }));
                    arguments.push(argument);
                    current = function;
                }
                tree::ExpressionKind::EvidenceApplication { function, .. } => {
                    pending.push(current);
                    current = function;
                }
                _ => break,
            }
        }
        let head = pending.first().copied().unwrap_or(current);
        arguments.reverse();
        trailing.reverse();
        ApplicationSpine { head, arguments, trailing, instantiations }
    }

    pub(super) fn trailing_dictionaries(
        &mut self,
        scope: &Scope,
        trailing: &[(EvidenceVarId, TypeId)],
    ) -> GoResult<Vec<Dictionary>> {
        let mut dictionaries = Vec::with_capacity(trailing.len());
        for &(evidence, constraint) in trailing {
            let constraint = self.context.types.substitute(constraint, &scope.substitution);
            dictionaries.push(self.resolve_evidence(&scope.evidence(), evidence, constraint)?);
        }
        Ok(dictionaries)
    }

    pub(super) fn next_parameter_type(
        &mut self,
        type_id: TypeId,
        instantiations: &Substitution,
    ) -> GoResult<Option<(TypeId, TypeId)>> {
        if let Some(parts) = self.context.types.function_parts(type_id) {
            return Ok(Some(parts));
        }
        let mut current = crate::monotype::expand_synonyms(&mut self.context, type_id)?;
        loop {
            let (names, inner) = self.context.types.peel_quantifiers(current);
            let (constraints, inner) = self.context.types.peel_constraints(inner);
            if names.is_empty() && constraints.is_empty() {
                return Ok(self.context.types.function_parts(current));
            }
            if !names.iter().all(|name| instantiations.contains_key(name)) {
                return Ok(None);
            }
            current = self.context.types.substitute(inner, instantiations);
        }
    }

    fn coerced_instantiation(
        &mut self,
        scope: &Scope,
        argument: tree::ExpressionId,
        evidence: &[(EvidenceVarId, TypeId)],
        result: TypeId,
    ) -> GoResult<Substitution> {
        let checked = scope.module.checked.tree[argument].type_id;
        let closed = self.context.types.substitute(checked, &scope.substitution);
        let closed = crate::monotype::expand_synonyms(&mut self.context, closed)?;
        let (names, inner) = self.context.types.peel_quantifiers(closed);
        let (constraints, body) = self.context.types.peel_constraints(inner);
        let mut bindings = Substitution::default();
        let mut matched = constraints.len() == evidence.len();
        for (&constraint, &(_, applied)) in constraints.iter().zip(evidence) {
            let applied = self.context.types.substitute(applied, &scope.substitution);
            matched &= self.context.types.match_type(constraint, applied, &names, &mut bindings);
        }
        let result = crate::monotype::expand_synonyms(&mut self.context, result)?;
        self.align(body, result, &names, &mut bindings);
        if !matched || !names.iter().all(|name| bindings.contains_key(name)) {
            return Err(scope.unsupported(UnsupportedState::Construct {
                construct: "evidence applied to a coercion whose argument it does not determine",
            }));
        }
        Ok(bindings)
    }

    fn align(
        &self,
        pattern: TypeId,
        target: TypeId,
        variables: &[Name],
        bindings: &mut Substitution,
    ) {
        let types = &self.context.types;
        match (
            types.lookup(types.strip_annotations(pattern)).clone(),
            types.lookup(types.strip_annotations(target)).clone(),
        ) {
            (Type::Rigid(name, _, _), _) if variables.contains(&name) => {
                bindings.entry(name).or_insert(target);
            }
            (
                Type::Application(pattern_function, pattern_argument),
                Type::Application(target_function, target_argument),
            )
            | (
                Type::Function(pattern_function, pattern_argument),
                Type::Function(target_function, target_argument),
            ) => {
                self.align(pattern_function, target_function, variables, bindings);
                self.align(pattern_argument, target_argument, variables, bindings);
            }
            (Type::Row(pattern_row), Type::Row(target_row)) => {
                let pattern_row = self.context.queries.lookup_row_type(pattern_row).clone();
                let target_row = self.context.queries.lookup_row_type(target_row).clone();
                let target_fields = &target_row.fields;
                for field in pattern_row.fields.iter() {
                    if let Some(other) =
                        target_fields.iter().find(|other| other.label == field.label)
                    {
                        self.align(field.id, other.id, variables, bindings);
                    }
                }
            }
            _ => {}
        }
    }

    pub(super) fn is_unsafe_coerce(
        &mut self,
        scope: &Scope,
        head: tree::ExpressionId,
    ) -> GoResult<bool> {
        let tree::ExpressionKind::Variable {
            resolution:
                tree::VariableResolution::Source(lowering::TermVariableResolution::Reference(
                    file_id,
                    term,
                )),
        } = scope.module.checked.tree[head].kind
        else {
            return Ok(false);
        };
        let module = self.context.module(file_id)?;
        let Some(name) = module.indexed.items[term].name.as_deref() else { return Ok(false) };
        Ok(foreign::foreign_import(&module.name, name) == Some(&Foreign::UnsafeCoerce))
    }

    pub(super) fn coerced_with_evidence(
        &mut self,
        scope: &mut Scope,
        argument: tree::ExpressionId,
        evidence: &[(EvidenceVarId, TypeId)],
        trailing: Vec<Dictionary>,
        (result, monotype): (TypeId, MonotypeId),
    ) -> GoResult<Expression> {
        let instantiation = self.coerced_instantiation(scope, argument, evidence, result)?;
        let substitution = scope.substitution.clone();
        scope.substitution.extend(instantiation);
        let argument = match scope.module.checked.tree[argument].kind {
            tree::ExpressionKind::EvidenceAbstraction { .. } => {
                self.evidence_redex(scope, argument, trailing)
            }
            _ => self.trailed_reference(scope, argument, Substitution::default(), None, trailing),
        };
        scope.substitution = substitution;
        let argument = argument?;
        let function = self.monotypes.function(argument.monotype, monotype);
        let function = self.foreign(&Foreign::UnsafeCoerce, function);
        let arguments = vec![argument];
        let kind = ExpressionKind::Apply { function: Box::new(function), arguments };
        Ok(Expression::new(kind, monotype))
    }
}
