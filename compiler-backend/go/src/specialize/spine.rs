use checking::TypeId;
use checking::evidence::EvidenceVarId;
use checking::tree;

use super::{Scope, Specializer};
use crate::dictionary::Dictionary;
use crate::error::GoResult;
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
}
