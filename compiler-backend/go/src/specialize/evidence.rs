//! Resolving a constraint's evidence to a dictionary: instances, superclasses and givens.

use super::{Specializer, string_literal};
use crate::context::ModuleData;
use crate::dictionary::{Dictionary, InstanceDictionary, Reflected};
use crate::error::{GoError, GoResult, UnsupportedState};
use crate::types::Substitution;
use checking::TypeId;
use checking::core::Type;
use checking::evidence::{
    Evidence, EvidenceBinderId, EvidenceId, EvidenceState, EvidenceVarId, InstanceCandidateOrigin,
    ReflectableEvidence, ReflectableOrdering, SynthesizedEvidence,
};
use checking::tree::{self, TermDeclarationKind};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use std::sync::Arc;

pub(super) struct EvidenceScope<'a> {
    pub(super) module: &'a Arc<ModuleData>,
    pub(super) substitution: &'a Substitution,
    pub(super) givens: &'a FxHashMap<EvidenceBinderId, Dictionary>,
    pub(super) definition: &'a str,
}

impl EvidenceScope<'_> {
    fn unsupported(&self, state: UnsupportedState) -> GoError {
        GoError::Unsupported { definition: self.definition.to_string(), state }
    }
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn instance_declaration(
        &mut self,
        origin: InstanceCandidateOrigin,
    ) -> GoResult<(Arc<ModuleData>, tree::TermDeclarationId)> {
        let (file_id, declaration) = match origin {
            InstanceCandidateOrigin::Instance(file_id, instance) => {
                let module = self.context.module(file_id)?;
                let item = module.indexed.pairs.instance_to_item(instance);
                (file_id, item.and_then(|item| module.checked.tree.lookup_instance(item)))
            }
            InstanceCandidateOrigin::Derive(file_id, derive) => {
                let module = self.context.module(file_id)?;
                let item = module.indexed.pairs.derive_to_item(derive);
                (file_id, item.and_then(|item| module.checked.tree.lookup_derive(item)))
            }
        };
        let module = self.context.module(file_id)?;
        match declaration {
            Some(declaration) => Ok((module, declaration)),
            None => Err(GoError::Unsupported {
                definition: self.instance_name(origin)?.to_string(),
                state: UnsupportedState::MissingDeclaration,
            }),
        }
    }

    pub(super) fn instance_name(&mut self, origin: InstanceCandidateOrigin) -> GoResult<SmolStr> {
        let name = match origin {
            InstanceCandidateOrigin::Instance(file_id, instance) => {
                let module = self.context.module(file_id)?;
                let item = module.indexed.pairs.instance_to_item(instance);
                item.and_then(|item| module.indexed.items[item].name.clone())
            }
            InstanceCandidateOrigin::Derive(file_id, derive) => {
                let module = self.context.module(file_id)?;
                let item = module.indexed.pairs.derive_to_item(derive);
                item.and_then(|item| module.indexed.items[item].name.clone())
            }
        };
        Ok(name.unwrap_or_else(|| SmolStr::new_static("instance")))
    }

    pub(super) fn dictionary_names(
        &mut self,
        dictionaries: &[Dictionary],
    ) -> GoResult<Vec<SmolStr>> {
        let mut names = Vec::with_capacity(dictionaries.len());
        for dictionary in dictionaries {
            names.push(match dictionary {
                Dictionary::Instance(instance) => self.instance_name(instance.origin)?,
                _ => SmolStr::default(),
            });
        }
        Ok(names)
    }

    /// The closed types an instance's variables stand for, and the dictionaries for
    /// its own constraints, keyed the way its member bodies refer to them.
    pub(super) fn instance_environment(
        &mut self,
        module: &ModuleData,
        declaration: tree::TermDeclarationId,
        dictionary: &InstanceDictionary,
    ) -> GoResult<(Substitution, FxHashMap<EvidenceBinderId, Dictionary>)> {
        let TermDeclarationKind::Instance(instance) = &module.checked.tree[declaration].kind else {
            unreachable!("invariant violated: instance origin has a non-instance declaration")
        };
        let signature = module.checked.tree[declaration].type_id;
        let (names, _) = self.context.types.peel_quantifiers(signature);
        let mut substitution = Substitution::default();
        for (position, &argument) in dictionary.types.iter().enumerate() {
            if let Some(&name) = names.get(position) {
                substitution.insert(name, argument);
            }
            if let Some(&rigid) = instance.rigid_parameters.get(position)
                && let Type::Rigid(name, _, _) = self.context.types.lookup(rigid)
            {
                substitution.insert(*name, argument);
            }
        }
        let mut givens = FxHashMap::default();
        for (evidence, dictionary) in instance.evidences.iter().zip(dictionary.context.iter()) {
            if let Evidence::Given(binder) = evidence.evidence {
                givens.insert(binder, dictionary.clone());
            }
        }
        Ok((substitution, givens))
    }

    pub(super) fn resolve_evidence(
        &mut self,
        scope: &EvidenceScope<'_>,
        variable: EvidenceVarId,
        constraint: TypeId,
    ) -> GoResult<Dictionary> {
        let EvidenceState::Solved(proof) = scope.module.checked.evidence[variable].state else {
            return Err(scope.unsupported(UnsupportedState::UnsolvedEvidence));
        };
        self.resolve_proof(scope, proof, Some(constraint))
    }

    pub(super) fn resolve_proof(
        &mut self,
        scope: &EvidenceScope<'_>,
        proof: EvidenceId,
        constraint: Option<TypeId>,
    ) -> GoResult<Dictionary> {
        let evidence = scope.module.checked.evidence[proof].clone();
        match evidence {
            Evidence::Variable(variable) => {
                let EvidenceState::Solved(proof) = scope.module.checked.evidence[variable].state
                else {
                    return Err(scope.unsupported(UnsupportedState::UnsolvedEvidence));
                };
                self.resolve_proof(scope, proof, constraint)
            }
            Evidence::Given(binder) => match scope.givens.get(&binder) {
                Some(dictionary) => Ok(dictionary.clone()),
                None => Err(scope.unsupported(UnsupportedState::UnboundEvidence)),
            },
            Evidence::Instance { origin, subgoals } => {
                self.resolve_instance(scope, origin, &subgoals, constraint)
            }
            Evidence::Superclass { parent, superclass } => {
                match self.resolve_proof(scope, parent, None)? {
                    Dictionary::Instance(parent) => {
                        self.resolve_superclass(scope, &parent, superclass)
                    }
                    Dictionary::Runtime(parent) => {
                        self.runtime_superclass(scope.definition, parent, superclass)
                    }
                    _ => {
                        let superclass = format!("{superclass:?}");
                        Err(scope.unsupported(UnsupportedState::MissingSuperclass { superclass }))
                    }
                }
            }
            Evidence::Trivial => Ok(Dictionary::Trivial),
            Evidence::Synthesized(SynthesizedEvidence::IsSymbol(symbol)) => {
                Ok(Dictionary::Symbol(SmolStr::from(string_literal(&symbol))))
            }
            Evidence::Synthesized(SynthesizedEvidence::Reflectable(reflectable)) => {
                let reflected = match reflectable {
                    ReflectableEvidence::Integer(value) => Reflected::Integer(value),
                    ReflectableEvidence::String(value) => {
                        Reflected::String(SmolStr::from(string_literal(&value)))
                    }
                    ReflectableEvidence::Boolean(value) => Reflected::Boolean(value),
                    ReflectableEvidence::Ordering(ordering) => {
                        Reflected::Ordering(match ordering {
                            ReflectableOrdering::Less => SmolStr::new_static("LT"),
                            ReflectableOrdering::Equal => SmolStr::new_static("EQ"),
                            ReflectableOrdering::Greater => SmolStr::new_static("GT"),
                        })
                    }
                };
                Ok(Dictionary::Reflectable(reflected))
            }
            Evidence::Synthesized(SynthesizedEvidence::Service(_)) => {
                Err(scope
                    .unsupported(UnsupportedState::Construct { construct: "service evidence" }))
            }
        }
    }

    pub(super) fn resolve_instance(
        &mut self,
        scope: &EvidenceScope<'_>,
        origin: InstanceCandidateOrigin,
        subgoals: &[EvidenceVarId],
        constraint: Option<TypeId>,
    ) -> GoResult<Dictionary> {
        let (module, declaration) = self.instance_declaration(origin)?;
        let signature = module.checked.tree[declaration].type_id;
        let (names, body) = self.context.types.peel_quantifiers(signature);
        let (contexts, head) = self.context.types.peel_constraints(body);
        let mut bindings = Substitution::default();
        if !names.is_empty() {
            let Some(constraint) = constraint else {
                return Err(scope.unsupported(UnsupportedState::Construct {
                    construct: "superclasses of instances with type variables",
                }));
            };
            let constraint = crate::monotype::expand_synonyms(&mut self.context, constraint)?;
            let head = crate::monotype::expand_synonyms(&mut self.context, head)?;
            if !self.context.types.match_type(head, constraint, &names, &mut bindings) {
                let pretty =
                    checking::core::pretty::Pretty::new(self.context.queries, &module.checked);
                let constraint = match pretty.render(constraint) {
                    Ok(rendered) => {
                        format!("{rendered} against instance {}", self.instance_name(origin)?)
                    }
                    Err(_) => format!("{constraint:?}"),
                };
                return Err(scope.unsupported(UnsupportedState::InstanceMismatch { constraint }));
            }
        }
        let mut recorded = Vec::with_capacity(subgoals.len());
        for (&subgoal, &instance_constraint) in subgoals.iter().zip(contexts.iter()) {
            let Some(constraint) = scope.module.checked.evidence[subgoal].constraint else {
                recorded.push(None);
                continue;
            };
            let constraint = self.context.types.substitute(constraint, scope.substitution);
            let constraint = crate::monotype::expand_synonyms(&mut self.context, constraint)?;
            let instance_constraint =
                crate::monotype::expand_synonyms(&mut self.context, instance_constraint)?;
            self.context.types.match_type(instance_constraint, constraint, &names, &mut bindings);
            recorded.push(Some(constraint));
        }
        let mut types = Vec::with_capacity(names.len());
        for name in &names {
            match bindings.get(name) {
                Some(&bound) => types.push(bound),
                None => {
                    let unconstrained =
                        self.context.queries.intern_type(Type::Unification(u32::MAX));
                    types.push(unconstrained);
                }
            }
        }
        let mut context = Vec::with_capacity(subgoals.len());
        for ((&subgoal, &instance_constraint), recorded) in
            subgoals.iter().zip(contexts.iter()).zip(recorded)
        {
            let constraint = recorded
                .unwrap_or_else(|| self.context.types.substitute(instance_constraint, &bindings));
            context.push(self.resolve_evidence(scope, subgoal, constraint)?);
        }
        let dictionary = Arc::new(InstanceDictionary {
            origin,
            types: Arc::from(types),
            context: Arc::from(context),
        });
        let TermDeclarationKind::Instance(instance) = &module.checked.tree[declaration].kind else {
            return Err(scope.unsupported(UnsupportedState::MissingDeclaration));
        };
        if let tree::InstanceImplementation::Delegate { constraint, evidence } =
            instance.implementation
        {
            let (substitution, givens) =
                self.instance_environment(&module, declaration, &dictionary)?;
            let constraint = self.context.types.substitute(constraint, &substitution);
            let instance_scope = EvidenceScope {
                module: &module,
                substitution: &substitution,
                givens: &givens,
                definition: scope.definition,
            };
            return self.resolve_evidence(&instance_scope, evidence, constraint);
        }
        Ok(Dictionary::Instance(dictionary))
    }

    pub(super) fn resolve_superclass(
        &mut self,
        scope: &EvidenceScope<'_>,
        parent: &Arc<InstanceDictionary>,
        superclass: checking::evidence::SuperclassId,
    ) -> GoResult<Dictionary> {
        let (module, declaration) = self.instance_declaration(parent.origin)?;
        let TermDeclarationKind::Instance(instance) = &module.checked.tree[declaration].kind else {
            return Err(scope.unsupported(UnsupportedState::MissingDeclaration));
        };
        let Some(entry) = instance.superclasses.iter().find(|entry| entry.id == superclass) else {
            let superclass = format!("{superclass:?}");
            return Err(scope.unsupported(UnsupportedState::MissingSuperclass { superclass }));
        };
        let entry = *entry;
        let (substitution, givens) = self.instance_environment(&module, declaration, parent)?;
        let constraint = self.context.types.substitute(entry.constraint, &substitution);
        let instance_scope = EvidenceScope {
            module: &module,
            substitution: &substitution,
            givens: &givens,
            definition: scope.definition,
        };
        self.resolve_evidence(&instance_scope, entry.evidence, constraint)
    }
}
