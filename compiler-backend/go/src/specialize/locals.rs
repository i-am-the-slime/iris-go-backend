use std::sync::Arc;

use checking::TypeId;
use checking::core::{Name, Type};
use checking::tree::{self, DeclarationAbstraction};
use files::FileId;
use indexing::TermItemId;
use smol_str::SmolStr;

use super::{
    LOCAL_SPECIALIZATION_LIMIT, LocalForm, LocalSource, LocalSpecialization, Reference, Scope,
    Specializer, runtime,
};
use crate::dictionary::Dictionary;
use crate::erasure::Erasure;
use crate::error::{GoResult, UnsupportedState};
use crate::monomorphic::{Binding, Expression, ExpressionKind};
use crate::scheme::rank_n_scheme;
use crate::types::Substitution;

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn local_reference(
        &mut self,
        scope: &Scope,
        source: LocalSource,
    ) -> GoResult<Expression> {
        let Some(local) = scope.locals.get(&source) else {
            return Err(self.unsupported(
                scope,
                UnsupportedState::Construct {
                    construct: "references to locals outside their scope",
                },
            ));
        };
        Ok(Expression::new(ExpressionKind::Local(local.id), local.monotype))
    }

    pub(super) fn reference(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
        instantiations: Substitution,
        expected: Option<TypeId>,
    ) -> GoResult<Expression> {
        self.trailed_reference(scope, id, instantiations, expected, vec![])
    }

    pub(super) fn trailed_reference(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
        mut instantiations: Substitution,
        expected: Option<TypeId>,
        trailing: Vec<Dictionary>,
    ) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let tree = &module.checked.tree;
        let mut dictionaries = vec![];
        let mut current = id;
        let mut through_alias = false;
        let resolution = loop {
            let mut evidences = vec![];
            let mut recorded = Substitution::default();
            loop {
                for instantiation in tree.lookup_instantiations(current) {
                    recorded.insert(instantiation.name, instantiation.argument);
                }
                match tree[current].kind {
                    tree::ExpressionKind::EvidenceApplication {
                        function,
                        evidence,
                        constraint,
                    } => {
                        evidences.push((evidence, constraint));
                        current = function;
                    }
                    _ => break,
                }
            }
            instantiations.extend(self.closed_instantiations(scope, recorded));
            self.context.types.close(&mut instantiations);
            evidences.reverse();
            for (evidence, constraint) in evidences {
                let constraint = self.context.types.substitute(constraint, &scope.substitution);
                dictionaries.push(self.resolve_evidence(
                    &scope.evidence(),
                    evidence,
                    constraint,
                )?);
            }

            let resolution = match &tree[current].kind {
                tree::ExpressionKind::Variable { resolution }
                | tree::ExpressionKind::RecordPun { resolution, .. } => *resolution,
                tree::ExpressionKind::Constructor { resolution } if trailing.is_empty() => {
                    let (file_id, term) = *resolution;
                    let monotype =
                        self.instantiated_monotype(scope, current, file_id, term, &instantiations)?;
                    return self.constructor(scope, file_id, term, monotype);
                }
                tree::ExpressionKind::EvidenceAbstraction { .. } => {
                    dictionaries.extend(trailing);
                    return self.evidence_redex(scope, current, dictionaries);
                }
                tree::ExpressionKind::TermApplication { .. }
                    if !through_alias && !dictionaries.is_empty() && trailing.is_empty() =>
                {
                    return self.application(scope, id);
                }
                tree::ExpressionKind::RecordAccess { record, labels } => {
                    let closed = self.accessed_field_scheme(scope, current, *record, labels)?;
                    let closed = closed.map(|(closed, accessed)| {
                        instantiations.extend(accessed);
                        closed
                    });
                    let value = self.expression(scope, current)?;
                    dictionaries.extend(trailing);
                    return self.instantiated_scheme_value(
                        scope,
                        value,
                        closed,
                        &instantiations,
                        dictionaries,
                    );
                }
                _ => {
                    if dictionaries.is_empty() && trailing.is_empty() {
                        return self.expression(scope, current);
                    }
                    return Err(self.unsupported(
                        scope,
                        UnsupportedState::Construct {
                            construct: "evidence applied to a non-reference",
                        },
                    ));
                }
            };
            if let tree::VariableResolution::Source(lowering::TermVariableResolution::Let(group)) =
                resolution
                && let Some(&aliased) = scope.local_aliases.get(&group)
            {
                current = aliased;
                through_alias = true;
                continue;
            }
            break resolution;
        };
        dictionaries.extend(trailing);

        match resolution {
            tree::VariableResolution::Generated(binder) => {
                let source = self.checked_binder_source(scope, binder);
                self.instantiated_local_reference(scope, source, &instantiations, dictionaries)
            }
            tree::VariableResolution::Source(lowering::TermVariableResolution::Binder(binder)) => {
                let source = LocalSource::Binder(binder);
                self.instantiated_local_reference(scope, source, &instantiations, dictionaries)
            }
            tree::VariableResolution::Source(lowering::TermVariableResolution::Let(group))
                if scope.polymorphic_locals.contains_key(&group) =>
            {
                self.polymorphic_local_reference(scope, group, &instantiations, dictionaries)
            }
            tree::VariableResolution::Source(lowering::TermVariableResolution::Let(group)) => {
                let source = LocalSource::Let(group);
                self.instantiated_local_reference(scope, source, &instantiations, dictionaries)
            }
            tree::VariableResolution::Source(lowering::TermVariableResolution::RecordPun(pun)) => {
                let source = LocalSource::RecordPun(pun);
                self.instantiated_local_reference(scope, source, &instantiations, dictionaries)
            }
            tree::VariableResolution::Source(lowering::TermVariableResolution::Reference(
                file_id,
                term,
            )) => {
                let checked = expected.unwrap_or(tree[id].type_id);
                self.erase_rank_n_skolems(scope, checked, &mut instantiations)?;
                self.recover_unrecorded_instantiations(
                    scope,
                    checked,
                    file_id,
                    term,
                    &mut instantiations,
                )?;
                self.add_floating_dictionaries(
                    (file_id, term),
                    &instantiations,
                    &mut dictionaries,
                )?;
                let monotype =
                    self.instantiated_monotype(scope, current, file_id, term, &instantiations)?;
                let reference = Reference { file_id, term, expression: id };
                self.global_reference(scope, reference, &instantiations, dictionaries, monotype)
            }
        }
    }

    fn accessed_field_scheme(
        &mut self,
        scope: &Scope,
        access: tree::ExpressionId,
        record: tree::ExpressionId,
        labels: &[SmolStr],
    ) -> GoResult<Option<(TypeId, Substitution)>> {
        let tree = &scope.module.checked.tree;
        let mut field = self.context.types.substitute(tree[record].type_id, &scope.substitution);
        for label in labels {
            let record = crate::monotype::expand_synonyms(&mut self.context, field)?;
            let Some(found) = self.record_field_type(record, label) else {
                return Ok(None);
            };
            field = found;
        }
        let Some(closed) = self.scheme_type(scope, field)? else {
            return Ok(None);
        };
        let (names, body) = self.context.types.peel_quantifiers(closed);
        let (_, body) = self.context.types.peel_constraints(body);
        let accessed = self.context.types.substitute(tree[access].type_id, &scope.substitution);
        let (_, accessed) = self.context.types.peel_constraints(accessed);
        let mut instantiations = Substitution::default();
        if !self.context.types.match_type(body, accessed, &names, &mut instantiations) {
            return Ok(None);
        }
        Ok(Some((closed, instantiations)))
    }

    fn record_field_type(&self, record: TypeId, label: &str) -> Option<TypeId> {
        let (_, arguments) = self.context.types.spine(record);
        let [row] = arguments[..] else {
            return None;
        };
        let row = self.context.types.strip_annotations(row);
        let Type::Row(row) = self.context.types.lookup(row) else {
            return None;
        };
        let row = self.context.queries.lookup_row_type(*row);
        row.fields.iter().find(|field| field.label == label).map(|field| field.id)
    }

    pub(super) fn evidence_redex(
        &mut self,
        scope: &mut Scope,
        abstraction: tree::ExpressionId,
        dictionaries: Vec<Dictionary>,
    ) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let tree = &module.checked.tree;
        let mut binders = Vec::with_capacity(dictionaries.len());
        let mut body = abstraction;
        while binders.len() < dictionaries.len()
            && let tree::ExpressionKind::EvidenceAbstraction { binder, expression } =
                tree[body].kind
        {
            binders.push(binder);
            body = expression;
        }
        if binders.len() != dictionaries.len() {
            return Err(self.unsupported(
                scope,
                UnsupportedState::Construct { construct: "evidence applied to a non-reference" },
            ));
        }
        let previous: Vec<_> = binders
            .iter()
            .zip(dictionaries)
            .map(|(&binder, dictionary)| (binder, scope.givens.insert(binder, dictionary)))
            .collect();
        let reduced = self.expression(scope, body);
        for (binder, given) in previous {
            match given {
                Some(dictionary) => scope.givens.insert(binder, dictionary),
                None => scope.givens.remove(&binder),
            };
        }
        reduced
    }

    pub(super) fn local_form(
        &self,
        scope: &Scope,
        declaration: &tree::LocalDeclaration,
    ) -> GoResult<LocalForm> {
        let abstracted = declaration
            .value
            .abstractions
            .iter()
            .any(|abstraction| !matches!(abstraction, DeclarationAbstraction::Argument));
        if abstracted {
            return Ok(LocalForm::Polymorphic);
        }
        let (names, inner) = self.context.types.peel_quantifiers(declaration.type_id);
        let (constraints, _) = self.context.types.peel_constraints(inner);
        if names.is_empty() && constraints.is_empty() {
            return Ok(LocalForm::Monomorphic);
        }
        if let [equation] = declaration.value.equations.as_ref()
            && equation.binders.is_empty()
            && let [alternative] = equation.guarded_expression.alternatives.as_ref()
            && alternative.pattern_guards.is_empty()
            && alternative.where_expression.bindings.chunks.is_empty()
        {
            return Ok(LocalForm::Alias(alternative.where_expression.expression));
        }
        Err(self.unsupported(
            scope,
            UnsupportedState::Construct { construct: "inferred polymorphic local bindings" },
        ))
    }

    fn polymorphic_local_reference(
        &mut self,
        scope: &mut Scope,
        source: lowering::LetBindingNameGroupId,
        instantiations: &Substitution,
        dictionaries: Vec<Dictionary>,
    ) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let declaration = &module.checked.tree[scope.polymorphic_locals[&source].declaration];
        let requested =
            self.abstraction_types(scope, &declaration.value.abstractions, instantiations)?;
        let mut substitution = scope.substitution.clone();
        substitution.extend(instantiations.iter().map(|(&name, &type_id)| (name, type_id)));
        let requested_monotype =
            self.declared_monotype(scope, declaration.type_id, &substitution)?;
        let types = self.terminate_local_growth(&scope.polymorphic_locals[&source], &requested);
        for (name, (&requested, &terminated)) in self
            .abstraction_names(&declaration.value.abstractions)
            .into_iter()
            .zip(requested.iter().zip(types.iter()))
        {
            if requested != terminated {
                substitution.insert(name, terminated);
            }
        }
        let name = scope.polymorphic_locals[&source].name.clone();
        let dictionaries = self.promote_growing_local_evidence(
            scope,
            &name,
            &declaration.value.abstractions,
            (&requested, &types),
            dictionaries,
        )?;
        let types: Arc<[TypeId]> = Arc::from(types);
        let (dictionaries, runtime_values) = self::runtime::detach_runtime_values(&dictionaries);
        let dictionaries: Arc<[Dictionary]> = Arc::from(dictionaries);
        let canonical = self.types_without_causes(&types);
        let existing =
            scope.polymorphic_locals[&source].specializations.iter().find(|specialization| {
                self.types_without_causes(&specialization.types) == canonical
                    && specialization.dictionaries == dictionaries
            });
        if let Some(specialization) = existing {
            let local = &specialization.local;
            let expression = Expression::new(ExpressionKind::Local(local.id), local.monotype);
            let expression = self.applied_local(expression, runtime_values);
            return Ok(self.coerce(expression, requested_monotype));
        }
        let mut monotype = self.declared_monotype(scope, declaration.type_id, &substitution)?;
        for value in runtime_values.iter().rev() {
            monotype = self.monotypes.function(value.monotype, monotype);
        }
        let polymorphic = scope
            .polymorphic_locals
            .get_mut(&source)
            .expect("invariant violated: polymorphic local is in scope");
        let local = self.fresh_local(polymorphic.name.clone(), monotype);
        let expression = Expression::new(ExpressionKind::Local(local.id), monotype);
        let requester = polymorphic.active;
        polymorphic.specializations.push(LocalSpecialization {
            types,
            dictionaries,
            local,
            value: None,
            requester,
        });
        let expression = self.applied_local(expression, runtime_values);
        Ok(self.coerce(expression, requested_monotype))
    }

    /// A local specialization applied to the run-time dictionaries it takes first.
    fn applied_local(&mut self, local: Expression, arguments: Vec<Expression>) -> Expression {
        if arguments.is_empty() {
            return local;
        }
        let mut monotype = local.monotype;
        for _ in &arguments {
            monotype = self.monotypes.result_after(monotype, 1);
        }
        let kind = ExpressionKind::Apply { function: Box::new(local), arguments };
        Expression::new(kind, monotype)
    }

    fn abstraction_names(&self, abstractions: &[DeclarationAbstraction]) -> Vec<Name> {
        let names = abstractions.iter().filter_map(|abstraction| match abstraction {
            DeclarationAbstraction::Type { binder, .. } => {
                Some(self.context.queries.lookup_forall_binder(*binder).name)
            }
            _ => None,
        });
        names.collect()
    }

    pub(super) fn specialize_polymorphic_locals(
        &mut self,
        scope: &mut Scope,
        sources: &[lowering::LetBindingNameGroupId],
    ) -> GoResult<()> {
        let module = Arc::clone(&scope.module);
        loop {
            let pending = sources.iter().find_map(|&source| {
                let specializations = &scope.polymorphic_locals[&source].specializations;
                let index = specializations
                    .iter()
                    .position(|specialization| specialization.value.is_none())?;
                Some((source, index))
            });
            let Some((source, index)) = pending else {
                return Ok(());
            };
            let polymorphic = &scope.polymorphic_locals[&source];
            if polymorphic.specializations.len() > LOCAL_SPECIALIZATION_LIMIT {
                return Err(self.unsupported(
                    scope,
                    UnsupportedState::SpecializationLimit { limit: LOCAL_SPECIALIZATION_LIMIT },
                ));
            }
            let value = &module.checked.tree[polymorphic.declaration].value;
            let specialization = &polymorphic.specializations[index];
            let types = Arc::clone(&specialization.types);
            let dictionaries = Arc::clone(&specialization.dictionaries);
            let substitution = scope.substitution.clone();
            let givens = scope.givens.clone();
            let active = scope
                .polymorphic_locals
                .get_mut(&source)
                .map(|polymorphic| polymorphic.active.replace(index));
            let specialized = self
                .bind_local_runtime_dictionaries(&scope.definition, &dictionaries)
                .and_then(|(dictionaries, parameters)| {
                    self.bind_abstractions(scope, &value.abstractions, &types, &dictionaries)?;
                    let body = self.equations(scope, &value.equations)?;
                    Ok(match parameters.is_empty() {
                        true => body,
                        false => self.lambda(parameters, body),
                    })
                });
            scope.substitution = substitution;
            scope.givens = givens;
            let polymorphic = scope
                .polymorphic_locals
                .get_mut(&source)
                .expect("invariant violated: polymorphic local is in scope");
            polymorphic.active = active.flatten();
            polymorphic.specializations[index].value = Some(specialized?);
        }
    }

    pub(super) fn specialized_bindings(
        &mut self,
        scope: &mut Scope,
        source: lowering::LetBindingNameGroupId,
    ) -> Vec<Binding> {
        let polymorphic = scope
            .polymorphic_locals
            .get_mut(&source)
            .expect("invariant violated: polymorphic local is in scope");
        let specializations = std::mem::take(&mut polymorphic.specializations);
        let bindings = specializations.into_iter().map(|specialization| Binding {
            local: specialization.local,
            value: specialization
                .value
                .expect("invariant violated: requested local specialization was never produced"),
        });
        bindings.collect()
    }

    /// Recovers, from the type the reference is checked at, the quantifiers
    /// the checker records no instantiation for: those of a result type, and
    /// those of a declaration referenced from its own recursive binding group,
    /// where the reference is monomorphic until the group is generalized.
    /// A reference checked against an unspecialized `forall` (`measure` passed
    /// as `Algebra`, `forall node ops. ...`) is instantiated at the skolems the
    /// checker introduced for its quantifiers. That `forall` is erased, so its
    /// skolems are too, and the reference is specialized at the erased type the
    /// parameter has.
    fn erase_rank_n_skolems(
        &mut self,
        scope: &Scope,
        checked: TypeId,
        instantiations: &mut Substitution,
    ) -> GoResult<()> {
        let checked = self.context.types.substitute(checked, &scope.substitution);
        let checked = crate::monotype::expand_synonyms(&mut self.context, checked)?;
        let checked = self.context.types.strip_annotations(checked);
        if !matches!(self.context.types.lookup(checked), Type::Forall(..)) {
            return Ok(());
        }
        if self.monotypes.scheme_for(&mut self.context, checked)?.is_some() {
            return Ok(());
        }
        let mut skolems = vec![];
        for &argument in instantiations.values() {
            self.context.types.rigid_names(argument, &mut skolems);
        }
        let accumulator = match rank_n_scheme(&mut self.context, checked)? {
            Some(scheme) => self.monotypes.schemes.accumulator(&scheme.key),
            None => None,
        };
        let erased = accumulator.unwrap_or_else(|| self.context.types.erased(Erasure::RankN));
        let skolems: Substitution = skolems
            .into_iter()
            .filter(|name| !scope.substitution.contains_key(name))
            .filter(|&name| self.context.types.name_erasure(name).is_none())
            .filter(|&name| !self.context.types.is_cons_list_name(name))
            .map(|name| (name, erased))
            .collect();
        for argument in instantiations.values_mut() {
            *argument = self.context.types.substitute(*argument, &skolems);
        }
        Ok(())
    }

    fn recover_unrecorded_instantiations(
        &mut self,
        scope: &Scope,
        checked: TypeId,
        file_id: FileId,
        term: TermItemId,
        instantiations: &mut Substitution,
    ) -> GoResult<()> {
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else {
            return Ok(());
        };
        let mut uninstantiated = vec![];
        let declared = self.outer_body(declared, &mut uninstantiated);
        let declared = self.strip_instantiated_result_quantifiers(declared, instantiations)?;
        let declared = self.context.types.substitute(declared, instantiations);
        let pattern = self.strip_inner_quantifiers(declared, &mut uninstantiated)?;
        uninstantiated.retain(|name| !instantiations.contains_key(name));
        if uninstantiated.is_empty() {
            return Ok(());
        }
        let checked = self.context.types.substitute(checked, &scope.substitution);
        let checked = self.strip_inner_quantifiers(checked, &mut vec![])?;
        let mut bindings = Substitution::default();
        if self.context.types.match_type(pattern, checked, &uninstantiated, &mut bindings) {
            instantiations.extend(bindings);
        }
        Ok(())
    }
}
