use building_types::QueryResult;
use rustc_hash::FxHashSet;

use crate::context::CheckContext;
use crate::core::Type;
use crate::error::{ErrorCrumb, ErrorKind};
use crate::evidence::{Evidence, EvidenceState, InstanceCandidateOrigin};
use crate::state::CheckState;
use crate::{ExternalQueries, tree};

use super::{DeriveHeadResult, DeriveStrategy, field, generate, tools, variance};

pub fn check_derive_members<Q>(
    state: &mut CheckState,
    context: &CheckContext<Q>,
    derives: &[DeriveHeadResult],
) -> QueryResult<()>
where
    Q: ExternalQueries,
{
    for result in derives {
        state.with_error_crumb(ErrorCrumb::DeriveDeclaration(result.item_id), |state| {
            state.with_implication(|state| check_derive_member(state, context, result))
        })?;
    }
    Ok(())
}

fn check_derive_member<Q>(
    state: &mut CheckState,
    context: &CheckContext<Q>,
    result: &DeriveHeadResult,
) -> QueryResult<()>
where
    Q: ExternalQueries,
{
    for &constraint in &result.constraints {
        state.push_given(constraint);
    }

    let mut variance_recipe = None;
    match result.strategy {
        DeriveStrategy::FieldConstraints { data_file, data_id, derived_type, class } => {
            tools::emit_superclass_constraints(
                state,
                context,
                result.class_file,
                result.class_id,
                &result.arguments,
            )?;
            field::generate_field_constraints(
                state,
                context,
                data_file,
                data_id,
                derived_type,
                class,
            )?;
        }
        DeriveStrategy::DelegateConstraint { derived_type, class } => {
            tools::emit_superclass_constraints(
                state,
                context,
                result.class_file,
                result.class_id,
                &result.arguments,
            )?;
            generate_delegate_constraint(state, context, derived_type, class);
        }
        DeriveStrategy::NewtypeDeriveConstraint { delegate_constraint } => {
            state.push_wanted(delegate_constraint);
        }
        DeriveStrategy::NewtypeClass | DeriveStrategy::Generic { .. } => {
            tools::emit_superclass_constraints(
                state,
                context,
                result.class_file,
                result.class_id,
                &result.arguments,
            )?;
        }
        DeriveStrategy::VarianceConstraints { data_file, data_id, derived_type, config } => {
            tools::emit_superclass_constraints(
                state,
                context,
                result.class_file,
                result.class_id,
                &result.arguments,
            )?;
            let recipe = variance::generate_variance_constraints(
                state,
                context,
                data_file,
                data_id,
                derived_type,
                config,
                &result.constraints,
            )?;
            variance_recipe = recipe.valid.then_some(recipe);
        }
    }

    if let tools::ConstraintReport::Solved = tools::solve_and_report_constraints(state, context)? {
        let declaration =
            generate::generate_instance(state, context, result, variance_recipe.as_ref())?;
        if let tools::ConstraintReport::Solved =
            tools::solve_and_report_constraints(state, context)?
            && let Some(declaration) = declaration
        {
            if delegates_to_itself(state, context, result, &declaration) {
                state.insert_error(ErrorKind::DeriveNewtypeCycle);
            }
            state.checked.tree.insert_derive(result.item_id, declaration);
        }
    }

    Ok(())
}

fn delegates_to_itself<Q>(
    state: &CheckState,
    context: &CheckContext<Q>,
    result: &DeriveHeadResult,
    declaration: &tree::TermDeclaration,
) -> bool
where
    Q: ExternalQueries,
{
    let tree::TermDeclarationKind::Instance(instance) = &declaration.kind else {
        return false;
    };
    let tree::InstanceImplementation::Delegate { evidence, .. } = instance.implementation else {
        return false;
    };
    if !instance.evidences.is_empty() {
        return false;
    }

    let itself = InstanceCandidateOrigin::Derive(context.id, result.derive_id);
    let evidences = &state.checked.evidence;
    let mut seen = FxHashSet::default();
    let mut pending_variables = vec![evidence];
    let mut pending_proofs = vec![];

    loop {
        if let Some(variable) = pending_variables.pop() {
            if seen.insert(variable)
                && let EvidenceState::Solved(proof) = evidences[variable].state
            {
                pending_proofs.push(proof);
            }
            continue;
        }
        let Some(proof) = pending_proofs.pop() else {
            return false;
        };
        match &evidences[proof] {
            Evidence::Instance { origin, .. } if *origin == itself => return true,
            Evidence::Instance { subgoals, .. } => pending_variables.extend(subgoals),
            Evidence::Variable(variable) => pending_variables.push(*variable),
            Evidence::Superclass { parent, .. } => pending_proofs.push(*parent),
            Evidence::Given(_) | Evidence::Trivial | Evidence::Synthesized(_) => {}
        }
    }
}

fn generate_delegate_constraint<Q>(
    state: &mut CheckState,
    context: &CheckContext<Q>,
    derived_type: crate::core::TypeId,
    class: (files::FileId, indexing::TypeItemId),
) where
    Q: ExternalQueries,
{
    let skolem_type = state.fresh_rigid(context.queries, context.prim.t);
    let applied_type = context.intern_application(derived_type, skolem_type);

    let class_type = context.queries.intern_type(Type::Constructor(class.0, class.1));
    let given_constraint = context.intern_application(class_type, skolem_type);
    let wanted_constraint = context.intern_application(class_type, applied_type);

    state.push_given(given_constraint);
    state.push_wanted(wanted_constraint);
}
