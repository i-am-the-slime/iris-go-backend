use std::sync::Arc;

use checking::core::Type;
use checking::{TypeId, tree};
use smol_str::{SmolStr, format_smolstr};

use super::{
    IgnoringCallee, Scope, Specializer, case_branch_position, is_foreign_wrapper,
    is_written_lambda, source_position, spine, string_literal,
};
use crate::dictionary::Dictionary;
use crate::error::{GoResult, UnsupportedState};
use crate::foreign::Foreign;
use crate::mono::{Alternative, Expression, ExpressionKind, Guarded, Literal, Local, RecordUpdate};
use crate::monotype::{Monotype, MonotypeId};
use crate::types::Substitution;

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn expression(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
    ) -> GoResult<Expression> {
        let result = self.translate_expression(scope, id);
        if result.is_ok() {
            return result;
        }
        let monotype = self.monotype(scope, scope.module.checked.tree[id].type_id);
        match monotype {
            Ok(monotype) => self.recover(result, monotype),
            Err(error) => {
                self.record(result.expect_err("invariant violated: result is an error"))?;
                Err(error)
            }
        }
    }

    fn translate_expression(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
    ) -> GoResult<Expression> {
        if let Some(constructed) = self.rank_n_construction(scope, id)? {
            return Ok(constructed);
        }
        self.translate_expression_at(scope, id)
    }

    /// An expression checked against an unconstrained `forall` (a CPS parser
    /// passed to its constructor, say) becomes one specialization per
    /// instantiation of the quantified variables, as a record of them.
    fn rank_n_construction(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
    ) -> GoResult<Option<Expression>> {
        if scope.rank_n_body == Some(id) {
            return Ok(None);
        }
        let type_id = scope.module.checked.tree[id].type_id;
        let closed = self.context.types.substitute(type_id, &scope.substitution);
        let closed = self.instantiate_inner_quantifiers(scope, id, closed);
        if !matches!(
            self.context.types.lookup(self.context.types.strip_annotations(closed)),
            Type::Forall(..)
        ) {
            return Ok(None);
        }
        let Some(scheme) = self.monotypes.scheme_for(&mut self.context, closed)? else {
            return self.grown_construction(scope, id, closed);
        };
        // Checking against a `forall` binds scoped skolems; a polymorphic
        // reference's own quantifiers are instantiated where it is used.
        if !scheme.constraints.is_empty()
            || scheme.names.iter().any(|name| !name.scoped || scope.substitution.contains_key(name))
        {
            return Ok(None);
        }
        let monotype = self.closed_monotype(scope, closed)?;
        self.note_construction(&scheme.key);
        let instantiations = self.monotypes.schemes.get(&scheme.key).to_vec();
        let mut fields = Vec::with_capacity(instantiations.len());
        let enclosing = scope.rank_n_body.replace(id);
        for instantiation in instantiations {
            let substitution = scope.substitution.clone();
            scope
                .substitution
                .extend(scheme.names.iter().copied().zip(instantiation.types.iter().copied()));
            self.constructing.push((scheme.key.clone(), Arc::clone(&instantiation.types)));
            let value = self.translate_expression_at(scope, id);
            self.constructing.pop();
            scope.substitution = substitution;
            match value {
                Ok(value) => fields.push((instantiation.label, value)),
                Err(error) => {
                    scope.rank_n_body = enclosing;
                    return Err(error);
                }
            }
        }
        scope.rank_n_body = enclosing;
        fields.sort_by(|left, right| left.0.cmp(&right.0));
        Ok(Some(Expression::new(ExpressionKind::Record(fields), monotype)))
    }

    /// A polymorphic reference checked against a `forall` has the type
    /// `forall sk. <its own forall a. ...>`; its own quantifiers are
    /// instantiated in terms of the skolems where it is used, as the tree
    /// records, which leaves the rank-N type it is checked against.
    fn instantiate_inner_quantifiers(
        &mut self,
        scope: &Scope,
        id: tree::ExpressionId,
        closed: TypeId,
    ) -> TypeId {
        let stripped = self.context.types.strip_annotations(closed);
        let Type::Forall(binder, inner) = self.context.types.lookup(stripped).clone() else {
            return closed;
        };
        if !self.context.queries.lookup_forall_binder(binder).name.scoped {
            return closed;
        }
        let rest = self.instantiate_inner_quantifiers(scope, id, inner);
        let (names, body) = self.context.types.peel_quantifiers(rest);
        if names.iter().all(|name| name.scoped) || names.is_empty() {
            return self.context.queries.intern_type(Type::Forall(binder, rest));
        }
        let instantiations = self.recorded_instantiations(scope, id);
        if !names.iter().all(|name| instantiations.contains_key(name)) {
            return closed;
        }
        let (_, body) = self.context.types.peel_constraints(body);
        let body = self.context.types.substitute(body, &instantiations);
        self.context.queries.intern_type(Type::Forall(binder, body))
    }

    pub(super) fn translate_expression_at(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
    ) -> GoResult<Expression> {
        let translated = self.translate_node(scope, id)?;
        Ok(translated.located(source_position(&scope.module, id)))
    }

    fn translate_node(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
    ) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let node = &module.checked.tree[id];
        let kind = match &node.kind {
            tree::ExpressionKind::Error => {
                return Err(self.unsupported(scope, UnsupportedState::ExpressionError));
            }
            tree::ExpressionKind::String { value, .. } => {
                ExpressionKind::Literal(string_literal(value))
            }
            tree::ExpressionKind::Char { value } => ExpressionKind::Literal(Literal::Char(*value)),
            tree::ExpressionKind::Boolean { value } => {
                ExpressionKind::Literal(Literal::Boolean(*value))
            }
            tree::ExpressionKind::Integer { value } => {
                let monotype = self.monotype(scope, node.type_id)?;
                if let Monotype::Number = self.monotypes.get(monotype) {
                    let value = format_smolstr!("{value}");
                    return Ok(Expression::new(
                        ExpressionKind::Literal(Literal::Number(value)),
                        monotype,
                    ));
                }
                ExpressionKind::Literal(Literal::Int(*value))
            }
            tree::ExpressionKind::Number { value } => {
                ExpressionKind::Literal(Literal::Number(value.clone()))
            }
            tree::ExpressionKind::Array { elements } => {
                let mut converted = Vec::with_capacity(elements.len());
                for &element in elements.iter() {
                    converted.push(self.expression(scope, element)?);
                }
                ExpressionKind::Array(converted)
            }
            tree::ExpressionKind::Record { fields } => {
                let mut converted = Vec::with_capacity(fields.len());
                for field in fields.iter() {
                    let (label, expression) = match field {
                        tree::RecordExpressionField::Field { label, expression }
                        | tree::RecordExpressionField::Pun { label, expression, .. } => {
                            (label, expression)
                        }
                    };
                    converted.push((label.clone(), self.expression(scope, *expression)?));
                }
                ExpressionKind::Record(converted)
            }
            tree::ExpressionKind::RecordAccess { record, labels } => {
                let mut record = self.expression(scope, *record)?;
                for label in labels.iter() {
                    let monotype = self.field_monotype(scope, record.monotype, label)?;
                    let kind =
                        ExpressionKind::Access { record: Box::new(record), label: label.clone() };
                    record = Expression::new(kind, monotype);
                }
                return Ok(record);
            }
            tree::ExpressionKind::RecordUpdate { record, updates } => {
                let record = self.expression(scope, *record)?;
                let updates = self.record_updates(scope, updates)?;
                ExpressionKind::Update { record: Box::new(record), updates }
            }
            tree::ExpressionKind::Constructor { .. }
            | tree::ExpressionKind::Variable { .. }
            | tree::ExpressionKind::RecordPun { .. }
            | tree::ExpressionKind::EvidenceApplication { .. } => {
                return self.reference(scope, id, Substitution::default(), None);
            }
            tree::ExpressionKind::Section { binder } => {
                return self.local_reference(scope, self.checked_binder_source(scope, *binder));
            }
            tree::ExpressionKind::TermApplication { .. } => return self.application(scope, id),
            tree::ExpressionKind::EvidenceAbstraction { binder, expression } => {
                let constraint = module.checked.evidence[*binder].constraint;
                if crate::monotype::is_partial(&mut self.context, constraint)? {
                    scope.givens.insert(*binder, Dictionary::Trivial);
                    return self.expression(scope, *expression);
                }
                return self.scheme_construction(scope, id);
            }
            tree::ExpressionKind::Lambda { binders, expression } => {
                if let Some(parameters) = self.variable_parameters(scope, binders)? {
                    if is_written_lambda(&module, node)
                        && let [parameter] = parameters.as_slice()
                        && matches!(self.monotypes.get(parameter.monotype), Monotype::Unit)
                    {
                        self.thunk_parameters.insert(parameter.id);
                    }
                    let body = self.expression(scope, *expression)?;
                    return Ok(self.lambda(parameters, body));
                }
                let mut parameters = Vec::with_capacity(binders.len());
                let mut patterns = Vec::with_capacity(binders.len());
                for &binder in binders.iter() {
                    let pattern = self.pattern(scope, binder)?;
                    let name = self.parameter_name(scope, [binder], pattern.monotype);
                    parameters.push(self.fresh_local(name, pattern.monotype));
                    patterns.push(pattern);
                }
                let body = self.expression(scope, *expression)?;
                let monotype = body.monotype;
                let scrutinees: Vec<Expression> =
                    parameters.iter().map(Local::expression).collect();
                let body = Guarded::Unconditional(body);
                let position = source_position(&module, id);
                let alternative = Alternative { patterns, body, position };
                let mut alternatives = vec![alternative];
                if !module.checked.tree.is_exhaustive_match(tree::PatternMatch::Expression(id)) {
                    alternatives.push(Alternative::match_failure(&scrutinees, monotype));
                }
                let kind = ExpressionKind::Case { scrutinees, alternatives };
                let body = Expression::new(kind, monotype);
                return Ok(self.lambda(parameters, body));
            }
            tree::ExpressionKind::IfThenElse { condition, then, else_ } => ExpressionKind::If {
                condition: Box::new(self.expression(scope, *condition)?),
                then: Box::new(self.expression(scope, *then)?),
                otherwise: Box::new(self.expression(scope, *else_)?),
            },
            tree::ExpressionKind::Case { scrutinees, alternatives } => {
                let mut converted_scrutinees = Vec::with_capacity(scrutinees.len());
                for &scrutinee in scrutinees.iter() {
                    converted_scrutinees.push(self.expression(scope, scrutinee)?);
                }
                let mut converted = Vec::with_capacity(alternatives.len());
                for alternative in alternatives.iter() {
                    let mut patterns = Vec::with_capacity(alternative.binders.len());
                    for &binder in alternative.binders.iter() {
                        patterns.push(self.pattern(scope, binder)?);
                    }
                    let body = self.guarded(scope, &alternative.guarded_expression)?;
                    let position = case_branch_position(&module, alternative.source);
                    converted.push(Alternative { patterns, body, position });
                }
                if !module.checked.tree.is_exhaustive_match(tree::PatternMatch::Expression(id)) {
                    let monotype = self.monotype(scope, node.type_id)?;
                    converted.push(Alternative::match_failure(&converted_scrutinees, monotype));
                }
                ExpressionKind::Case { scrutinees: converted_scrutinees, alternatives: converted }
            }
            tree::ExpressionKind::Let { bindings, expression } => {
                return self.let_bindings(scope, bindings, *expression);
            }
        };
        let monotype = self.monotype(scope, node.type_id)?;
        Ok(Expression::new(kind, monotype))
    }

    pub(super) fn field_monotype(
        &mut self,
        scope: &Scope,
        record: MonotypeId,
        label: &str,
    ) -> GoResult<MonotypeId> {
        if let Monotype::Record(fields) = self.monotypes.get(record)
            && let Some(field) = fields.iter().find(|field| field.label == label)
        {
            return Ok(field.monotype);
        }
        Err(self
            .unsupported(scope, UnsupportedState::OpenType { rendered: format!("{{ {label} }}") }))
    }

    fn record_updates(
        &mut self,
        scope: &mut Scope,
        updates: &[tree::RecordExpressionUpdate],
    ) -> GoResult<Vec<RecordUpdate>> {
        let mut converted = Vec::with_capacity(updates.len());
        for update in updates {
            converted.push(match update {
                tree::RecordExpressionUpdate::Leaf { label, expression } => RecordUpdate::Leaf {
                    label: label.clone(),
                    value: self.expression(scope, *expression)?,
                },
                tree::RecordExpressionUpdate::Branch { label, updates } => RecordUpdate::Branch {
                    label: label.clone(),
                    updates: self.record_updates(scope, updates)?,
                },
                tree::RecordExpressionUpdate::Error => {
                    return Err(self.unsupported(scope, UnsupportedState::ExpressionError));
                }
            });
        }
        Ok(converted)
    }

    pub(super) fn application(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
    ) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let spine::ApplicationSpine { head, arguments, trailing: evidence, instantiations } =
            self.application_spine(scope, id);
        let mut result_instantiations = instantiations;
        self.context.types.close(&mut result_instantiations);
        let monotype = self.instantiated_result_monotype(
            scope,
            module.checked.tree[id].type_id,
            &result_instantiations,
        )?;
        let trailing = self.trailing_dictionaries(scope, &evidence)?;
        if let tree::ExpressionKind::Constructor { resolution } = module.checked.tree[head].kind
            && trailing.is_empty()
            && self.is_newtype_constructor(resolution)?
            && let [argument] = arguments[..]
        {
            let mut argument = self.expression(scope, argument)?;
            if matches!(self.monotypes.get(monotype), Monotype::Recursive(_)) {
                return Ok(argument);
            }
            if self.mentions_erased(monotype) {
                return Ok(self.coerce(argument, monotype));
            }
            argument.monotype = monotype;
            return Ok(argument);
        }
        if !trailing.is_empty()
            && let [argument] = arguments[..]
            && self.is_unsafe_coerce(scope, head)?
        {
            let result = module.checked.tree[id].type_id;
            let result = self.context.types.substitute(result, &scope.substitution);
            let result = (result, monotype);
            return self.coerced_with_evidence(scope, argument, &evidence, trailing, result);
        }
        if trailing.is_empty()
            && let Some(reference) = self.traversal_reference(scope, head, &arguments)?
        {
            return self.traverse_array(scope, reference, &arguments);
        }
        let head_type = self.instantiated_node_type(scope, head, &result_instantiations);
        let function = match module.checked.tree[head].kind {
            tree::ExpressionKind::Constructor { .. }
            | tree::ExpressionKind::Variable { .. }
            | tree::ExpressionKind::RecordPun { .. }
            | tree::ExpressionKind::EvidenceApplication { .. } => {
                self.trailed_reference(scope, head, result_instantiations.clone(), None, trailing)
            }
            _ if trailing.is_empty() => self.expression(scope, head),
            _ => Err(self.unsupported(
                scope,
                UnsupportedState::Construct { construct: "evidence applied to a non-reference" },
            )),
        };
        let mut function = match function {
            Ok(function) => function,
            Err(error) => {
                self.record(error)?;
                for argument in arguments {
                    self.expression(scope, argument)?;
                }
                let blocked = SmolStr::new_static("blocked");
                return Ok(Expression::new(ExpressionKind::Fail(blocked), monotype));
            }
        };
        let mut parameter_type = head_type;
        let mut callee = IgnoringCallee::of(&function, 0);
        let mut converted = Vec::with_capacity(arguments.len());
        for (position, argument) in arguments.into_iter().enumerate() {
            let expected = self.next_parameter_type(parameter_type, &result_instantiations)?;
            if let Some((_, result)) = expected {
                parameter_type = result;
            }
            if let Some(parameter) = callee.ignores(&self.monotypes, position) {
                let ignored = SmolStr::new_static("ignored foreign argument");
                converted.push(Expression::new(ExpressionKind::Fail(ignored), parameter));
                continue;
            }
            let converted_argument = match (&module.checked.tree[argument].kind, expected) {
                (
                    tree::ExpressionKind::Variable { .. }
                    | tree::ExpressionKind::EvidenceApplication { .. },
                    Some((expected, _)),
                ) if !self.is_continuation(scope, expected)? => {
                    self.reference(scope, argument, Substitution::default(), Some(expected))?
                }
                _ => self.expression(scope, argument)?,
            };
            if position == 0 && is_foreign_wrapper(&function, Foreign::Identity) {
                callee = IgnoringCallee::of(&converted_argument, 1);
            }
            converted.push(converted_argument);
        }
        if let Monotype::Erased(_) = self.monotypes.get(function.monotype) {
            let mut expected = monotype;
            for argument in converted.iter().rev() {
                expected = self.monotypes.function(argument.monotype, expected);
            }
            function = self.coerce(function, expected);
        }
        let mut result = function.monotype;
        let mut coerced = Vec::with_capacity(converted.len());
        for argument in converted {
            match self.monotypes.function_parts(result) {
                Some((parameter, rest)) => {
                    coerced.push(self.coerce(argument, parameter));
                    result = rest;
                }
                None => coerced.push(argument),
            }
        }
        let kind = ExpressionKind::Apply { function: Box::new(function), arguments: coerced };
        if result != monotype && self.mentions_erased(result) {
            let applied = Expression::new(kind, result);
            return Ok(self.coerce(applied, monotype));
        }
        Ok(Expression::new(kind, monotype))
    }
}
