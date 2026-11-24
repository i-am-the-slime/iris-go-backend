use std::sync::Arc;

use checking::tree;
use smol_str::SmolStr;

use super::{
    LocalForm, LocalSource, PolymorphicLocal, Scope, Specializer, alternatives_monotype,
    equation_position,
};
use crate::error::{GoResult, UnsupportedState};
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Guard, Guarded, GuardedBranch, Local,
    Pattern, PatternKind,
};
use crate::monotype::MonotypeId;

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// The function the equations define, its body written where the first equation is.
    pub(super) fn equations(
        &mut self,
        scope: &mut Scope,
        equations: &[tree::Equation],
    ) -> GoResult<Expression> {
        let position =
            equations.first().and_then(|first| equation_position(&scope.module, first.source));
        let mut function = self.equation_function(scope, equations)?;
        if let ExpressionKind::Lambda { body, .. } = &mut function.kind {
            body.position = body.position.or(position);
        }
        Ok(function.located(position))
    }

    fn equation_function(
        &mut self,
        scope: &mut Scope,
        equations: &[tree::Equation],
    ) -> GoResult<Expression> {
        let Some(first) = equations.first() else {
            return Err(self.unsupported(scope, UnsupportedState::MissingEquation));
        };
        let pattern_match = tree::PatternMatch::Equations(first.source);
        let exhaustive = scope.module.checked.tree.is_exhaustive_match(pattern_match);
        let arity = equations.iter().map(|equation| equation.binders.len()).max().unwrap_or(0);
        if arity == 0 {
            return self.guarded_expression(scope, &first.guarded_expression, exhaustive);
        }
        if let [equation] = equations
            && let Some(parameters) = self.variable_parameters(scope, &equation.binders)?
        {
            let body = self.guarded_expression(scope, &equation.guarded_expression, exhaustive)?;
            return Ok(self.lambda(parameters, body));
        }
        let mut parameters = Vec::with_capacity(arity);
        for position in 0..arity {
            let binder = equations
                .iter()
                .find_map(|equation| equation.binders.get(position))
                .copied()
                .expect("invariant violated: arity is the maximum binder count");
            let monotype =
                self.binder_monotype(scope, scope.module.checked.tree[binder].type_id)?;
            let binders = equations.iter().filter_map(|equation| equation.binders.get(position));
            let name = self.parameter_name(scope, binders.copied(), monotype);
            parameters.push(self.fresh_local(name, monotype));
        }
        let mut alternatives = Vec::with_capacity(equations.len());
        for equation in equations {
            let mut patterns = Vec::with_capacity(arity);
            for &binder in equation.binders.iter() {
                patterns.push(self.pattern(scope, binder)?);
            }
            for parameter in &parameters[patterns.len()..] {
                patterns
                    .push(Pattern { kind: PatternKind::Wildcard, monotype: parameter.monotype });
            }
            let body = self.guarded(scope, &equation.guarded_expression)?;
            let position = equation_position(&scope.module, equation.source);
            alternatives.push(Alternative { patterns, body, position });
        }
        let scrutinees: Vec<Expression> = parameters.iter().map(Local::expression).collect();
        let monotype = alternatives_monotype(&alternatives);
        if !exhaustive {
            alternatives.push(Alternative::match_failure(&scrutinees, monotype));
        }
        let body = Expression::new(ExpressionKind::Case { scrutinees, alternatives }, monotype);
        Ok(self.lambda(parameters, body))
    }

    /// A parameter that patterns take apart is called by the name a variable
    /// or as-pattern gives it in one of them, else after its type.
    pub(super) fn parameter_name(
        &self,
        scope: &Scope,
        binders: impl IntoIterator<Item = tree::BinderId>,
        monotype: MonotypeId,
    ) -> SmolStr {
        let named = binders.into_iter().find_map(|binder| match self.unwrap_typed(scope, binder) {
            (binder, tree::BinderKind::Variable) => Some(self.binder_name(scope, binder)),
            (_, tree::BinderKind::Named { name, .. }) => Some(name.clone()),
            _ => None,
        });
        named.unwrap_or_else(|| self.monotypes.value_name(monotype))
    }

    pub(super) fn variable_parameters(
        &mut self,
        scope: &mut Scope,
        binders: &[tree::BinderId],
    ) -> GoResult<Option<Vec<Local>>> {
        let all_variables = binders.iter().all(|&binder| {
            matches!(
                self.unwrap_typed(scope, binder).1,
                tree::BinderKind::Variable | tree::BinderKind::Wildcard
            )
        });
        if !all_variables {
            return Ok(None);
        }
        let mut parameters = Vec::with_capacity(binders.len());
        for &binder in binders {
            let pattern = self.pattern(scope, binder)?;
            let local = match pattern.kind {
                PatternKind::Variable(local) => local,
                PatternKind::Wildcard => {
                    self.fresh_local(SmolStr::new_static("ignored"), pattern.monotype)
                }
                _ => unreachable!(
                    "invariant violated: variable binders convert to variable patterns"
                ),
            };
            parameters.push(local);
        }
        Ok(Some(parameters))
    }

    pub(super) fn unwrap_typed<'s>(
        &self,
        scope: &'s Scope,
        mut binder: tree::BinderId,
    ) -> (tree::BinderId, &'s tree::BinderKind) {
        loop {
            match &scope.module.checked.tree[binder].kind {
                tree::BinderKind::Typed { binder: inner, .. } => binder = *inner,
                kind => return (binder, kind),
            }
        }
    }

    pub(super) fn lambda(&mut self, parameters: Vec<Local>, body: Expression) -> Expression {
        let mut monotype = body.monotype;
        for parameter in parameters.iter().rev() {
            monotype = self.monotypes.function(parameter.monotype, monotype);
        }
        Expression::new(ExpressionKind::Lambda { parameters, body: Box::new(body) }, monotype)
    }

    pub(super) fn guarded(
        &mut self,
        scope: &mut Scope,
        guarded: &tree::GuardedExpression,
    ) -> GoResult<Guarded> {
        if let [alternative] = guarded.alternatives.as_ref()
            && alternative.pattern_guards.is_empty()
        {
            let body = self.where_expression(scope, &alternative.where_expression)?;
            return Ok(Guarded::Unconditional(body));
        }
        let mut branches = Vec::with_capacity(guarded.alternatives.len());
        for alternative in guarded.alternatives.iter() {
            let mut guards = Vec::with_capacity(alternative.pattern_guards.len());
            for guard in alternative.pattern_guards.iter() {
                let guard = match guard {
                    tree::PatternGuard::Boolean { expression } => {
                        Guard::Boolean(self.expression(scope, *expression)?)
                    }
                    tree::PatternGuard::Pattern { binder, expression, .. } => {
                        let value = self.expression(scope, *expression)?;
                        let pattern = self.pattern(scope, *binder)?;
                        Guard::Pattern { pattern, value }
                    }
                };
                guards.push(guard);
            }
            let body = self.where_expression(scope, &alternative.where_expression)?;
            branches.push(GuardedBranch { guards, body });
        }
        Ok(Guarded::Guards(branches))
    }

    fn guarded_expression(
        &mut self,
        scope: &mut Scope,
        guarded: &tree::GuardedExpression,
        exhaustive: bool,
    ) -> GoResult<Expression> {
        match self.guarded(scope, guarded)? {
            Guarded::Unconditional(body) => Ok(body),
            Guarded::Guards(branches) => {
                let monotype = branches[0].body.monotype;
                let body = Guarded::Guards(branches);
                let alternative = Alternative { patterns: vec![], body, position: None };
                let mut alternatives = vec![alternative];
                if !exhaustive {
                    alternatives.push(Alternative::match_failure(&[], monotype));
                }
                let kind = ExpressionKind::Case { scrutinees: vec![], alternatives };
                Ok(Expression::new(kind, monotype))
            }
        }
    }

    fn where_expression(
        &mut self,
        scope: &mut Scope,
        where_expression: &tree::WhereExpression,
    ) -> GoResult<Expression> {
        self.let_bindings(scope, &where_expression.bindings, where_expression.expression)
    }

    pub(super) fn let_bindings(
        &mut self,
        scope: &mut Scope,
        bindings: &tree::LetBindings,
        body: tree::ExpressionId,
    ) -> GoResult<Expression> {
        enum Declared {
            Monomorphic(Local, Arc<[tree::Equation]>),
            Polymorphic(lowering::LetBindingNameGroupId),
        }
        enum Member {
            Monomorphic(Binding),
            Polymorphic(lowering::LetBindingNameGroupId),
        }
        enum Chunk {
            Names(Vec<Vec<Member>>),
            Pattern(Pattern, Expression, bool),
        }
        let module = Arc::clone(&scope.module);
        let mut chunks = Vec::with_capacity(bindings.chunks.len());
        let mut polymorphic = vec![];
        let mut shadowed = vec![];
        for chunk in bindings.chunks.iter() {
            match chunk {
                tree::LetBindingChunk::Pattern { binder, .. }
                    if let tree::BinderKind::Wildcard = module.checked.tree[*binder].kind => {}
                tree::LetBindingChunk::Pattern { binder, where_expression, .. } => {
                    let value = self.where_expression(scope, where_expression)?;
                    let pattern = self.pattern(scope, *binder)?;
                    let pattern_match = tree::PatternMatch::LetPattern(*binder);
                    let exhaustive = module.checked.tree.is_exhaustive_match(pattern_match);
                    chunks.push(Chunk::Pattern(pattern, value, exhaustive));
                }
                tree::LetBindingChunk::PatternError { .. } => {
                    return Err(self.unsupported(scope, UnsupportedState::BinderError));
                }
                tree::LetBindingChunk::Names { groups, .. } => {
                    let mut declarations = vec![];
                    for group in groups.iter() {
                        let mut members = vec![];
                        for &source in group.as_slice() {
                            let Some(declaration_id) = module.checked.tree.lookup_let(source)
                            else {
                                return Err(self.unsupported(
                                    scope,
                                    UnsupportedState::MissingLocalDeclaration,
                                ));
                            };
                            let declaration = &module.checked.tree[declaration_id];
                            let name = module
                                .lowered
                                .tree
                                .get_let_binding_group(source)
                                .name
                                .clone()
                                .unwrap_or_else(|| SmolStr::new_static("binding"));
                            match self.local_form(scope, declaration)? {
                                LocalForm::Monomorphic => {
                                    let monotype = self.monotype(scope, declaration.type_id)?;
                                    let local = self.fresh_local(name, monotype);
                                    scope.locals.insert(LocalSource::Let(source), local.clone());
                                    let equations = Arc::clone(&declaration.value.equations);
                                    members.push(Declared::Monomorphic(local, equations));
                                }
                                LocalForm::Polymorphic => {
                                    let entry = PolymorphicLocal {
                                        name,
                                        declaration: declaration_id,
                                        specializations: vec![],
                                        active: None,
                                    };
                                    let previous = scope.polymorphic_locals.insert(source, entry);
                                    shadowed.push((source, previous));
                                    polymorphic.push(source);
                                    members.push(Declared::Polymorphic(source));
                                }
                                LocalForm::Alias(expression) => {
                                    scope.local_aliases.insert(source, expression);
                                }
                            }
                        }
                        declarations.push(members);
                    }
                    let mut groups = Vec::with_capacity(declarations.len());
                    for members in declarations {
                        let mut converted = Vec::with_capacity(members.len());
                        for member in members {
                            converted.push(match member {
                                Declared::Monomorphic(local, equations) => {
                                    let value = self.equations(scope, &equations);
                                    let value = self.recover(value, local.monotype)?;
                                    Member::Monomorphic(Binding { local, value })
                                }
                                Declared::Polymorphic(source) => Member::Polymorphic(source),
                            });
                        }
                        groups.push(converted);
                    }
                    chunks.push(Chunk::Names(groups));
                }
            }
        }
        let mut body = self.expression(scope, body)?;
        self.specialize_polymorphic_locals(scope, &polymorphic)?;
        for chunk in chunks.into_iter().rev() {
            match chunk {
                Chunk::Names(groups) => {
                    for members in groups.into_iter().rev() {
                        let mut bindings = vec![];
                        for member in members {
                            match member {
                                Member::Monomorphic(binding) => bindings.push(binding),
                                Member::Polymorphic(source) => {
                                    bindings.extend(self.specialized_bindings(scope, source));
                                }
                            }
                        }
                        if bindings.is_empty() {
                            continue;
                        }
                        let monotype = body.monotype;
                        let kind = ExpressionKind::Let { bindings, body: Box::new(body) };
                        body = Expression::new(kind, monotype);
                    }
                }
                Chunk::Pattern(pattern, value, exhaustive) => {
                    let monotype = body.monotype;
                    let alternative = Alternative {
                        patterns: vec![pattern],
                        body: Guarded::Unconditional(body),
                        position: value.position,
                    };
                    let scrutinees = vec![value];
                    let mut alternatives = vec![alternative];
                    if !exhaustive {
                        alternatives.push(Alternative::match_failure(&scrutinees, monotype));
                    }
                    let kind = ExpressionKind::Case { scrutinees, alternatives };
                    body = Expression::new(kind, monotype);
                }
            }
        }
        for (source, previous) in shadowed.into_iter().rev() {
            match previous {
                Some(previous) => scope.polymorphic_locals.insert(source, previous),
                None => scope.polymorphic_locals.remove(&source),
            };
        }
        Ok(body)
    }
}
