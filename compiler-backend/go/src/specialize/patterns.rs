//! A constructor's fields have the representation of its data type's monotype,
//! which erases the arguments of a non-regular data type, while the patterns on
//! them have the types the checker gave them. A field whose pattern expects
//! another representation is bound as stored and matched again, converted, by a
//! pattern guard: `One x _` on a `Sequence Int` binds the erased field and
//! asserts `x` to `Int`.

use std::sync::Arc;

use checking::core::Type;
use checking::{TypeId, tree};
use smol_str::{SmolStr, format_smolstr};

use super::{LocalSource, Scope, Specializer, string_literal};
use crate::error::{GoError, GoResult, UnsupportedState};
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Guard, Guarded, GuardedBranch, Literal,
    Pattern, PatternKind,
};
use crate::monotype::{DataConstructor, DataType, Failure, Monotype, MonotypeId};

impl<Q> Specializer<'_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn match_field_representations(
        &mut self,
        expression: &mut Expression,
    ) -> GoResult<()> {
        if let ExpressionKind::Case { scrutinees, alternatives } = &mut expression.kind {
            self.remove_refuted_alternatives(scrutinees, alternatives, expression.monotype)?;
            for alternative in alternatives {
                self.alternative_field_representations(alternative)?;
            }
        }
        let mut result = Ok(());
        crate::monomorphic::traversal::for_each_child_mut(expression, &mut |child| {
            if result.is_ok() {
                result = self.match_field_representations(child);
            }
        });
        result
    }

    /// Drops the alternatives that match a refuted constructor, such as
    /// `IntValue (a ~ Int)` at `Value String`: no value reaches them, in JS
    /// either, and their bodies coerce between the apart types.
    fn remove_refuted_alternatives(
        &mut self,
        scrutinees: &[Expression],
        alternatives: &mut Vec<Alternative>,
        result: crate::monotype::MonotypeId,
    ) -> GoResult<()> {
        let mut kept = Vec::with_capacity(alternatives.len());
        for alternative in std::mem::take(alternatives) {
            let mut refuted = false;
            for pattern in &alternative.patterns {
                refuted |= self.is_refuted(pattern)?;
            }
            if !refuted {
                kept.push(alternative);
            }
        }
        if kept.is_empty() {
            kept.push(Alternative::match_failure(scrutinees, result));
        }
        *alternatives = kept;
        Ok(())
    }

    /// Whether a pattern matches a refuted constructor anywhere inside it.
    fn is_refuted(&mut self, pattern: &Pattern) -> GoResult<bool> {
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Variable(_) | PatternKind::Literal(_) => Ok(false),
            PatternKind::Named { pattern, .. } => self.is_refuted(pattern),
            PatternKind::Array(elements) | PatternKind::Closure { captures: elements, .. } => {
                for element in elements {
                    if self.is_refuted(element)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            PatternKind::Record(fields) => {
                for (_, field) in fields {
                    if self.is_refuted(field)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            PatternKind::Constructor { data, constructor, arguments } => {
                let constructors = self.constructors_of(data)?;
                if constructors[*constructor].refuted {
                    return Ok(true);
                }
                for argument in arguments {
                    if self.is_refuted(argument)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
        }
    }

    fn alternative_field_representations(&mut self, alternative: &mut Alternative) -> GoResult<()> {
        let mut converted = vec![];
        for pattern in &mut alternative.patterns {
            self.field_representations(pattern, &mut converted)?;
        }
        match &mut alternative.body {
            Guarded::Unconditional(body) => {
                if converted.is_empty() {
                    return Ok(());
                }
                let placeholder = Expression::new(ExpressionKind::Unit, body.monotype);
                let body = std::mem::replace(body, placeholder);
                alternative.body = match conversions_as_bindings(&converted) {
                    Some(bindings) => {
                        let monotype = body.monotype;
                        let kind = ExpressionKind::Let { bindings, body: Box::new(body) };
                        Guarded::Unconditional(Expression::new(kind, monotype))
                    }
                    None => Guarded::Guards(vec![GuardedBranch { guards: converted, body }]),
                };
            }
            Guarded::Guards(branches) => {
                for branch in branches {
                    let mut guards = converted.clone();
                    for guard in std::mem::take(&mut branch.guards) {
                        let Guard::Pattern { mut pattern, value } = guard else {
                            guards.push(guard);
                            continue;
                        };
                        let mut nested = vec![];
                        self.field_representations(&mut pattern, &mut nested)?;
                        guards.push(Guard::Pattern { pattern, value });
                        guards.extend(nested);
                    }
                    branch.guards = guards;
                }
            }
        }
        Ok(())
    }

    /// Rebinds every field of `pattern` whose sub-pattern expects another
    /// representation, and adds the guard that matches the converted field.
    fn field_representations(
        &mut self,
        pattern: &mut Pattern,
        converted: &mut Vec<Guard>,
    ) -> GoResult<()> {
        match &mut pattern.kind {
            PatternKind::Wildcard | PatternKind::Variable(_) | PatternKind::Literal(_) => Ok(()),
            PatternKind::Named { pattern, .. } => self.field_representations(pattern, converted),
            PatternKind::Array(elements) | PatternKind::Closure { captures: elements, .. } => {
                for element in elements {
                    self.field_representations(element, converted)?;
                }
                Ok(())
            }
            PatternKind::Record(fields) => {
                for (_, field) in fields {
                    self.field_representations(field, converted)?;
                }
                Ok(())
            }
            PatternKind::Constructor { data, constructor, arguments } => {
                let constructors = self.constructors_of(data)?;
                let fields = constructors[*constructor].fields.clone();
                for (argument, &field) in arguments.iter_mut().zip(fields.iter()) {
                    if !self.changes_representation(field, argument.monotype) {
                        self.field_representations(argument, converted)?;
                        continue;
                    }
                    if let PatternKind::Wildcard = argument.kind {
                        argument.monotype = field;
                        continue;
                    }
                    let name = match &argument.kind {
                        PatternKind::Variable(local) | PatternKind::Named { local, .. } => {
                            local.name.clone()
                        }
                        _ => SmolStr::new_static("field"),
                    };
                    let stored = self.fresh_local(name, field);
                    let stored_value = Expression::new(ExpressionKind::Local(stored.id), field);
                    let stored = Pattern { kind: PatternKind::Variable(stored), monotype: field };
                    let mut expected = std::mem::replace(argument, stored);
                    let value = self.coerce(stored_value, expected.monotype);
                    let mut nested = vec![];
                    self.field_representations(&mut expected, &mut nested)?;
                    converted.push(Guard::Pattern { pattern: expected, value });
                    converted.extend(nested);
                }
                Ok(())
            }
        }
    }

    fn constructors_of(&mut self, data: &DataType) -> GoResult<Arc<[DataConstructor]>> {
        match self.monotypes.constructors(&mut self.context, data) {
            Ok(constructors) => Ok(constructors),
            Err(Failure::Unsupported(state)) => Err(self.pattern_error(state)),
            Err(Failure::Query(error)) => Err(error.into()),
        }
    }

    fn pattern_error(&mut self, state: UnsupportedState) -> GoError {
        let definition =
            self.current.map(|id| self.function_keys[id.0 as usize].definition.clone());
        let definition = match definition.map(|definition| self.describe_definition(definition)) {
            Some(Ok(definition)) => definition,
            Some(Err(error)) => return error,
            None => "constructor pattern".into(),
        };
        GoError::Unsupported { definition, state }
    }
}

/// Conversions that only bind variables are plain bindings and leave the
/// alternative unconditional.
fn conversions_as_bindings(converted: &[Guard]) -> Option<Vec<Binding>> {
    let bindings = converted.iter().map(|guard| match guard {
        Guard::Pattern { pattern: Pattern { kind: PatternKind::Variable(local), .. }, value } => {
            Some(Binding { local: local.clone(), value: value.clone() })
        }
        _ => None,
    });
    bindings.collect()
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn pattern(
        &mut self,
        scope: &mut Scope,
        binder_id: tree::BinderId,
    ) -> GoResult<Pattern> {
        let module = Arc::clone(&scope.module);
        let binder = &module.checked.tree[binder_id];
        let monotype = self.binder_monotype(scope, binder.type_id)?;
        let kind = match &binder.kind {
            tree::BinderKind::Typed { binder, .. } => return self.pattern(scope, *binder),
            tree::BinderKind::Error => {
                return Err(self.unsupported(scope, UnsupportedState::BinderError));
            }
            tree::BinderKind::Integer { value } => {
                PatternKind::Literal(Literal::Int(i64::from(*value)))
            }
            tree::BinderKind::Number { negative, value } => {
                let value = if *negative { format_smolstr!("-{value}") } else { value.clone() };
                PatternKind::Literal(Literal::Number(value))
            }
            tree::BinderKind::Variable => {
                let name = self.binder_name(scope, binder_id);
                let local = self.fresh_local(name, monotype);
                let source = self.checked_binder_source(scope, binder_id);
                scope.locals.insert(source, local.clone());
                self.register_scheme_local(scope, source, binder.type_id)?;
                PatternKind::Variable(local)
            }
            tree::BinderKind::Named { name, binder: inner } => {
                let local = self.fresh_local(name.clone(), monotype);
                let source = self.checked_binder_source(scope, binder_id);
                scope.locals.insert(source, local.clone());
                self.register_scheme_local(scope, source, binder.type_id)?;
                let pattern = self.pattern(scope, *inner)?;
                PatternKind::Named { local, pattern: Box::new(pattern) }
            }
            tree::BinderKind::Wildcard => PatternKind::Wildcard,
            tree::BinderKind::String { value } => PatternKind::Literal(string_literal(value)),
            tree::BinderKind::Char { value } => PatternKind::Literal(Literal::Char(*value)),
            tree::BinderKind::Boolean { value } => PatternKind::Literal(Literal::Boolean(*value)),
            tree::BinderKind::Array { elements } => {
                let mut patterns = Vec::with_capacity(elements.len());
                for &element in elements.iter() {
                    patterns.push(self.pattern(scope, element)?);
                }
                PatternKind::Array(patterns)
            }
            tree::BinderKind::Record { fields } => {
                let mut patterns = Vec::with_capacity(fields.len());
                for field in fields.iter() {
                    match field {
                        tree::RecordBinderField::Field { label, binder } => {
                            patterns.push((label.clone(), self.pattern(scope, *binder)?));
                        }
                        tree::RecordBinderField::Pun { label } => {
                            let Some(pun) = self.record_pun_source(scope, binder_id, label) else {
                                return Err(self.unsupported(scope, UnsupportedState::BinderError));
                            };
                            let field_monotype = self.field_monotype(scope, monotype, label)?;
                            let local = self.fresh_local(label.clone(), field_monotype);
                            let source = LocalSource::RecordPun(pun);
                            scope.locals.insert(source, local.clone());
                            if let Some(&pun_type) = scope.module.checked.node_types.puns.get(&pun)
                            {
                                self.register_scheme_local(scope, source, pun_type)?;
                            }
                            let pattern = Pattern {
                                kind: PatternKind::Variable(local),
                                monotype: field_monotype,
                            };
                            patterns.push((label.clone(), pattern));
                        }
                    }
                }
                PatternKind::Record(patterns)
            }
            tree::BinderKind::Constructor { resolution, arguments } => {
                if self.is_newtype_constructor(*resolution)? {
                    let [argument] = arguments.as_ref() else {
                        return Err(self.unsupported(scope, UnsupportedState::BinderError));
                    };
                    let mut pattern = self.pattern(scope, *argument)?;
                    if let Monotype::Recursive(data) = self.monotypes.get(monotype).clone() {
                        // The wrapped value has the unfolded representation, as the
                        // declared type of a function like `step (ListT m) = m` says.
                        let unfolded = self.monotypes.unfold_in(
                            &mut self.context,
                            &data,
                            &scope.definition,
                        )?;
                        self.adopt_representation(scope, *argument, &mut pattern, unfolded);
                        pattern.monotype = unfolded;
                    } else {
                        if !self.monotypes.same_without_causes(pattern.monotype, monotype)
                            && self.mentions_erased(monotype)
                        {
                            self.adopt_representation(scope, *argument, &mut pattern, monotype);
                        }
                        pattern.monotype = monotype;
                    }
                    return Ok(pattern);
                }
                let Monotype::Data(data) = self.monotypes.get(monotype).clone() else {
                    return Err(self.unsupported(scope, UnsupportedState::BinderError));
                };
                let constructors = self
                    .monotypes
                    .constructors(&mut self.context, &data)
                    .map_err(|failure| failure.at(&scope.definition))?;
                let Some(constructor) = constructors
                    .iter()
                    .position(|constructor| constructor.term == Some(resolution.1))
                else {
                    return Err(self.unsupported(scope, UnsupportedState::BinderError));
                };
                let mut patterns = Vec::with_capacity(arguments.len());
                for &argument in arguments.iter() {
                    patterns.push(self.pattern(scope, argument)?);
                }
                PatternKind::Constructor { data, constructor, arguments: patterns }
            }
        };
        Ok(Pattern { kind, monotype })
    }

    fn adopt_representation(
        &mut self,
        scope: &mut Scope,
        binder: tree::BinderId,
        pattern: &mut Pattern,
        monotype: MonotypeId,
    ) {
        let (binder, _) = self.unwrap_typed(scope, binder);
        let source = self.checked_binder_source(scope, binder);
        if let PatternKind::Variable(local) | PatternKind::Named { local, .. } = &mut pattern.kind {
            local.monotype = monotype;
            scope.locals.insert(source, local.clone());
        }
    }

    /// A binder whose type is quantified, directly or through a synonym such as
    /// profunctor-lenses' `Lens s a`, is instantiated at each of its uses.
    fn register_scheme_local(
        &mut self,
        scope: &mut Scope,
        source: LocalSource,
        type_id: TypeId,
    ) -> GoResult<()> {
        match self.scheme_type(scope, type_id)? {
            Some(closed) => scope.scheme_locals.insert(source, closed),
            None => scope.scheme_locals.remove(&source),
        };
        Ok(())
    }

    pub(super) fn scheme_type(
        &mut self,
        scope: &Scope,
        type_id: TypeId,
    ) -> GoResult<Option<TypeId>> {
        let closed = self.context.types.substitute(type_id, &scope.substitution);
        let (head, _) = self.context.types.spine(closed);
        let closed = match self.context.types.lookup(head) {
            Type::Synonym(..) => crate::monotype::expand_synonyms(&mut self.context, closed)?,
            _ => closed,
        };
        let quantified = matches!(
            self.context.types.lookup(self.context.types.strip_annotations(closed)),
            Type::Forall(..) | Type::Constrained(..)
        );
        Ok(quantified.then_some(closed))
    }

    pub(super) fn binder_name(&self, scope: &Scope, binder_id: tree::BinderId) -> SmolStr {
        let binder = &scope.module.checked.tree[binder_id];
        match binder.source {
            tree::BinderSource::Binder(source) => {
                match scope.module.lowered.tree.get_binder_kind(source) {
                    Some(lowering::BinderKind::Variable { variable: Some(name) }) => name.clone(),
                    Some(lowering::BinderKind::Named { named: Some(name), .. }) => name.clone(),
                    _ => SmolStr::new_static(crate::naming::VALUE),
                }
            }
            tree::BinderSource::Generated { name, .. } => {
                SmolStr::clone(self.context.queries.lookup_smol_str(name))
            }
            _ => SmolStr::new_static(crate::naming::VALUE),
        }
    }

    fn record_pun_source(
        &self,
        scope: &Scope,
        binder_id: tree::BinderId,
        label: &str,
    ) -> Option<lowering::RecordPunId> {
        let tree::BinderSource::Binder(source) = scope.module.checked.tree[binder_id].source else {
            return None;
        };
        let lowering::BinderKind::Record { record } =
            scope.module.lowered.tree.get_binder_kind(source)?
        else {
            return None;
        };
        record.iter().find_map(|field| {
            let lowering::BinderRecordItem::RecordPun { id, name } = field else {
                return None;
            };
            name.as_deref().filter(|name| *name == label).map(|_| *id)
        })
    }
}
