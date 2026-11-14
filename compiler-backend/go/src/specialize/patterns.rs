//! A constructor's fields have the representation of its data type's monotype,
//! which erases the arguments of a non-regular data type, while the patterns on
//! them have the types the checker gave them. A field whose pattern expects
//! another representation is bound as stored and matched again, converted, by a
//! pattern guard: `One x _` on a `Sequence Int` binds the erased field and
//! asserts `x` to `Int`.

use smol_str::SmolStr;

use super::Specializer;
use crate::error::{GoError, GoResult, UnsupportedState};
use crate::mono::{
    Alternative, Binding, Expression, ExpressionKind, Guard, Guarded, GuardedBranch,
};
use crate::mono::{Pattern, PatternKind};

impl<Q> Specializer<'_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn match_field_representations(
        &mut self,
        expression: &mut Expression,
    ) -> GoResult<()> {
        if let ExpressionKind::Case { alternatives, .. } = &mut expression.kind {
            for alternative in alternatives {
                self.alternative_field_representations(alternative)?;
            }
        }
        let mut result = Ok(());
        crate::simplify::for_each_child_mut(expression, &mut |child| {
            if result.is_ok() {
                result = self.match_field_representations(child);
            }
        });
        result
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
                let constructors = match self.monotypes.constructors(&mut self.context, data)? {
                    Ok(constructors) => constructors,
                    Err(state) => return Err(self.pattern_error(state)),
                };
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
