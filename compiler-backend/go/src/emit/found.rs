//! Foreigns whose Go helper answers a Maybe as Go's own lookups do, with the `Just`'s field and
//! whether there is one ([`crate::foreign::Boundary::found`]):
//!
//! ```go
//! first, found := prim.CodeUnitCharAt(0, word)
//! if found { … } else { … }
//! ```
//!
//! A case over such a call branches on `found` and binds the field where `Just` would, and one
//! whose `Just` alternative is the field itself defines its result by the call:
//!
//! ```go
//! first, found := prim.CodeUnitCharAt(0, word)
//! if !found { first = '?' }
//! ```
//!
//! Anywhere else the Maybe is built from the two.

use super::iteration::Found;
use super::{Emitter, Mode, Sink, identifier_expression, lines, local_uses};
use crate::error::GoResult;
use crate::foreign::{Foreign, MaybeConstructors};
use crate::monomorphic::{Alternative, Expression, ExpressionKind, Guarded, Local, PatternKind};
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement};

/// The alternative a case over a found call takes for `Just` or for `Nothing`, with the local it
/// binds the `Just`'s field to.
struct Branch<'a> {
    payload: Option<&'a Local>,
    alternative: &'a Alternative,
    body: &'a Expression,
}

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// What a found call answers, built from its two results: a Maybe, or whatever the
    /// arguments in the constructors' places make of them (`member` passes `false` and
    /// `const true` to `lookup`).
    pub(super) fn found_maybe(
        &mut self,
        called: GoExpression,
        arguments: &[Expression],
        constructors: MaybeConstructors,
        result: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let name = self.temporary(&super::scrutinee_name(&called));
        let payload = self.temporary("value");
        let found = self.temporary("found");
        let defined = out.len();
        out.push(GoStatement::Define {
            names: vec![payload.clone(), found.clone()],
            values: vec![called],
        });
        let payload = identifier_expression(&payload);
        let mut then = vec![];
        let mut otherwise = vec![];
        let (present, absent) = if self.is_maybe(result)? {
            let (data, just) = self.constructor_named(result, "Just")?;
            let (_, nothing) = self.constructor_named(result, "Nothing")?;
            (self.construct(&data, just, vec![payload])?, self.construct(&data, nothing, vec![])?)
        } else {
            let present = match self.callback(&arguments[constructors.just], 1) {
                Some(Found::Inline { parameters, body }) => {
                    if local_uses(body, parameters[0].id) == 0
                        && let GoStatement::Define { names, .. } = &mut out[defined]
                    {
                        names[0] = "_".to_string();
                    }
                    self.locals.insert(parameters[0].id, payload);
                    self.value(body, &mut then)?
                }
                _ => {
                    let present = self.value(&arguments[constructors.just], out)?;
                    super::call(present, vec![payload])
                }
            };
            (present, self.value(&arguments[constructors.nothing], &mut otherwise)?)
        };
        let type_ = self.go_type(result)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let target = vec![identifier_expression(&name)];
        then.push(GoStatement::Assign { targets: target.clone(), values: vec![present] });
        otherwise.push(GoStatement::Assign { targets: target, values: vec![absent] });
        out.push(GoStatement::If { condition: identifier_expression(&found), then, otherwise });
        Ok(identifier_expression(&name))
    }

    /// A case whose one scrutinee is a found call, as a test of `found`; false, emitting
    /// nothing, for any other case.
    pub(super) fn found_case(
        &mut self,
        expression: &Expression,
        scrutinees: &[Expression],
        alternatives: &[Alternative],
        mode: Mode,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<bool> {
        let [scrutinee] = scrutinees else { return Ok(false) };
        let ExpressionKind::Foreign { foreign, arguments } = &scrutinee.kind else {
            return Ok(false);
        };
        let Foreign::Call { function, boundary, .. } = **foreign else { return Ok(false) };
        if !boundary.found || boundary.iteration.is_some() || !self.is_maybe(scrutinee.monotype)? {
            return Ok(false);
        }
        let (_, just) = self.constructor_named(scrutinee.monotype, "Just")?;
        let Some([present, absent]) = branches(alternatives, just) else { return Ok(false) };

        let values = self.boundary_arguments(arguments, boundary, scrutinee.monotype, true, out)?;
        let function = self.boundary_function(function, boundary, scrutinee.monotype)?;
        let called = super::call(function, values);
        if let (Sink::Define(name), Mode::Value, Some(local)) = (&sink, mode, present.payload)
            && matches!(present.body.kind, ExpressionKind::Local(id) if id == local.id)
        {
            let found = self.temporary("found");
            out.push(GoStatement::Define {
                names: vec![name.clone(), found.clone()],
                values: vec![called],
            });
            let line = self.branch_line(absent.alternative.position)?;
            let mut fallback = vec![];
            self.sink(absent.body, mode, Sink::Assign(name.clone()), &mut fallback)?;
            lines::attribute_branch(line.as_ref(), 0, &mut fallback);
            let missing = GoExpression::Unary {
                operator: "!",
                operand: Box::new(identifier_expression(&found)),
            };
            out.push(GoStatement::If { condition: missing, then: fallback, otherwise: vec![] });
            return Ok(true);
        }
        let payload = match present.payload {
            Some(local) if local_uses(present.body, local.id) > 0 => self.bind_local(local),
            _ => "_".to_string(),
        };
        let found = self.temporary("found");
        out.push(GoStatement::Define { names: vec![payload, found.clone()], values: vec![called] });

        let sink = self.prepare_branching_sink(sink, expression, mode, out)?;
        let mut blocks = vec![];
        for branch in [&present, &absent] {
            let line = self.branch_line(branch.alternative.position)?;
            let mut block = vec![];
            self.sink(branch.body, mode, sink.clone(), &mut block)?;
            lines::attribute_branch(line.as_ref(), 0, &mut block);
            blocks.push(block);
        }
        let [then, otherwise] = <[_; 2]>::try_from(blocks).expect("two branches");
        let found = identifier_expression(&found);
        out.push(match then.iter().all(|statement| matches!(statement, GoStatement::Line(_))) {
            true => GoStatement::If {
                condition: GoExpression::Unary { operator: "!", operand: Box::new(found) },
                then: otherwise,
                otherwise: vec![],
            },
            false => GoStatement::If { condition: found, then, otherwise },
        });
        Ok(true)
    }

    fn is_maybe(&mut self, monotype: MonotypeId) -> GoResult<bool> {
        let Monotype::Data(data) = self.monotypes.get(monotype).clone() else { return Ok(false) };
        Ok(self.maybe_payload(&data)?.is_some())
    }
}

/// The first alternative that `Just` reaches and the first that `Nothing` reaches, when every
/// alternative is unconditional and matches a constructor or anything.
fn branches(alternatives: &[Alternative], just: usize) -> Option<[Branch<'_>; 2]> {
    let mut present = None;
    let mut absent = None;
    for alternative in alternatives {
        let Guarded::Unconditional(body) = &alternative.body else { return None };
        let [pattern] = alternative.patterns.as_slice() else { return None };
        let branch = |payload| Branch { payload, alternative, body };
        match &pattern.kind {
            PatternKind::Wildcard => {
                present.get_or_insert_with(|| branch(None));
                absent.get_or_insert_with(|| branch(None));
            }
            PatternKind::Constructor { constructor, arguments, .. } if *constructor == just => {
                let payload = match arguments.as_slice() {
                    [field] => match &field.kind {
                        PatternKind::Wildcard => None,
                        PatternKind::Variable(local) => Some(local),
                        _ => return None,
                    },
                    _ => return None,
                };
                present.get_or_insert_with(|| branch(payload));
            }
            PatternKind::Constructor { .. } => {
                absent.get_or_insert_with(|| branch(None));
            }
            _ => return None,
        }
    }
    let [present, absent] = [present?, absent?];
    (!std::ptr::eq(present.alternative, absent.alternative)).then_some([present, absent])
}
