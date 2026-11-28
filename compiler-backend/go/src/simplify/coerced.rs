use rustc_hash::FxHashMap;

use super::{INLINE_SIZE, Simplifier};
use crate::monomorphic::{Binding, Expression, ExpressionKind, Guarded, Local};
use crate::monotype::MonotypeId;
use crate::purity::{is_within_size, only_called};

impl Simplifier<'_> {
    pub(super) fn pushed_coercion(
        &mut self,
        value: Expression,
        monotype: MonotypeId,
    ) -> Result<Expression, Expression> {
        if returns_coerced(&value) || self.leads_to_one_result(&value, monotype) {
            let pushed = self.coerced_inward(value, monotype);
            return Ok(self.expression(pushed));
        }
        let Some(callee) = self.coerced_helper_called(&value) else { return Err(value) };
        let parameters = callee.parameters.clone();
        let mut body = callee.body.clone();
        let ExpressionKind::Apply { arguments, .. } = value.kind else {
            unreachable!("invariant violated: a coerced helper is applied")
        };
        let mut renaming = FxHashMap::default();
        let parameters: Vec<Local> = parameters
            .iter()
            .map(|parameter| self.rename_binder(parameter, &mut renaming))
            .collect();
        self.rename(&mut body, &mut renaming);
        let body = self.coerced_inward(body, monotype);
        let bindings = parameters
            .into_iter()
            .zip(arguments)
            .map(|(local, value)| Binding { local, value })
            .collect();
        let kind = ExpressionKind::Let { bindings, body: Box::new(body) };
        Ok(self.expression(Expression::new(kind, monotype)))
    }

    fn coerced_helper_called(&self, value: &Expression) -> Option<&crate::monomorphic::Function> {
        let ExpressionKind::Apply { function, arguments } = &value.kind else { return None };
        let ExpressionKind::Function(id) = function.kind else { return None };
        if id == self.entry || self.recursive[id.0 as usize] {
            return None;
        }
        let callee = self.functions[id.0 as usize].as_ref()?;
        let fits = callee.parameters.len() == arguments.len()
            && self.sizes[id.0 as usize] <= INLINE_SIZE
            && returns_coerced(&callee.body);
        fits.then_some(callee)
    }

    pub(super) fn is_coerced_helper(&self, binding: &Binding, body: &Expression) -> bool {
        let ExpressionKind::Lambda { parameters, body: lambda_body } = &binding.value.kind else {
            return false;
        };
        self.fuel > 0
            && is_within_size(&binding.value, INLINE_SIZE)
            && returns_coerced(lambda_body)
            && only_called(body, binding.local.id, parameters.len())
    }

    fn coerced_inward(&mut self, mut value: Expression, monotype: MonotypeId) -> Expression {
        let kind = std::mem::replace(&mut value.kind, ExpressionKind::Unit);
        let kind = match kind {
            ExpressionKind::Let { bindings, body } => ExpressionKind::Let {
                bindings,
                body: Box::new(self.coerced_inward(*body, monotype)),
            },
            ExpressionKind::If { condition, then, otherwise } => ExpressionKind::If {
                condition,
                then: Box::new(self.coerced_inward(*then, monotype)),
                otherwise: Box::new(self.coerced_inward(*otherwise, monotype)),
            },
            ExpressionKind::Case { scrutinees, mut alternatives } => {
                for alternative in &mut alternatives {
                    let taken = std::mem::replace(&mut alternative.body, Guarded::Guards(vec![]));
                    alternative.body = self.coerced_guarded(taken, monotype);
                }
                ExpressionKind::Case { scrutinees, alternatives }
            }
            ExpressionKind::Lambda { parameters, body }
                if self.takes_same_parameters(value.monotype, monotype, parameters.len()) =>
            {
                let result = self.monotypes.result_after(monotype, parameters.len());
                ExpressionKind::Lambda {
                    parameters,
                    body: Box::new(self.coerced_inward(*body, result)),
                }
            }
            ExpressionKind::EffectPure(inner)
                if let Some(result) = self.monotypes.effect_result(monotype) =>
            {
                ExpressionKind::EffectPure(Box::new(self.coerced_inward(*inner, result)))
            }
            ExpressionKind::EffectBind { action, local, body }
                if self.monotypes.effect_result(monotype).is_some() =>
            {
                ExpressionKind::EffectBind {
                    action,
                    local,
                    body: Box::new(self.coerced_inward(*body, monotype)),
                }
            }
            ExpressionKind::Coerce(inner) => {
                return Expression::new(ExpressionKind::Coerce(inner), monotype);
            }
            kind => {
                value.kind = kind;
                if self.monotypes.same_without_causes(value.monotype, monotype) {
                    value.monotype = monotype;
                    return value;
                }
                return Expression::new(ExpressionKind::Coerce(Box::new(value)), monotype);
            }
        };
        Expression::new(kind, monotype)
    }

    fn coerced_guarded(&mut self, guarded: Guarded, monotype: MonotypeId) -> Guarded {
        match guarded {
            Guarded::Unconditional(body) => {
                Guarded::Unconditional(self.coerced_inward(body, monotype))
            }
            Guarded::Guards(mut branches) => {
                for branch in &mut branches {
                    let placeholder = Expression::new(ExpressionKind::Unit, monotype);
                    let body = std::mem::replace(&mut branch.body, placeholder);
                    branch.body = self.coerced_inward(body, monotype);
                }
                Guarded::Guards(branches)
            }
        }
    }

    fn leads_to_one_result(&self, value: &Expression, monotype: MonotypeId) -> bool {
        match &value.kind {
            ExpressionKind::EffectPure(_) | ExpressionKind::EffectBind { .. } => {
                self.monotypes.effect_result(monotype).is_some()
            }
            ExpressionKind::Lambda { parameters, .. } => {
                self.takes_same_parameters(value.monotype, monotype, parameters.len())
            }
            _ => false,
        }
    }

    fn takes_same_parameters(&self, from: MonotypeId, to: MonotypeId, arity: usize) -> bool {
        let mut from = from;
        let mut to = to;
        for _ in 0..arity {
            let Some((from_argument, from_result)) = self.monotypes.function_parts(from) else {
                return false;
            };
            let Some((to_argument, to_result)) = self.monotypes.function_parts(to) else {
                return false;
            };
            if !self.monotypes.same_without_causes(from_argument, to_argument) {
                return false;
            }
            from = from_result;
            to = to_result;
        }
        true
    }
}

fn returns_coerced(body: &Expression) -> bool {
    match &body.kind {
        ExpressionKind::Coerce(_) => true,
        ExpressionKind::Let { body, .. } => returns_coerced(body),
        ExpressionKind::If { then, otherwise, .. } => {
            returns_coerced(then) || returns_coerced(otherwise)
        }
        ExpressionKind::Case { alternatives, .. } => {
            alternatives.iter().any(|alternative| match &alternative.body {
                Guarded::Unconditional(body) => returns_coerced(body),
                Guarded::Guards(branches) => {
                    branches.iter().any(|branch| returns_coerced(&branch.body))
                }
            })
        }
        _ => false,
    }
}
