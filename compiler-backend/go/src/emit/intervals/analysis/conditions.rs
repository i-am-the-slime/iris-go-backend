use rustc_hash::FxHashMap;

use super::{Analysis, BoundTest};
use crate::emit::intervals::constraints::{State, Symbol};
use crate::emit::intervals::syntax::each_subexpression;
use crate::syntax::{GoBinaryOperator, GoExpression, GoUnaryOperator};

impl Analysis<'_, '_, '_> {
    pub(super) fn condition(&mut self, test: &GoExpression, state: &mut State) -> BoundTest {
        // Where paths that assigned differently met, the symbol gets a generation of its own
        // here, so that the test is used only until the next assignment.
        let mut read = vec![];
        each_subexpression(test, &mut |value| {
            if let GoExpression::Identifier(name) = value {
                read.push(name.clone());
            }
        });
        for name in read {
            let Some(symbol) = self.lookup(&name) else { continue };
            let length = self.bindings.get(&symbol).and_then(|binding| binding.length);
            for symbol in [Some(symbol), length].into_iter().flatten() {
                if state.generations.get(&symbol) == Some(&0) {
                    let generation = self.fresh_generation();
                    state.generations.insert(symbol, generation);
                }
            }
        }
        if state.heap == 0 {
            state.heap = self.fresh_generation();
        }
        let mut scope = FxHashMap::default();
        let mut generations = vec![];
        let mut through_pointer = false;
        each_subexpression(test, &mut |value| match value {
            GoExpression::Identifier(name) => {
                if let Some(symbol) = self.lookup(name) {
                    scope.insert(name.clone(), symbol);
                    generations.push((symbol, state.generations.get(&symbol).copied()));
                    if let Some(length) =
                        self.bindings.get(&symbol).and_then(|binding| binding.length)
                    {
                        generations.push((length, state.generations.get(&length).copied()));
                    }
                }
            }
            GoExpression::Unary { operator: GoUnaryOperator::Dereference, .. } => {
                through_pointer = true
            }
            _ => {}
        });
        let heap = through_pointer.then_some(state.heap);
        BoundTest { test: test.clone(), scope, generations, heap }
    }

    /// Whether assuming the test can tell anything: it reads a tracked symbol, a name bound to
    /// a test, or a constant.
    pub(super) fn informs(&self, test: &GoExpression) -> bool {
        let mut informs = false;
        each_subexpression(test, &mut |value| match value {
            GoExpression::Boolean(_) => informs = true,
            GoExpression::Identifier(name) => {
                informs |= self.lookup(name).is_some_and(|symbol| {
                    self.conditions.contains_key(&symbol)
                        || self.bindings.get(&symbol).is_some_and(|binding| binding.tracked)
                })
            }
            _ => {}
        });
        informs
    }

    pub(super) fn assume(&mut self, state: &State, test: &GoExpression, truth: bool) -> State {
        self.assume_with(state, test, truth, None)
    }

    /// `state` where `test` is `truth`. `blank` stands for the empty name, the loop variable
    /// of a counting loop's test.
    pub(super) fn assume_with(
        &mut self,
        state: &State,
        test: &GoExpression,
        truth: bool,
        blank: Option<Symbol>,
    ) -> State {
        if state.unreachable {
            return state.clone();
        }
        let from = self.temporaries.len();
        let mut assumed = state.clone();
        self.assume_into(&mut assumed, test, truth, blank);
        self.forget_temporaries(&mut assumed, from);
        assumed
    }

    fn assume_into(
        &mut self,
        state: &mut State,
        test: &GoExpression,
        truth: bool,
        blank: Option<Symbol>,
    ) {
        if state.unreachable {
            return;
        }
        match test {
            GoExpression::Boolean(value) => {
                if *value != truth {
                    *state = State::unreachable();
                }
            }
            GoExpression::Unary { operator: GoUnaryOperator::Not, operand } => {
                self.assume_into(state, operand, !truth, blank)
            }
            GoExpression::Binary { operator: GoBinaryOperator::LogicalAnd, left, right }
                if truth =>
            {
                self.assume_into(state, left, true, blank);
                self.assume_into(state, right, true, blank);
            }
            GoExpression::Binary { operator: GoBinaryOperator::LogicalOr, left, right }
                if !truth =>
            {
                self.assume_into(state, left, false, blank);
                self.assume_into(state, right, false, blank);
            }
            GoExpression::Binary {
                operator: operator @ (GoBinaryOperator::LogicalAnd | GoBinaryOperator::LogicalOr),
                left,
                right,
            } => {
                // `a && b` false: `a` false, or `a` true and `b` false; `a || b` true dually.
                let first = *operator == GoBinaryOperator::LogicalOr;
                let mut one = state.clone();
                self.assume_into(&mut one, left, first, blank);
                let mut other = state.clone();
                self.assume_into(&mut other, left, !first, blank);
                self.assume_into(&mut other, right, first, blank);
                *state = one.join(&other);
            }
            GoExpression::Binary { operator, left, right } if operator.is_comparison() => {
                let operator = if truth { Some(*operator) } else { operator.negated_comparison() };
                let Some(operator) = operator else { return };
                let left = self.value_with(left, state, blank);
                let right = self.value_with(right, state, blank);
                let (Some(left), Some(right)) = (left, right) else { return };
                match operator {
                    GoBinaryOperator::LessThan => state.assume_at_most(left, right, -1),
                    GoBinaryOperator::LessThanOrEqual => state.assume_at_most(left, right, 0),
                    GoBinaryOperator::GreaterThan => state.assume_at_most(right, left, -1),
                    GoBinaryOperator::GreaterThanOrEqual => state.assume_at_most(right, left, 0),
                    GoBinaryOperator::Equal => {
                        state.assume_at_most(left, right, 0);
                        state.assume_at_most(right, left, 0);
                    }
                    _ => {}
                }
            }
            GoExpression::Identifier(name) => {
                let Some(symbol) = self.lookup(name) else { return };
                let Some(condition) = self.conditions.get(&symbol).cloned() else { return };
                if !holds(&condition, state) {
                    return;
                }
                self.scopes.push(condition.scope);
                self.assume_into(state, &condition.test, truth, blank);
                self.scopes.pop();
            }
            _ => {}
        }
    }

    /// Whether the state proves the test true or false.
    pub(super) fn decide(&mut self, state: &State, test: &GoExpression) -> Option<bool> {
        if state.unreachable {
            return None;
        }
        if self.assume(state, test, false).unreachable {
            Some(true)
        } else if self.assume(state, test, true).unreachable {
            Some(false)
        } else {
            None
        }
    }
}

fn holds(condition: &BoundTest, state: &State) -> bool {
    let unchanged = condition.generations.iter().all(|(symbol, generation)| {
        let now = state.generations.get(symbol).copied();
        now == *generation && now != Some(0)
    });
    unchanged && condition.heap.is_none_or(|heap| heap == state.heap && heap != 0)
}
