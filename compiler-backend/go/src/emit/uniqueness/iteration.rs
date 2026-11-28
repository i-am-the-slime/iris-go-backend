//! What a tail loop's parameter reaches: the next iteration, through the loop's jumps, or past
//! the iteration, through every other value the iteration computes.

use crate::monomorphic::{Expression, ExpressionKind, FunctionId, Guard, Guarded, LocalId};

/// A parameter of a self-recursive function whose tail calls are the jumps of its loop.
#[derive(Clone, Copy)]
pub(in crate::emit) struct TailLoop {
    pub function: FunctionId,
    pub arity: usize,
    pub position: usize,
    pub parameter: LocalId,
}

/// The values that every jump of the loop passes as its parameter, when the parameter cannot
/// reach the next iteration any other way: none of the values the iteration computes on its way
/// to a jump or a result, nor the jumps' other arguments, `may_hold` the parameter. The loop's
/// result may hold it, as it ends the loop.
pub(in crate::emit) fn next_iterations<'e>(
    tail_loop: TailLoop,
    body: &'e Expression,
    may_hold: &mut impl FnMut(&Expression) -> bool,
) -> Option<Vec<&'e Expression>> {
    let mut next = vec![];
    results(tail_loop, body, may_hold, &mut next)?;
    Some(next)
}

fn results<'e>(
    tail_loop: TailLoop,
    expression: &'e Expression,
    may_hold: &mut impl FnMut(&Expression) -> bool,
    next: &mut Vec<&'e Expression>,
) -> Option<()> {
    match &expression.kind {
        ExpressionKind::Let { bindings, body } => {
            for binding in bindings {
                unaliased(may_hold, &binding.value)?;
            }
            results(tail_loop, body, may_hold, next)
        }
        ExpressionKind::If { condition, then, otherwise } => {
            unaliased(may_hold, condition)?;
            results(tail_loop, then, may_hold, next)?;
            results(tail_loop, otherwise, may_hold, next)
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            for scrutinee in scrutinees {
                unaliased(may_hold, scrutinee)?;
            }
            for alternative in alternatives {
                match &alternative.body {
                    Guarded::Unconditional(body) => results(tail_loop, body, may_hold, next)?,
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            for guard in &branch.guards {
                                match guard {
                                    Guard::Boolean(value) | Guard::Pattern { value, .. } => {
                                        unaliased(may_hold, value)?;
                                    }
                                }
                            }
                            results(tail_loop, &branch.body, may_hold, next)?;
                        }
                    }
                }
            }
            Some(())
        }
        ExpressionKind::Apply { function, arguments }
            if matches!(function.kind, ExpressionKind::Function(id) if id == tail_loop.function)
                && arguments.len() == tail_loop.arity =>
        {
            for (position, argument) in arguments.iter().enumerate() {
                if position == tail_loop.position {
                    next.push(argument);
                } else {
                    unaliased(may_hold, argument)?;
                }
            }
            Some(())
        }
        _ => Some(()),
    }
}

fn unaliased(may_hold: &mut impl FnMut(&Expression) -> bool, value: &Expression) -> Option<()> {
    (!may_hold(value)).then_some(())
}

#[cfg(test)]
mod tests {
    use smol_str::SmolStr;

    use super::{TailLoop, next_iterations};
    use crate::monomorphic::traversal::mentions_local;
    use crate::monomorphic::{Binding, Expression, ExpressionKind, FunctionId, Local, LocalId};
    use crate::monotype::MonotypeId;

    const LOOP: TailLoop =
        TailLoop { function: FunctionId(0), arity: 2, position: 0, parameter: LocalId(1) };

    fn expression(kind: ExpressionKind) -> Expression {
        Expression::new(kind, MonotypeId::for_tests())
    }

    fn local(id: u32) -> Expression {
        expression(ExpressionKind::Local(LocalId(id)))
    }

    fn call(function: u32, arguments: Vec<Expression>) -> Expression {
        let function = Box::new(expression(ExpressionKind::Function(FunctionId(function))));
        expression(ExpressionKind::Apply { function, arguments })
    }

    fn binding(id: u32, value: Expression, body: Expression) -> Expression {
        let monotype = MonotypeId::for_tests();
        let local = Local { id: LocalId(id), name: SmolStr::new_static("bound"), monotype };
        let bindings = vec![Binding { local, value }];
        expression(ExpressionKind::Let { bindings, body: Box::new(body) })
    }

    /// `if done then xs else go (step xs) n`
    fn stepping(next: Expression, other: Expression) -> Expression {
        expression(ExpressionKind::If {
            condition: Box::new(local(9)),
            then: Box::new(local(1)),
            otherwise: Box::new(call(0, vec![next, other])),
        })
    }

    fn next_of(body: &Expression) -> Option<usize> {
        let mut holds = |value: &Expression| mentions_local(value, LOOP.parameter);
        next_iterations(LOOP, body, &mut holds).map(|next| next.len())
    }

    #[test]
    fn the_jumps_pass_the_next_iterations() {
        assert_eq!(next_of(&stepping(call(7, vec![local(1)]), local(2))), Some(1));
        assert_eq!(next_of(&local(1)), Some(0));
    }

    #[test]
    fn the_parameter_reaching_the_next_iteration_otherwise_stops_it() {
        assert_eq!(next_of(&stepping(call(7, vec![local(1)]), local(1))), None);
        let kept = binding(3, local(1), stepping(local(2), local(3)));
        assert_eq!(next_of(&kept), None);
    }

    #[test]
    fn a_call_of_another_function_is_a_result() {
        assert_eq!(next_of(&call(5, vec![local(1), local(1)])), Some(0));
    }
}
