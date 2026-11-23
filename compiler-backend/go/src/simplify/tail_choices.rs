use rustc_hash::FxHashSet;

use crate::foreign::{Foreign, Operator};
use crate::graph::strongly_connected;
use crate::monomorphic::traversal::reference_graph;
use crate::monomorphic::{Expression, ExpressionKind, FunctionId, Guarded, Literal, Program};

pub(super) fn branch_tail_calls(mut program: Program) -> Program {
    let references = reference_graph(&program.functions);
    let components = strongly_connected(&references);
    let arities: Vec<usize> =
        program.functions.iter().map(|function| function.parameters.len()).collect();
    for component in components {
        let members: FxHashSet<FunctionId> =
            component.iter().map(|&index| FunctionId(index as u32)).collect();
        let recursive = component.len() > 1 || references[component[0]].contains(&component[0]);
        if !recursive {
            continue;
        }
        let callees = Callees { members: &members, arities: &arities };
        for index in component {
            branch_tail(&mut program.functions[index].body, &callees);
        }
    }
    program
}

struct Callees<'c> {
    members: &'c FxHashSet<FunctionId>,
    arities: &'c [usize],
}

impl Callees<'_> {
    fn called_in_tail(&self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Apply { function, arguments } => {
                matches!(function.kind, ExpressionKind::Function(id)
                    if self.members.contains(&id) && self.arities[id.0 as usize] == arguments.len())
            }
            ExpressionKind::Let { body, .. } => self.called_in_tail(body),
            ExpressionKind::If { then, otherwise, .. } => {
                self.called_in_tail(then) || self.called_in_tail(otherwise)
            }
            ExpressionKind::Case { alternatives, .. } => {
                alternatives.iter().any(|alternative| match &alternative.body {
                    Guarded::Unconditional(body) => self.called_in_tail(body),
                    Guarded::Guards(branches) => {
                        branches.iter().any(|branch| self.called_in_tail(&branch.body))
                    }
                })
            }
            ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments }
                if is_short_circuit(*operator) =>
            {
                self.called_in_tail(&arguments[1])
            }
            _ => false,
        }
    }
}

fn branch_tail(expression: &mut Expression, callees: &Callees<'_>) {
    match &mut expression.kind {
        ExpressionKind::Let { body, .. } => branch_tail(body, callees),
        ExpressionKind::If { then, otherwise, .. } => {
            branch_tail(then, callees);
            branch_tail(otherwise, callees);
        }
        ExpressionKind::Case { alternatives, .. } => {
            for alternative in alternatives {
                match &mut alternative.body {
                    Guarded::Unconditional(body) => branch_tail(body, callees),
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            branch_tail(&mut branch.body, callees);
                        }
                    }
                }
            }
        }
        ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments }
            if is_short_circuit(*operator) && callees.called_in_tail(&arguments[1]) =>
        {
            let deciding = *operator == Operator::BooleanOr;
            let [condition, mut rest] = <[Expression; 2]>::try_from(std::mem::take(arguments))
                .unwrap_or_else(|_| {
                    unreachable!("invariant violated: a Boolean operator has two operands")
                });
            branch_tail(&mut rest, callees);
            let decided = Expression::new(
                ExpressionKind::Literal(Literal::Boolean(deciding)),
                expression.monotype,
            );
            let (then, otherwise) = if deciding { (decided, rest) } else { (rest, decided) };
            expression.kind = ExpressionKind::If {
                condition: Box::new(condition),
                then: Box::new(then),
                otherwise: Box::new(otherwise),
            };
        }
        _ => {}
    }
}

fn is_short_circuit(operator: Operator) -> bool {
    matches!(operator, Operator::BooleanAnd | Operator::BooleanOr)
}
