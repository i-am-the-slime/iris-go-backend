use crate::foreign::{Foreign, GoPackage};
use crate::monomorphic::traversal::{reference_graph, visit};
use crate::monomorphic::{Expression, ExpressionKind, Function, FunctionId, LocalId, Program};
use crate::monotype::{Monotype, Monotypes};

pub struct Suspension {
    suspending: Vec<bool>,
}

impl Suspension {
    pub fn analyse(program: &Program, monotypes: &Monotypes) -> Suspension {
        let mut suspending: Vec<bool> = program
            .functions
            .iter()
            .map(|function| suspends_directly(function, monotypes))
            .collect();
        let references = reference_graph(&program.functions);
        loop {
            let mut changed = false;
            for (index, callees) in references.iter().enumerate() {
                if !suspending[index] && callees.iter().any(|&callee| suspending[callee]) {
                    suspending[index] = true;
                    changed = true;
                }
            }
            if !changed {
                return Suspension { suspending };
            }
        }
    }

    pub fn copy(&mut self, original: FunctionId) {
        self.suspending.push(self.suspending[original.0 as usize]);
    }

    pub fn may_suspend(&self, expression: &Expression, monotypes: &Monotypes) -> bool {
        self.may_suspend_except(expression, &[], monotypes)
    }

    pub fn traversal_may_suspend(
        &self,
        callback: &Expression,
        elements: &Expression,
        monotypes: &Monotypes,
    ) -> bool {
        let parameters: Vec<LocalId> = match &callback.kind {
            ExpressionKind::Lambda { parameters, .. } => {
                parameters.iter().map(|parameter| parameter.id).collect()
            }
            _ => vec![],
        };
        self.may_suspend_except(callback, &parameters, monotypes)
            || self.may_suspend(elements, monotypes)
    }

    fn may_suspend_except(
        &self,
        expression: &Expression,
        parameters: &[LocalId],
        monotypes: &Monotypes,
    ) -> bool {
        let mut found = false;
        visit(expression, &mut |node| {
            found |= match &node.kind {
                ExpressionKind::Foreign { foreign, .. } => foreign_suspends(foreign),
                ExpressionKind::Function(id) => self.suspending[id.0 as usize],
                ExpressionKind::Apply { function, .. } => {
                    !matches!(
                        function.kind,
                        ExpressionKind::Function(_) | ExpressionKind::Lambda { .. }
                    ) && is_effect(node.monotype, monotypes)
                }
                ExpressionKind::Local(id) => {
                    !parameters.contains(id) && is_effect(node.monotype, monotypes)
                }
                ExpressionKind::Access { .. }
                | ExpressionKind::Coerce(_)
                | ExpressionKind::Closure { .. } => is_effect(node.monotype, monotypes),
                _ => false,
            };
        });
        found
    }
}

fn suspends_directly(function: &Function, monotypes: &Monotypes) -> bool {
    let mut found = false;
    visit(&function.body, &mut |node| {
        found |= match &node.kind {
            ExpressionKind::Foreign { foreign, .. } => foreign_suspends(foreign),
            ExpressionKind::Apply { function, .. } => {
                !matches!(
                    function.kind,
                    ExpressionKind::Function(_) | ExpressionKind::Lambda { .. }
                ) && is_effect(node.monotype, monotypes)
            }
            ExpressionKind::Local(_)
            | ExpressionKind::Access { .. }
            | ExpressionKind::Coerce(_)
            | ExpressionKind::Closure { .. } => is_effect(node.monotype, monotypes),
            _ => false,
        };
    });
    found
}

fn foreign_suspends(foreign: &Foreign) -> bool {
    match foreign {
        Foreign::Perform { function, .. } | Foreign::Call { function, .. } => matches!(
            function.package,
            GoPackage::Aff
                | GoPackage::AVar
                | GoPackage::Promise
                | GoPackage::YogaOm
                | GoPackage::Tauri
        ),
        Foreign::MakeAff | Foreign::ForkFiber | Foreign::NewFiber | Foreign::NewSupervisedFiber => {
            true
        }
        Foreign::Project { effectful, .. } => *effectful,
        _ => false,
    }
}

fn is_effect(monotype: crate::monotype::MonotypeId, monotypes: &Monotypes) -> bool {
    match monotypes.get(monotype) {
        Monotype::Effect(_) => true,
        Monotype::Function(_, result) | Monotype::Array(result) => is_effect(*result, monotypes),
        _ => false,
    }
}
