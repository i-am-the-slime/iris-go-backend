//! Functions that call each other in tail position, such as `isEven` and `isOdd`, run as one
//! loop: a Go function `isEvenOrIsOdd(step, …)` whose `for { switch step { … } }` holds every
//! member's body, so that a tail call between members reassigns the parameters and the step
//! instead of growing the stack. Each member keeps its name as a thin entry that starts the loop
//! at its own step. A call between members that is not in tail position calls that entry.

use rustc_hash::FxHashSet;

use super::{
    Emitter, LoopTarget, Mode, Sink, TailLoop, call, captures_parameters, identifier_expression,
};
use crate::error::GoResult;
use crate::graph::strongly_connected;
use crate::monomorphic::{Expression, ExpressionKind, Function, FunctionId, Guarded, Program};
use crate::monotype::Monotypes;
use crate::naming::capitalise;
use crate::syntax::{GoCase, GoDeclaration, GoDefault, GoExpression, GoStatement, GoType};

use super::packages::Spelling;

/// Members of a strongly connected component of the tail-call graph, in program order.
pub(super) struct TailGroup {
    pub members: Vec<FunctionId>,
    /// The Go function running the loop, and the constant naming each member's step.
    pub name: String,
    pub steps: Vec<String>,
}

/// The strongly connected components of two or more functions in the graph whose edges are
/// saturated calls in tail position.
pub(super) fn tail_call_groups(
    program: &Program,
    monotypes: &Monotypes,
    lazy_constants: &FxHashSet<FunctionId>,
) -> Vec<Vec<FunctionId>> {
    let looping = |id: FunctionId| {
        !program.function(id).parameters.is_empty() && !lazy_constants.contains(&id)
    };
    let successors = (0..program.functions.len()).map(|index| {
        let id = FunctionId(index as u32);
        if !looping(id) {
            return vec![];
        }
        let function = program.function(id);
        let mode = mode_of(function, monotypes);
        let mut callees = vec![];
        tail_callees(&function.body, mode, program, &mut callees);
        callees.retain(|callee| looping(*callee) && *callee != id);
        callees.sort_unstable_by_key(|callee| callee.0);
        callees.dedup();
        callees.into_iter().map(|callee| callee.0 as usize).collect()
    });
    let successors: Vec<Vec<usize>> = successors.collect();
    let groups = strongly_connected(&successors)
        .into_iter()
        .filter(|component| component.len() > 1)
        .map(|mut component| {
            component.sort_unstable();
            component.into_iter().map(|index| FunctionId(index as u32)).collect()
        });
    groups.collect()
}

fn mode_of(function: &Function, monotypes: &Monotypes) -> Mode {
    if monotypes.effect_result(function.result).is_some() { Mode::Perform } else { Mode::Value }
}

/// The functions that `expression` calls, saturated, in tail position; the positions
/// `has_tail_call` recognises for a function calling itself.
fn tail_callees(
    expression: &Expression,
    mode: Mode,
    program: &Program,
    callees: &mut Vec<FunctionId>,
) {
    match &expression.kind {
        ExpressionKind::Apply { function, arguments } => {
            if let ExpressionKind::Function(id) = function.kind
                && program.function(id).parameters.len() == arguments.len()
            {
                callees.push(id);
            }
        }
        ExpressionKind::Let { body, .. } => tail_callees(body, mode, program, callees),
        ExpressionKind::If { then, otherwise, .. } => {
            tail_callees(then, mode, program, callees);
            tail_callees(otherwise, mode, program, callees);
        }
        ExpressionKind::Case { alternatives, .. } => {
            for alternative in alternatives {
                match &alternative.body {
                    Guarded::Unconditional(body) => tail_callees(body, mode, program, callees),
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            tail_callees(&branch.body, mode, program, callees);
                        }
                    }
                }
            }
        }
        ExpressionKind::EffectBind { body, .. } if mode == Mode::Perform => {
            tail_callees(body, mode, program, callees);
        }
        _ => {}
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// Names each group's loop function after its members, once the members have their names.
    pub(super) fn name_tail_groups(&mut self, groups: Vec<Vec<FunctionId>>) {
        for members in groups {
            let first = self.function_names[members[0].0 as usize].clone();
            let suffix = if members.len() == 2 {
                format!("Or{}", capitalise(&self.function_names[members[1].0 as usize]))
            } else {
                "Group".to_string()
            };
            let name = self.global_name(Spelling::derived("", first, &suffix));
            let steps = members.iter().map(|member| {
                let parent = self.function_names[member.0 as usize].clone();
                self.global_name(Spelling::derived("", parent, "Step"))
            });
            let steps = steps.collect();
            let group = self.tail_groups.len();
            for member in &members {
                self.tail_group_of.insert(*member, group);
            }
            self.tail_groups.push(TailGroup { members, name, steps });
        }
    }

    /// The name of a function as code refers to it, noting the reference.
    pub(super) fn function_reference(&self, id: FunctionId) -> &str {
        self.referenced.borrow_mut().insert(id);
        &self.function_names[id.0 as usize]
    }

    /// The entries of group members that no emitted code calls, since only other members reach
    /// them, by a jump inside the loop; never the program's entry, which `main` calls.
    pub(super) fn unused_tail_group_entries(&self) -> FxHashSet<String> {
        let referenced = self.referenced.borrow();
        self.tail_group_of
            .keys()
            .filter(|member| **member != self.program.entry && !referenced.contains(member))
            .map(|member| self.function_names[member.0 as usize].clone())
            .collect()
    }

    /// A member's entry, preceded by the group's steps and loop when it is the first member.
    pub(super) fn tail_group_member(
        &mut self,
        id: FunctionId,
        group: usize,
    ) -> GoResult<Vec<GoDeclaration>> {
        let mut declarations = vec![];
        if self.tail_groups[group].members[0] == id {
            let steps = self.tail_groups[group].steps.clone();
            declarations.push(GoDeclaration::Constants {
                type_name: None,
                names: steps,
                line: None,
                member_lines: vec![],
            });
            declarations.push(self.tail_group_loop(group)?);
        }
        declarations.push(self.tail_group_entry(id, group)?);
        Ok(declarations)
    }

    /// `func isEven(k int) bool { return isEvenOrIsOdd(isEvenStep, k) }`.
    fn tail_group_entry(&mut self, id: FunctionId, group: usize) -> GoResult<GoDeclaration> {
        let function: &Function = self.program.function(id);
        self.current = Some(id);
        self.locals.clear();
        self.local_names.clear();
        let slots = self.tail_group_slots(group)?;
        let members = &self.tail_groups[group].members;
        let member = members.iter().position(|candidate| *candidate == id).unwrap();
        let mut parameters = vec![];
        for parameter in &function.parameters {
            let name = self.bind_local(parameter);
            parameters.push((name, self.go_type(parameter.monotype)?));
        }
        let mut body = vec![];
        let mut arguments = vec![identifier_expression(&self.tail_groups[group].steps[member])];
        for (slot, (slot_name, slot_type)) in slots.slots.iter().enumerate() {
            let own = slots.assignment[member].iter().position(|assigned| *assigned == slot);
            let argument = match own {
                Some(position) => identifier_expression(&parameters[position].0),
                None => match zero_value(slot_type) {
                    Some(zero) => zero,
                    None => {
                        let name = self.local_name(slot_name.clone());
                        body.push(GoStatement::Variable {
                            name: name.clone(),
                            type_: slot_type.clone(),
                            value: None,
                        });
                        identifier_expression(&name)
                    }
                },
            };
            arguments.push(argument);
        }
        let effect_result = self.monotypes.effect_result(function.result);
        let result = self.go_result(effect_result.unwrap_or(function.result))?;
        let looped = call(identifier_expression(&self.tail_groups[group].name), arguments);
        body.push(match result {
            None => GoStatement::Expression(looped),
            Some(_) => GoStatement::Return(Some(looped)),
        });
        let name = self.function_names[id.0 as usize].clone();
        Ok(GoDeclaration::Function { name, parameters, result, body })
    }

    /// `func isEvenOrIsOdd(step int, k int) bool { for { switch step { … } } }`.
    fn tail_group_loop(&mut self, group: usize) -> GoResult<GoDeclaration> {
        let members = self.tail_groups[group].members.clone();
        let steps = self.tail_groups[group].steps.clone();
        self.locals.clear();
        self.local_names.clear();
        let step = self.local_name("step".into());
        let slots = self.tail_group_slots(group)?;
        let slot_names = slots.slots.iter().map(|(name, _)| self.local_name(name.clone()));
        let slot_names: Vec<String> = slot_names.collect();
        let mut parameters = vec![(step.clone(), GoType::Int)];
        for ((_, type_), name) in slots.slots.iter().zip(&slot_names) {
            parameters.push((name.clone(), type_.clone()));
        }
        let targets = members.iter().enumerate().map(|(member, id)| LoopTarget {
            function: *id,
            parameters: slots.assignment[member]
                .iter()
                .map(|slot| identifier_expression(&slot_names[*slot]))
                .collect(),
            step: Some(identifier_expression(&steps[member])),
        });
        let targets: Vec<LoopTarget> = targets.collect();
        let mut reassigned = slot_names.clone();
        reassigned.push(step.clone());
        let first: &Function = self.program.function(members[0]);
        let mode = mode_of(first, self.monotypes);
        let effect_result = self.monotypes.effect_result(first.result);
        let result = self.go_result(effect_result.unwrap_or(first.result))?;
        let mut cases = vec![];
        for (member, id) in members.iter().enumerate() {
            let function: &Function = self.program.function(*id);
            self.current = Some(*id);
            let mut body = vec![];
            for (position, parameter) in function.parameters.iter().enumerate() {
                let slot = &slot_names[slots.assignment[member][position]];
                self.locals.insert(parameter.id, identifier_expression(slot));
                let captured = captures_parameters(
                    &function.body,
                    std::slice::from_ref(parameter),
                    mode,
                    self.monotypes,
                );
                if captured {
                    let copy = self.local_name(format!("{slot}Captured"));
                    self.locals.insert(parameter.id, identifier_expression(&copy));
                    body.push(GoStatement::Define {
                        names: vec![copy],
                        values: vec![identifier_expression(slot)],
                    });
                }
            }
            self.tail_loop = Some(TailLoop {
                parameters: reassigned.clone(),
                targets: targets.clone(),
                current: *id,
                step: Some(step.clone()),
            });
            let emitted = self.sink(&function.body, mode, Sink::Return, &mut body);
            self.tail_loop = None;
            emitted?;
            if let Some(GoStatement::Continue) = body.last() {
                body.pop();
            } else if result.is_none() && !terminates(&body) {
                body.push(GoStatement::Return(None));
            }
            let values = vec![identifier_expression(&steps[member])];
            cases.push(GoCase { values, body, line: None });
        }
        let default = GoDefault::covering(&mut cases);
        let switch = GoStatement::Switch {
            value: Some(identifier_expression(&step)),
            cases,
            default: Some(default),
        };
        let name = self.tail_groups[group].name.clone();
        Ok(GoDeclaration::Function {
            name,
            parameters,
            result,
            body: vec![GoStatement::Loop(vec![switch])],
        })
    }

    /// The loop's parameter variables: each member's parameters, sharing a variable with an
    /// earlier member's parameter of the same Go type, so that members alike in their parameters,
    /// as `isEven` and `isOdd` are, share all of them.
    fn tail_group_slots(&mut self, group: usize) -> GoResult<Slots> {
        let members = self.tail_groups[group].members.clone();
        let mut slots: Vec<(String, GoType)> = vec![];
        let mut assignment = vec![];
        for id in members {
            let function: &Function = self.program.function(id);
            let mut taken: Vec<usize> = vec![];
            for parameter in &function.parameters {
                let type_ = self.go_type(parameter.monotype)?;
                let shared = slots.iter().enumerate().position(|(slot, (_, slot_type))| {
                    *slot_type == type_ && !taken.contains(&slot)
                });
                let slot = match shared {
                    Some(slot) => slot,
                    None => {
                        let base = self.local_base(&parameter.name, parameter.monotype);
                        slots.push((base, type_));
                        slots.len() - 1
                    }
                };
                taken.push(slot);
            }
            assignment.push(taken);
        }
        Ok(Slots { slots, assignment })
    }
}

struct Slots {
    /// Each variable's base name and type.
    slots: Vec<(String, GoType)>,
    /// For each member, the variable holding each of its parameters.
    assignment: Vec<Vec<usize>>,
}

/// The literal of a type's zero value, where Go has a short one.
fn zero_value(type_: &GoType) -> Option<GoExpression> {
    match type_ {
        GoType::Int | GoType::Float64 | GoType::Rune => Some(GoExpression::Integer(0)),
        GoType::Named(name) if matches!(name.as_str(), "int32" | "float64" | "int" | "rune") => {
            Some(GoExpression::Integer(0))
        }
        GoType::Bool => Some(GoExpression::Boolean(false)),
        GoType::String => Some(GoExpression::String(String::new())),
        GoType::Pointer(_)
        | GoType::Slice(_)
        | GoType::Function { .. }
        | GoType::Any
        | GoType::Erased(_) => Some(GoExpression::nil()),
        _ => None,
    }
}

/// Whether control cannot fall out of the end of the statements.
fn terminates(statements: &[GoStatement]) -> bool {
    match statements.last() {
        Some(GoStatement::Return(_) | GoStatement::Continue) => true,
        Some(statement) if statement.is_panic() => true,
        Some(GoStatement::If { then, otherwise, .. }) => terminates(then) && terminates(otherwise),
        Some(GoStatement::Switch { cases, default: Some(default), .. }) => {
            cases.iter().all(|case| terminates(&case.body)) && terminates(&default.body)
        }
        _ => false,
    }
}
