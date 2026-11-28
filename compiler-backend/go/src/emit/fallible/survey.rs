use rustc_hash::{FxHashMap, FxHashSet};

use super::syntax::{joined_results, terminates};
use super::{EitherShape, values};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoExpression, GoStatement, GoType, Name};

/// What the survey of a declaration learns about a local holding an `Either`.
pub(super) struct Candidate {
    pub(super) shape: String,
    /// Calls of fallible functions it holds the result of.
    pub(super) calls: usize,
    /// Whether a statement after its definition assigns it again.
    pub(super) reassigned: bool,
    /// Whether it reads the `Left` where only an `if` that returned before tells it is one, which
    /// holds as long as nothing assigns it again.
    read_after_early_return: bool,
    /// Whether a `var` declares it for the branches that follow to store into.
    joins: bool,
    /// Whether it is used in a way the two locals can't stand for.
    escapes: bool,
    /// The two locals of the last `EFromResults(value, err)` it holds.
    pub(super) results: Option<(String, String)>,
}

impl Candidate {
    /// A parameter, which the calls store into as branches store into a joining local.
    pub(super) fn parameter(shape: &str) -> Candidate {
        Candidate {
            shape: shape.to_string(),
            calls: 0,
            reassigned: false,
            read_after_early_return: false,
            joins: true,
            escapes: false,
            results: None,
        }
    }

    /// Whether the local becomes two: it holds a call's two results, joins branches or changes,
    /// as a fold's accumulator does.
    pub(super) fn splits(&self) -> bool {
        let stays_known = !(self.reassigned && self.read_after_early_return);
        let worth_it = self.calls > 0 || self.joins || self.reassigned;
        !self.escapes && stays_known && worth_it
    }
}
/// The survey of a function body for the locals that can become two.
pub(super) struct Survey<'s> {
    shapes: &'s FxHashMap<String, EitherShape>,
    callable: &'s FxHashMap<String, String>,
    parameters: &'s FxHashMap<String, FxHashMap<usize, String>>,
    split_parameters: &'s FxHashMap<String, FxHashMap<usize, String>>,
    binders: &'s FxHashMap<String, usize>,
    pub(super) candidates: FxHashMap<String, Candidate>,
    /// What the code knows about the candidates where it is.
    facts: Vec<Fact>,
}

/// That a candidate holds a `Left` or a `Right` where the code is.
struct Fact {
    local: String,
    left: bool,
    /// Whether an `if` that returned before tells.
    early: bool,
    /// Whether a statement since assigned the candidate, so that it no longer holds.
    stale: bool,
}

/// Marks a read of the field both sides of an `Either Int Int` share as one of the `Left` or the
/// `Right`, for the rewrite.
const SIDE_MARK: char = '\u{1}';

pub(super) fn marked_side(field: &str, left: bool) -> String {
    format!("{SIDE_MARK}{}{field}", if left { 'L' } else { 'R' })
}

/// The side a marked field read reads, `true` for the `Left`, and the field.
pub(super) fn read_side(field: &str) -> Option<(bool, &str)> {
    let rest = field.strip_prefix(SIDE_MARK)?;
    Some((rest.starts_with('L'), &rest[1..]))
}

/// Unmarks the shared field reads of the locals that stay `Either` structs.
pub(super) fn unmark_sides(body: &mut [GoStatement], kept: &impl Fn(&str) -> bool) {
    for statement in body.iter_mut() {
        go_traversal::each_expression_in_statement(statement, |expression| {
            if let GoExpression::Field { value, name } = expression
                && let Some((_, field)) = read_side(name)
                && let GoExpression::Identifier(local) = value.unattributed()
                && !kept(local)
            {
                *name = field.to_string();
            }
        });
    }
}

/// The branches of one statement: each starts from what held before it, and after the statement
/// a fact holds only if no branch assigned its candidate.
struct Branches {
    before: Vec<bool>,
    after: Vec<bool>,
}

impl Branches {
    fn start(survey: &Survey<'_>) -> Branches {
        let before: Vec<bool> = survey.facts.iter().map(|fact| fact.stale).collect();
        Branches { after: before.clone(), before }
    }

    fn enter(&self, survey: &mut Survey<'_>) {
        for (fact, stale) in survey.facts.iter_mut().zip(&self.before) {
            fact.stale = *stale;
        }
    }

    fn leave(&mut self, survey: &Survey<'_>) {
        for (stale, fact) in self.after.iter_mut().zip(&survey.facts) {
            *stale |= fact.stale;
        }
    }

    fn end(self, survey: &mut Survey<'_>) {
        for (fact, stale) in survey.facts.iter_mut().zip(&self.after) {
            fact.stale = *stale;
        }
    }
}

/// The locals the statements assign to, in loops and branches too.
fn assigned_in(body: &mut [GoStatement]) -> FxHashSet<String> {
    let mut assigned = FxHashSet::default();
    crate::syntax::statements_names(body, &mut |name| {
        if let Name::Written(name) = name {
            assigned.insert(name.clone());
        }
    });
    assigned
}

impl<'s> Survey<'s> {
    pub(super) fn new(
        shapes: &'s FxHashMap<String, EitherShape>,
        callable: &'s FxHashMap<String, String>,
        parameters: &'s FxHashMap<String, FxHashMap<usize, String>>,
        split_parameters: &'s FxHashMap<String, FxHashMap<usize, String>>,
        binders: &'s FxHashMap<String, usize>,
    ) -> Survey<'s> {
        Survey {
            shapes,
            callable,
            parameters,
            split_parameters,
            binders,
            candidates: FxHashMap::default(),
            facts: vec![],
        }
    }

    pub(super) fn block(&mut self, statements: &mut [GoStatement], own: Option<&str>) {
        let known = self.facts.len();
        for statement in statements {
            self.statement(statement, own);
            if let GoStatement::If { condition, then, otherwise } = statement
                && otherwise.is_empty()
                && terminates(then)
                && let Some((local, left)) = self.tag_test(condition)
            {
                self.facts.push(Fact { local, left: !left, early: true, stale: false });
            }
        }
        self.facts.truncate(known);
    }

    fn candidate_target(&self, target: &GoExpression) -> Option<String> {
        match target.unattributed() {
            GoExpression::Identifier(local) if self.candidates.contains_key(local) => {
                Some(local.clone())
            }
            _ => None,
        }
    }

    /// The tag test a condition starts with, `local.Tag == tag && …`, which holds wherever the
    /// whole condition does.
    fn leading_tag_test(&self, condition: &GoExpression) -> Option<(String, bool)> {
        match condition.unattributed() {
            GoExpression::Binary { operator: "&&", left, .. } => self.leading_tag_test(left),
            condition => self.tag_test(condition),
        }
    }

    /// Forgets what the code knew about the candidate.
    fn assigned(&mut self, local: &str) {
        for fact in self.facts.iter_mut().filter(|fact| fact.local == local) {
            fact.stale = true;
        }
    }

    /// The `Either` type of a value a local is defined as, when it can be split.
    fn source_shape(&self, value: &GoExpression) -> Option<String> {
        if let Some((shape, _, _)) = joined_results(value) {
            return self.shapes.contains_key(&shape).then_some(shape);
        }
        match value.unattributed() {
            GoExpression::Call { function, .. } => match function.unattributed() {
                GoExpression::Identifier(name) => self.callable.get(name).cloned(),
                _ => None,
            },
            GoExpression::Composite { type_: GoType::Named(name), .. }
                if self.shapes.contains_key(name) =>
            {
                Some(name.clone())
            }
            _ => None,
        }
    }

    fn consider(&mut self, local: &str, shape: String, joins: bool) {
        if self.binders.get(local) != Some(&1) {
            return;
        }
        self.candidates.insert(
            local.to_string(),
            Candidate {
                shape,
                calls: 0,
                reassigned: false,
                read_after_early_return: false,
                joins,
                escapes: false,
                results: None,
            },
        );
    }

    /// The body of a function literal that returns two results.
    fn converted_literal(&mut self, literal: &mut GoExpression, shape: &str) {
        match literal {
            GoExpression::Attributed { value, .. } => self.converted_literal(value, shape),
            GoExpression::Function { body, .. } => self.block(body, Some(shape)),
            value => self.expression(value),
        }
    }

    /// A value stored into a candidate: a fallible call or a construction of its type.
    fn source(&mut self, local: &str, value: &mut GoExpression) {
        let Some(candidate) = self.candidates.get(local) else {
            self.expression(value);
            return;
        };
        let shape = candidate.shape.clone();
        let is_call = self.source_shape(value).as_ref() == Some(&shape)
            && matches!(value.unattributed(), GoExpression::Call { .. });
        let construction = match self.source_shape(value).as_ref() == Some(&shape) {
            true => self.shapes[&shape].construction(value),
            false => None,
        };
        let is_construction = construction.is_some();
        let joined = joined_results(value);
        let candidate = self.candidates.get_mut(local).expect("invariant violated: a candidate");
        if is_call {
            candidate.calls += 1;
            candidate.results = joined.map(|(_, value, failure)| (value, failure));
            self.expression(value);
            return;
        } else if !is_construction {
            candidate.escapes = true;
            self.expression(value);
            return;
        }
        match value {
            GoExpression::Attributed { value, .. } => self.children(value),
            value => self.children(value),
        }
    }

    fn children(&mut self, value: &mut GoExpression) {
        struct Children<'a, 's>(&'a mut Survey<'s>);
        impl Walk for Children<'_, '_> {
            fn expression(&mut self, value: &mut GoExpression) {
                self.0.expression(value);
            }
            fn block(&mut self, _: &mut Vec<GoStatement>) {}
        }
        go_traversal::expression(&mut Children(self), value);
    }

    fn statement(&mut self, statement: &mut GoStatement, own: Option<&str>) {
        match statement {
            GoStatement::Define { names, values }
                if let ([local], [value]) = (names.as_slice(), values.as_slice())
                    && self.callable.contains_key(local)
                    && matches!(value.unattributed(), GoExpression::Function { .. }) =>
            {
                let shape = self.callable[&names[0]].clone();
                self.converted_literal(&mut values[0], &shape);
            }
            GoStatement::Define { names, values } if names.len() == 1 && values.len() == 1 => {
                if let Some(shape) = self.source_shape(&values[0]) {
                    self.consider(&names[0], shape, false);
                }
                let name = names[0].clone();
                self.source(&name, &mut values[0]);
            }
            GoStatement::Variable { name, type_, value } => {
                if let GoType::Named(shape) = type_
                    && self.shapes.contains_key(shape)
                {
                    self.consider(name, shape.clone(), true);
                }
                let name = name.clone();
                if let Some(value) = value {
                    self.source(&name, value);
                }
            }
            GoStatement::Assign { targets, values }
                if targets.len() == 1
                    && values.len() == 1
                    && let GoExpression::Identifier(target) = targets[0].unattributed()
                    && self.candidates.contains_key(target) =>
            {
                let target = target.clone();
                if let Some(candidate) = self.candidates.get_mut(&target) {
                    candidate.reassigned = true;
                }
                self.source(&target, &mut values[0]);
                self.assigned(&target);
            }
            GoStatement::Assign { targets, values }
                if targets.len() == values.len()
                    && targets.len() > 1
                    && targets.iter().any(|target| self.candidate_target(target).is_some()) =>
            {
                let mut stored = vec![];
                for (target, value) in targets.iter_mut().zip(values.iter_mut()) {
                    let Some(local) = self.candidate_target(target) else {
                        self.expression(target);
                        self.expression(value);
                        continue;
                    };
                    let shape = self.candidates[&local].shape.clone();
                    let constructs = self.shapes[&shape].construction(value).is_some();
                    let candidate =
                        self.candidates.get_mut(&local).expect("invariant violated: a candidate");
                    candidate.reassigned = true;
                    candidate.escapes |= !constructs;
                    self.source(&local, value);
                    stored.push(local);
                }
                for local in stored {
                    self.assigned(&local);
                }
            }
            GoStatement::Return(Some(value))
                if let GoExpression::Identifier(local) = value.unattributed()
                    && let Some(candidate) = self.candidates.get_mut(local) =>
            {
                if own != Some(candidate.shape.as_str()) {
                    candidate.escapes = true;
                }
            }
            GoStatement::Switch { value: Some(scrutinee), cases, default }
                if let Some(local) = self.tagged(scrutinee) =>
            {
                let shape = &self.shapes[&self.candidates[&local].shape];
                let sides: Vec<Option<bool>> = cases
                    .iter()
                    .map(|case| {
                        let sides: Vec<Option<bool>> =
                            case.values.iter().map(|value| shape.is_left_tag(value)).collect();
                        match sides.as_slice() {
                            [side] => *side,
                            _ => None,
                        }
                    })
                    .collect();
                let undecided = sides.iter().any(Option::is_none)
                    || cases.len() + usize::from(default.is_some()) != 2
                    || (default.is_none() && sides.iter().all(|side| *side == sides[0]));
                if undecided && let Some(candidate) = self.candidates.get_mut(&local) {
                    candidate.escapes = true;
                }
                let mut seen_left = false;
                let mut branches = Branches::start(self);
                for (case, side) in cases.iter_mut().zip(&sides) {
                    let side = side.unwrap_or(false);
                    seen_left |= side;
                    branches.enter(self);
                    self.with_fact(&local, side, |survey| survey.block(&mut case.body, own));
                    branches.leave(self);
                }
                if let Some(default) = default {
                    branches.enter(self);
                    self.with_fact(&local, !seen_left, |survey| {
                        survey.block(&mut default.body, own)
                    });
                    branches.leave(self);
                }
                branches.end(self);
            }
            GoStatement::If { condition, then, otherwise }
                if let Some((local, left)) = self.tag_test(condition) =>
            {
                let mut branches = Branches::start(self);
                branches.enter(self);
                self.with_fact(&local, left, |survey| survey.block(then, own));
                branches.leave(self);
                branches.enter(self);
                self.with_fact(&local, !left, |survey| survey.block(otherwise, own));
                branches.leave(self);
                branches.end(self);
            }
            GoStatement::If { condition, then, otherwise }
                if let Some((local, left)) = self.leading_tag_test(condition) =>
            {
                self.expression(condition);
                let mut branches = Branches::start(self);
                branches.enter(self);
                self.with_fact(&local, left, |survey| survey.block(then, own));
                branches.leave(self);
                branches.enter(self);
                self.block(otherwise, own);
                branches.leave(self);
                branches.end(self);
            }
            statement => {
                struct Inner<'a, 's> {
                    survey: &'a mut Survey<'s>,
                    own: Option<&'a str>,
                    branches: Branches,
                }
                impl Walk for Inner<'_, '_> {
                    fn expression(&mut self, value: &mut GoExpression) {
                        self.survey.expression(value);
                    }
                    fn block(&mut self, body: &mut Vec<GoStatement>) {
                        self.branches.enter(self.survey);
                        self.survey.block(body, self.own);
                        self.branches.leave(self.survey);
                    }
                }
                if let GoStatement::Loop(body)
                | GoStatement::LabeledLoop { body, .. }
                | GoStatement::Range { body, .. }
                | GoStatement::Counting { body, .. }
                | GoStatement::CountingDown { body, .. } = &mut *statement
                {
                    for local in assigned_in(body) {
                        self.assigned(&local);
                    }
                }
                let branches = Branches::start(self);
                let mut inner = Inner { survey: self, own, branches };
                go_traversal::statement(&mut inner, statement);
                let Inner { branches, .. } = inner;
                branches.end(self);
            }
        }
    }

    fn with_fact(&mut self, local: &str, left: bool, visit: impl FnOnce(&mut Survey<'s>)) {
        self.facts.push(Fact { local: local.to_string(), left, early: false, stale: false });
        visit(self);
        self.facts.pop();
    }

    /// Whether the local holds a `Left` (`true`) or a `Right` where the code is, and whether an
    /// early return tells.
    fn known_side(&self, local: &str) -> Option<(bool, bool)> {
        let fact = self.facts.iter().rev().find(|fact| fact.local == local)?;
        (!fact.stale).then_some((fact.left, fact.early))
    }

    /// The candidate whose tag the value reads.
    fn tagged(&self, value: &GoExpression) -> Option<String> {
        let GoExpression::Field { value, name } = value.unattributed() else { return None };
        let GoExpression::Identifier(local) = value.unattributed() else { return None };
        (name == "Tag" && self.candidates.contains_key(local)).then(|| local.clone())
    }

    /// `local.Tag == tag` of a candidate, with whether it holds when the local is a `Left`.
    fn tag_test(&self, condition: &GoExpression) -> Option<(String, bool)> {
        let GoExpression::Binary { operator, left, right } = condition.unattributed() else {
            return None;
        };
        if !matches!(*operator, "==" | "!=") {
            return None;
        }
        let (local, tag) = match self.tagged(left) {
            Some(local) => (local, right),
            None => (self.tagged(right)?, left),
        };
        let is_left = self.shapes[&self.candidates[&local].shape].is_left_tag(tag)?;
        Some((local, (*operator == "==") == is_left))
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Identifier(name) => {
                if let Some(candidate) = self.candidates.get_mut(name.as_str()) {
                    candidate.escapes = true;
                }
            }
            GoExpression::Field { value: inner, name }
                if let GoExpression::Identifier(local) = inner.unattributed()
                    && self.candidates.contains_key(local) =>
            {
                let local = local.clone();
                let shape = &self.shapes[&self.candidates[&local].shape];
                let known = self.known_side(&local);
                let shared = shape.shares_field() && *name == shape.left_field;
                let left_read = *name == shape.left_field;
                let right_read = *name == shape.right_field;
                let Some(candidate) = self.candidates.get_mut(&local) else { return };
                match known {
                    Some((true, early)) if left_read => {
                        candidate.read_after_early_return |= early;
                        if shared {
                            *name = marked_side(name, true);
                        }
                    }
                    Some((false, _)) if right_read && shared => *name = marked_side(name, false),
                    _ if right_read && !shared => {}
                    _ => candidate.escapes = true,
                }
            }
            GoExpression::Function { body, .. } => self.block(body, None),
            GoExpression::Call { function, arguments }
                if let GoExpression::Identifier(head) = function.unattributed()
                    && let Some(shape) = head.strip_prefix(values::LITERAL_MARK) =>
            {
                let shape = shape.to_string();
                for argument in arguments.iter_mut() {
                    self.converted_literal(argument, &shape);
                }
            }
            GoExpression::Call { function, arguments }
                if let GoExpression::Identifier(head) = function.unattributed()
                    && (self.parameters.contains_key(head)
                        || self.split_parameters.contains_key(head)) =>
            {
                let empty = FxHashMap::default();
                let slots = self.parameters.get(head).unwrap_or(&empty);
                let split = self.split_parameters.get(head).unwrap_or(&empty);
                for (index, argument) in arguments.iter_mut().enumerate() {
                    match (slots.get(&index), split.get(&index)) {
                        (Some(shape), _) => self.converted_literal(argument, shape),
                        (None, Some(shape)) => match argument {
                            GoExpression::Identifier(local)
                                if self
                                    .candidates
                                    .get(local.as_str())
                                    .is_some_and(|candidate| candidate.shape == *shape) => {}
                            GoExpression::Attributed { value, .. } => self.children(value),
                            argument => self.children(argument),
                        },
                        (None, None) => self.expression(argument),
                    }
                }
            }
            GoExpression::Binary { operator: "&&", left, right }
                if let Some((local, side)) = self.leading_tag_test(left) =>
            {
                self.expression(left);
                self.with_fact(&local, side, |survey| survey.expression(right));
            }
            value if self.tag_test(value).is_some() => {}
            value => self.children(value),
        }
    }
}
