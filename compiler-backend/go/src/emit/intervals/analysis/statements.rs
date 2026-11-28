use rustc_hash::FxHashMap;

use super::loops::Header;
use super::values::Computed;
use super::{Analysis, Frame};
use crate::emit::intervals::constraints::{Kind, State, Symbol, Typing, Value, ZERO, kind_of_type};
use crate::emit::intervals::names::shape_of_type;
use crate::emit::intervals::syntax::{is_bounds_test, is_test};
use crate::syntax::{GoBuiltin, GoExpression, GoStatement, GoUnaryOperator};

impl Analysis<'_, '_, '_> {
    pub(super) fn block(&mut self, body: &mut Vec<GoStatement>, state: &mut State) {
        let watermark = self.next;
        self.scopes.push(FxHashMap::default());
        let mut position = 0;
        while position < body.len() {
            if state.unreachable {
                break;
            }
            if self.rewriting() && self.rewrite_statement(body, position, state) {
                continue;
            }
            // A bounds test bound to a name is rewritten after it is interpreted, so that the
            // name stands for the test as written.
            let before =
                (self.rewriting() && is_bound_bounds_test(&body[position])).then(|| state.clone());
            let from = self.temporaries.len();
            self.statement(&mut body[position], state);
            self.forget_temporaries(state, from);
            if let Some(before) = before
                && let GoStatement::Define { values, .. } = &mut body[position]
            {
                self.simplify_test(&mut values[0], &before);
            }
            position += 1;
        }
        self.scopes.pop();
        self.restrict(state, watermark);
    }

    fn statement(&mut self, statement: &mut GoStatement, state: &mut State) {
        // A call's arguments are read before it runs, and the values assigned after.
        let keeps = !is_leaf(statement) || self.keeps(statement, state);
        match statement {
            GoStatement::Define { names, values } => {
                values.iter_mut().for_each(|value| self.visit(value, state));
                if !keeps {
                    self.forget_heap(state);
                }
                self.define(names, values, state);
            }
            GoStatement::Variable { name, type_, value } => {
                if let Some(value) = value {
                    self.visit(value, state);
                }
                if !keeps {
                    self.forget_heap(state);
                }
                let zero = GoExpression::Integer(0);
                let value = value.clone();
                let kind = kind_of_type(type_);
                let shape = shape_of_type(type_);
                let computed = match &value {
                    Some(value) => self.computed(value, state),
                    None if kind.is_some() => self.computed(&zero, state),
                    None => Computed {
                        length: shape.map(|_| Value::constant(0)),
                        ..Computed::default()
                    },
                };
                let symbol = self.bind(name, kind, shape, state);
                self.settle(symbol, computed, state);
            }
            GoStatement::Assign { targets, values } => {
                values.iter_mut().for_each(|value| self.visit(value, state));
                targets.iter_mut().for_each(|target| self.visit_target(target, state));
                self.observe_stores(targets, values, state);
                if !keeps {
                    self.forget_heap(state);
                }
                self.assign(targets, values, state);
            }
            GoStatement::Expression(value) => {
                let panics = matches!(value, GoExpression::Call { function, .. }
                    if function.is_builtin(GoBuiltin::Panic));
                self.visit(value, state);
                if !keeps {
                    self.forget_heap(state);
                }
                if panics {
                    *state = State::unreachable();
                }
            }
            GoStatement::Defer(value) => self.visit(value, state),
            GoStatement::Return(value) => {
                if let Some(value) = value {
                    self.visit(value, state);
                }
                *state = State::unreachable();
            }
            GoStatement::If { condition, then, otherwise } => {
                self.visit(condition, state);
                if !self.keeps_expression(condition, state) {
                    self.forget_heap(state);
                }
                let (mut passed, mut failed) = if self.informs(condition) {
                    (self.assume(state, condition, true), self.assume(state, condition, false))
                } else {
                    (state.clone(), std::mem::take(state))
                };
                self.block(then, &mut passed);
                self.block(otherwise, &mut failed);
                *state = passed.join(&failed);
            }
            GoStatement::Switch { value, cases, default } => {
                if let Some(value) = value {
                    self.visit(value, state);
                    if !self.keeps_expression(value, state) {
                        self.forget_heap(state);
                    }
                }
                let tested = value.is_none();
                let mut rest = state.clone();
                let mut ends = State::unreachable();
                self.frames.push(Frame {
                    label: None,
                    switch: true,
                    breaks: State::unreachable(),
                    continues: State::unreachable(),
                });
                for case in cases.iter_mut() {
                    case.values.iter_mut().for_each(|test| self.visit(test, &mut rest));
                    let mut entered = if tested {
                        let mut entered = State::unreachable();
                        for test in &case.values {
                            entered = entered.join(&self.assume(&rest, test, true));
                        }
                        for test in &case.values {
                            rest = self.assume(&rest, test, false);
                        }
                        entered
                    } else {
                        rest.clone()
                    };
                    self.block(&mut case.body, &mut entered);
                    ends = ends.join(&entered);
                }
                match default {
                    Some(default) => {
                        let mut entered = rest;
                        self.block(&mut default.body, &mut entered);
                        ends = ends.join(&entered);
                    }
                    None => ends = ends.join(&rest),
                }
                let frame = self.frames.pop().expect("the switch's frame");
                ends = ends.join(&frame.breaks);
                if let Some(enclosing) = self.frames.last_mut() {
                    enclosing.continues = enclosing.continues.join(&frame.continues);
                }
                *state = ends;
            }
            GoStatement::IfAssert { name, value, then, .. } => {
                self.visit(value, state);
                let mut entered = state.clone();
                self.scopes.push(FxHashMap::default());
                self.bind(name, None, None, &mut entered);
                self.block(then, &mut entered);
                self.scopes.pop();
                *state = state.join(&entered);
            }
            GoStatement::Loop(body) => self.looping(state, None, body, Header::Forever),
            GoStatement::LabeledLoop { label, body } => {
                let label = label.clone();
                self.looping(state, Some(label), body, Header::Forever)
            }
            GoStatement::Counting { variable, start, end, body } => {
                self.visit(start, state);
                let typing =
                    [&*start, &*end].into_iter().find_map(|value| match self.typing(value) {
                        Some(Typing::Typed(kind)) => Some(kind),
                        _ => None,
                    });
                let kind = typing.or(Some(Kind::Int));
                let computed = self.computed(start, state);
                self.scopes.push(FxHashMap::default());
                let symbol = self.bind(variable, kind, None, state);
                self.settle(symbol, computed, state);
                let end = end.clone();
                self.looping(state, None, body, Header::Counting { variable: symbol, end: &end });
                self.scopes.pop();
                state.forget(symbol);
            }
            GoStatement::CountingDown { variable, start, body } => {
                self.visit(start, state);
                let kind = match self.typing(start) {
                    Some(Typing::Typed(kind)) => Some(kind),
                    _ => Some(Kind::Int),
                };
                let computed = self.computed(start, state);
                self.scopes.push(FxHashMap::default());
                let symbol = self.bind(variable, kind, None, state);
                self.settle(symbol, computed, state);
                self.looping(state, None, body, Header::CountingDown { variable: symbol });
                self.scopes.pop();
                state.forget(symbol);
            }
            GoStatement::Range { index, element, iterable, body } => {
                self.visit(iterable, state);
                let (kind, bound) = self.range_bound(iterable, state);
                let length = self.symbol();
                if let Some(bound) = bound {
                    state.assume_at_most(Value::of(length), bound, 0);
                    state.assume_at_most(bound, Value::of(length), 0);
                }
                self.scopes.push(FxHashMap::default());
                let index = index.as_ref().map(|index| self.bind(index, kind, None, state));
                self.bind(element, None, None, state);
                let header = Header::Range { index, length: bound.map(|_| length) };
                self.looping(state, None, body, header);
                self.scopes.pop();
                index.into_iter().for_each(|index| state.forget(index));
                state.forget(length);
            }
            GoStatement::Continue => {
                let state = std::mem::replace(state, State::unreachable());
                if let Some(frame) = self.frames.iter_mut().rev().find(|frame| !frame.switch) {
                    frame.continues = frame.continues.join(&state);
                }
            }
            GoStatement::Break => {
                let state = std::mem::replace(state, State::unreachable());
                if let Some(frame) = self.frames.last_mut() {
                    frame.breaks = frame.breaks.join(&state);
                }
            }
            GoStatement::BreakTo(label) => {
                let state = std::mem::replace(state, State::unreachable());
                if let Some(frame) =
                    self.frames.iter_mut().rev().find(|frame| frame.label.as_ref() == Some(label))
                {
                    frame.breaks = frame.breaks.join(&state);
                }
            }
            GoStatement::Line(_) => {}
        }
    }

    fn keeps(&self, statement: &mut GoStatement, state: &State) -> bool {
        if !self.lengths_through_pointers.iter().any(|length| state.mentions(*length)) {
            return true;
        }
        if let GoStatement::Assign { targets, values } = statement
            && let [GoExpression::Unary { operator: GoUnaryOperator::Dereference, .. }] =
                targets.as_slice()
        {
            // A store of the slice itself is interpreted by `assign`; its value may still call.
            let mut values: Vec<GoStatement> =
                values.iter().map(|value| GoStatement::Expression(value.clone())).collect();
            return self.keeping.keeps(&mut values);
        }
        self.keeping.keeps(std::slice::from_mut(statement))
    }

    fn keeps_expression(&self, value: &GoExpression, state: &State) -> bool {
        self.keeps(&mut GoStatement::Expression(value.clone()), state)
    }

    fn define(&mut self, names: &[String], values: &[GoExpression], state: &mut State) {
        let computed: Vec<Computed> = if names.len() == values.len() {
            values.iter().map(|value| self.computed(value, state)).collect()
        } else {
            names.iter().map(|_| Computed::default()).collect()
        };
        let kinds: Vec<Option<Kind>> = if names.len() == values.len() {
            values.iter().map(|value| self.kind_of_definition(value)).collect()
        } else {
            names.iter().map(|_| None).collect()
        };
        let condition = match (names, values) {
            ([name], [value]) if is_test(value) && !self.names.assigned.contains(name) => {
                Some(self.condition(value, state))
            }
            _ => None,
        };
        for (position, name) in names.iter().enumerate() {
            if name == "_" {
                continue;
            }
            let existing = self.scopes.last().and_then(|scope| scope.get(name).copied());
            let computed = computed[position];
            let symbol = match existing {
                Some(symbol) => {
                    let computed = self.hold(computed, state);
                    self.forget_binding(symbol, state);
                    self.settle(symbol, computed, state);
                    if let Some(condition) = &condition {
                        self.conditions.insert(symbol, condition.clone());
                    }
                    continue;
                }
                None => self.bind(name, kinds[position], None, state),
            };
            self.settle(symbol, computed, state);
            if let Some(condition) = &condition {
                self.conditions.insert(symbol, condition.clone());
            }
        }
    }

    fn assign(&mut self, targets: &[GoExpression], values: &[GoExpression], state: &mut State) {
        if targets.len() != values.len() {
            for target in targets {
                if let GoExpression::Identifier(name) = target
                    && let Some(symbol) = self.lookup(name)
                {
                    self.forget_binding(symbol, state);
                }
            }
            return;
        }
        let computed: Vec<Computed> = values
            .iter()
            .map(|value| {
                let computed = self.computed(value, state);
                self.hold(computed, state)
            })
            .collect();
        let mut stored = vec![];
        for (target, computed) in targets.iter().zip(computed) {
            match target {
                GoExpression::Identifier(name) => {
                    if let Some(symbol) = self.lookup(name) {
                        stored.push((symbol, computed));
                    }
                }
                GoExpression::Unary { operator: GoUnaryOperator::Dereference, operand } => {
                    let pointer = match &**operand {
                        GoExpression::Identifier(name) => self.lookup(name),
                        _ => None,
                    };
                    let length = pointer.and_then(|pointer| {
                        let binding = &self.bindings[&pointer];
                        binding.through_pointer.then_some(binding.length).flatten()
                    });
                    // The new slice's length goes through a temporary: forgetting every length
                    // behind a pointer forgets the old one, which it may be counted from.
                    let carried = match (length, computed.length) {
                        (Some(_), Some(value)) => {
                            let temporary = self.temporary(state, None);
                            state.assume_at_most(Value::of(temporary), value, 0);
                            state.assume_at_most(value, Value::of(temporary), 0);
                            Some(temporary)
                        }
                        _ => None,
                    };
                    self.forget_heap(state);
                    if let (Some(length), Some(temporary)) = (length, carried) {
                        state.add(length, temporary, 0);
                        state.add(temporary, length, 0);
                    }
                }
                _ => {}
            }
        }
        for (symbol, _) in &stored {
            self.forget_binding(*symbol, state);
        }
        for (symbol, computed) in stored {
            self.settle(symbol, computed, state);
        }
    }

    /// Forgets what is known of a binding's value before it is assigned.
    pub(super) fn forget_binding(&mut self, symbol: Symbol, state: &mut State) {
        // An untracked binding has no constraints, no length and no generation to change.
        if self.bindings.get(&symbol).is_some_and(|binding| !binding.tracked) {
            return;
        }
        state.forget(symbol);
        let generation = self.fresh_generation();
        state.generations.insert(symbol, generation);
        if let Some(length) = self.bindings.get(&symbol).and_then(|binding| binding.length) {
            self.forget_length(state, length);
            state.add(ZERO, length, 0);
        }
        if let Some(binding) = self.bindings.get(&symbol)
            && binding.tracked
            && let Some(kind) = binding.kind
        {
            self.kinds.insert(symbol, kind);
        }
    }

    /// Gives a binding the value computed for it.
    fn settle(&mut self, symbol: Symbol, computed: Computed, state: &mut State) {
        let Some(binding) = self.bindings.get(&symbol) else { return };
        if !binding.tracked {
            return;
        }
        let length = binding.length;
        if binding.kind.is_some()
            && let Some(value) = computed.value
        {
            state.assume_at_most(Value::of(symbol), value, 0);
            state.assume_at_most(value, Value::of(symbol), 0);
        }
        if let (Some(length), Some(value)) = (length, computed.length) {
            state.assume_at_most(Value::of(length), value, 0);
            state.assume_at_most(value, Value::of(length), 0);
        }
    }
}

fn is_bound_bounds_test(statement: &GoStatement) -> bool {
    matches!(statement, GoStatement::Define { names, values }
        if names.len() == 1 && values.len() == 1 && is_bounds_test(&values[0]))
}

fn is_leaf(statement: &GoStatement) -> bool {
    matches!(
        statement,
        GoStatement::Define { .. }
            | GoStatement::Variable { .. }
            | GoStatement::Assign { .. }
            | GoStatement::Expression(_)
            | GoStatement::Return(_)
    )
}
