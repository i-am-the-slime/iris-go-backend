use super::{Analysis, Frame};
use crate::emit::intervals::constraints::{Kind, State, Symbol, Typing, Value, ZERO};
use crate::syntax::{GoBinaryOperator, GoExpression, GoStatement};

impl Analysis<'_, '_, '_> {
    pub(super) fn looping(
        &mut self,
        state: &mut State,
        label: Option<String>,
        body: &mut Vec<GoStatement>,
        header: Header<'_>,
    ) {
        let watermark = self.next;
        let mut head = state.clone();
        self.quiet += 1;
        let mut rounds = 0;
        loop {
            let (back, _) = self.iteration(&head, label.clone(), body, &header, watermark);
            let joined = head.join(&back);
            let next = if rounds >= 2 { head.widen(&joined) } else { joined };
            if next == head {
                break;
            }
            head = next;
            rounds += 1;
            if rounds > 12 {
                head = State { generations: head.generations, ..State::default() };
                head.generations.values_mut().for_each(|generation| *generation = 0);
                head.heap = 0;
            }
        }
        self.quiet -= 1;
        let (_, exit) = self.iteration(&head, label, body, &header, watermark);
        *state = exit;
    }

    /// One pass through the loop from `head`: the state it returns to the head with, and the
    /// state it leaves with.
    fn iteration(
        &mut self,
        head: &State,
        label: Option<String>,
        body: &mut Vec<GoStatement>,
        header: &Header<'_>,
        watermark: Symbol,
    ) -> (State, State) {
        let (mut entered, mut exit) = match header {
            Header::Forever => (head.clone(), State::unreachable()),
            Header::Counting { variable, end } => {
                let mut end = (*end).clone();
                let mut visited = head.clone();
                self.visit(&mut end, &mut visited);
                let test = GoExpression::Binary {
                    operator: GoBinaryOperator::LessThan,
                    left: Box::new(GoExpression::Identifier(String::new())),
                    right: Box::new(end),
                };
                (
                    self.assume_with(head, &test, true, Some(*variable)),
                    self.assume_with(head, &test, false, Some(*variable)),
                )
            }
            Header::CountingDown { variable } => {
                let mut entered = head.clone();
                entered.add(ZERO, *variable, 0);
                let mut exit = head.clone();
                exit.add(*variable, ZERO, -1);
                (entered, exit)
            }
            Header::Range { index, length } => {
                let mut entered = head.clone();
                if let Some(index) = index {
                    entered.forget(*index);
                    entered.add(ZERO, *index, 0);
                    if let Some(length) = length {
                        entered.add(*index, *length, -1);
                    }
                }
                (entered, head.clone())
            }
        };
        self.frames.push(Frame {
            label,
            switch: false,
            breaks: State::unreachable(),
            continues: State::unreachable(),
        });
        self.block(body, &mut entered);
        let frame = self.frames.pop().expect("the loop's frame");
        let mut back = entered.join(&frame.continues);
        self.restrict(&mut back, watermark);
        match header {
            Header::Counting { variable, .. } => self.step(&mut back, *variable, 1),
            Header::CountingDown { variable } => self.step(&mut back, *variable, -1),
            Header::Range { index: Some(index), .. } => back.forget(*index),
            _ => {}
        }
        exit = exit.join(&frame.breaks);
        self.restrict(&mut exit, watermark);
        (back, exit)
    }

    /// `variable += by`, unless the variable may wrap.
    fn step(&mut self, state: &mut State, variable: Symbol, by: i128) {
        if state.unreachable {
            return;
        }
        let kind = self.bindings[&variable].kind.unwrap_or(Kind::Int32);
        let current = Value::of(variable);
        let fits = match by.signum() {
            1 => self.upper(state, current).is_some_and(|upper| upper + by <= kind.range().1),
            _ => self.lower(state, current).is_some_and(|lower| lower + by >= kind.range().0),
        };
        let from = self.temporaries.len();
        let stepped = if fits {
            let temporary = self.temporary(state, Some(kind));
            let value = Value::of(temporary);
            state.assume_at_most(value, current, by);
            state.assume_at_most(current, value, -by);
            Some(value)
        } else {
            None
        };
        self.forget_binding(variable, state);
        if let Some(value) = stepped {
            state.assume_at_most(Value::of(variable), value, 0);
            state.assume_at_most(value, Value::of(variable), 0);
        }
        self.forget_temporaries(state, from);
    }

    /// The kind of a range loop's index and the number of its iterations.
    pub(super) fn range_bound(
        &mut self,
        iterable: &GoExpression,
        state: &mut State,
    ) -> (Option<Kind>, Option<Value>) {
        if let Some(length) = self.length(iterable, state) {
            return (Some(Kind::Int), Some(length));
        }
        match self.typing(iterable) {
            Some(Typing::Typed(kind)) => (Some(kind), self.value(iterable, state)),
            _ => (None, None),
        }
    }
}

pub(super) enum Header<'a> {
    Forever,
    Counting { variable: Symbol, end: &'a GoExpression },
    CountingDown { variable: Symbol },
    Range { index: Option<Symbol>, length: Option<Symbol> },
}
