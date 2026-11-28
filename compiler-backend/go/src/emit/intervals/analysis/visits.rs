use rustc_hash::FxHashMap;

use super::Analysis;
use crate::emit::intervals::constraints::{Kind, State, Typing, Value, kind_of_type};
use crate::emit::intervals::names::{Shape, shape_of_type};
use crate::emit::intervals::program::{Entry, Place};
use crate::emit::intervals::{site_of, written_field};
use crate::syntax::GoExpression;

impl Analysis<'_, '_, '_> {
    pub(super) fn visit(&mut self, value: &mut GoExpression, state: &mut State) {
        if state.unreachable {
            return;
        }
        match value {
            GoExpression::Function { parameters, body, .. } => {
                let frames = std::mem::take(&mut self.frames);
                let temporaries = std::mem::take(&mut self.temporaries);
                let mut inner = State::default();
                self.scopes.push(FxHashMap::default());
                for (name, type_) in parameters.iter() {
                    self.bind(name, kind_of_type(type_), shape_of_type(type_), &mut inner);
                }
                self.block(body, &mut inner);
                self.scopes.pop();
                self.frames = frames;
                self.temporaries = temporaries;
                return;
            }
            _ => walk_children(value, |child| self.visit(child, state)),
        }
        if let GoExpression::Composite { fields, .. } = value {
            for (label, field) in fields.iter() {
                if label.as_ref().is_some_and(|label| self.program.fields.contains(label)) {
                    let fits = self.fits_in_int32(field, state);
                    self.observe(site_of(field), fits);
                }
            }
        }
        if let GoExpression::Call { function, arguments } = value {
            if let GoExpression::Identifier(callee) = &**function {
                let callee = callee.clone();
                self.call(&callee, arguments, state);
            }
            if self.rewriting()
                && let GoExpression::Qualified { package, name } = &**function
                && package == "prim"
                && matches!(name.as_str(), "IntMod" | "IntDiv")
                && arguments.len() == 2
                && self.natural_division(&arguments[0], &arguments[1], state)
            {
                let operator = if name == "IntMod" { "%" } else { "/" };
                let mut arguments = std::mem::take(arguments);
                let right = arguments.pop().expect("a divisor");
                let left = arguments.pop().expect("a dividend");
                *value =
                    GoExpression::Binary { operator, left: Box::new(left), right: Box::new(right) };
            }
        }
    }

    pub(super) fn visit_target(&mut self, target: &mut GoExpression, state: &mut State) {
        match target {
            GoExpression::Identifier(_) => {}
            GoExpression::Unary { operator: "*", operand } => self.visit_target(operand, state),
            _ => self.visit(target, state),
        }
    }

    /// Whether Go's truncating division agrees with Euclidean division here: a dividend proven
    /// non-negative, a divisor proven positive, and a typed one among them for the result's type.
    fn natural_division(
        &mut self,
        dividend: &GoExpression,
        divisor: &GoExpression,
        state: &State,
    ) -> bool {
        let typed = [dividend, divisor]
            .iter()
            .any(|side| matches!(self.typing(side), Some(Typing::Typed(_))));
        let from = self.temporaries.len();
        let mut scratch = state.clone();
        let dividend = self.value(dividend, &mut scratch);
        let divisor = self.value(divisor, &mut scratch);
        let natural = dividend
            .is_some_and(|value| self.lower(&scratch, value).is_some_and(|lower| lower >= 0))
            && divisor
                .is_some_and(|value| self.lower(&scratch, value).is_some_and(|lower| lower >= 1));
        self.forget_temporaries(&mut scratch, from);
        typed && natural
    }

    pub(super) fn observe_stores(
        &mut self,
        targets: &[GoExpression],
        values: &[GoExpression],
        state: &State,
    ) {
        for (position, target) in targets.iter().enumerate() {
            if written_field(target, &self.program.fields).is_none() {
                continue;
            }
            let fits =
                targets.len() == values.len() && self.fits_in_int32(&values[position], state);
            self.observe(site_of(target), fits);
        }
    }

    fn fits_in_int32(&mut self, value: &GoExpression, state: &State) -> bool {
        if self.observations.is_none() || self.quiet > 0 || state.unreachable {
            return false;
        }
        let from = self.temporaries.len();
        let mut scratch = state.clone();
        let (low, high) = Kind::Int32.range();
        let fits = self.value(value, &mut scratch).is_some_and(|value| {
            self.lower(&scratch, value).is_some_and(|lower| lower >= low)
                && self.upper(&scratch, value).is_some_and(|upper| upper <= high)
        });
        self.forget_temporaries(&mut scratch, from);
        fits
    }

    fn observe(&mut self, site: usize, fits: bool) {
        if self.quiet > 0 {
            return;
        }
        if let Some(observations) = &mut self.observations {
            let proven = observations.entry(site).or_insert(true);
            *proven &= fits;
        }
    }

    /// Records what a call of an internal function gives its parameters.
    fn call(&mut self, callee: &str, arguments: &[GoExpression], state: &State) {
        if self.quiet > 0 || state.unreachable || !self.program.internal.contains(callee) {
            return;
        }
        let Some(signature) = self.program.signatures.get(callee) else { return };
        if signature.parameters.len() != arguments.len() {
            return;
        }
        let parameters = signature.parameters.clone();
        let from = self.temporaries.len();
        let mut scratch = state.clone();
        let mut places: Vec<(Place, Value)> = vec![(Place::Zero, Value::constant(0))];
        for (position, (argument, type_)) in arguments.iter().zip(&parameters).enumerate() {
            if kind_of_type(type_).is_some()
                && let Some(value) = self.value(argument, &mut scratch)
            {
                places.push((Place::Parameter(position), value));
            }
            let length = match shape_of_type(type_) {
                Some(Shape::Fixed) => self.length(argument, &mut scratch),
                Some(Shape::Pointer) => match argument {
                    GoExpression::Identifier(_) => {
                        let dereferenced = GoExpression::Unary {
                            operator: "*",
                            operand: Box::new(argument.clone()),
                        };
                        self.length(&dereferenced, &mut scratch)
                    }
                    _ => None,
                },
                None => None,
            };
            if let Some(length) = length {
                places.push((Place::Length(position), length));
            }
        }
        let mut facts = FxHashMap::default();
        // Bounds that come from the arguments' types, which the constraints leave implicit.
        for (place, value) in &places {
            if *place == Place::Zero {
                continue;
            }
            if let Some(upper) = self.upper(&scratch, *value)
                && upper <= i64::MAX as i128
            {
                facts.insert((*place, Place::Zero), upper as i64);
            }
            if let Some(lower) = self.lower(&scratch, *value)
                && -lower <= i64::MAX as i128
            {
                facts.insert((Place::Zero, *place), (-lower) as i64);
            }
        }
        for (a, left) in &places {
            for (b, right) in &places {
                if a == b {
                    continue;
                }
                if let Some(distance) = scratch.get(left.symbol, right.symbol) {
                    let bound = distance as i128 + left.offset as i128 - right.offset as i128;
                    if bound >= i64::MIN as i128 && bound <= i64::MAX as i128 {
                        let entry = facts.entry((*a, *b)).or_insert(i64::MAX);
                        *entry = (*entry).min(bound as i64);
                    }
                }
            }
        }
        self.forget_temporaries(&mut scratch, from);
        let facts = Entry(facts);
        let merged = match self.calls.get(callee) {
            Some(old) => old.join(&facts),
            None => facts,
        };
        self.calls.insert(callee.to_string(), merged);
    }
}

/// Calls `visit` on the expression's direct children, outside function literals.
fn walk_children(value: &mut GoExpression, mut visit: impl FnMut(&mut GoExpression)) {
    match value {
        GoExpression::Function { .. } => {}
        GoExpression::Call { function, arguments } => {
            visit(function);
            arguments.iter_mut().for_each(visit);
        }
        GoExpression::Binary { left, right, .. } => {
            visit(left);
            visit(right);
        }
        GoExpression::Index { value, index } => {
            visit(value);
            visit(index);
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. }
        | GoExpression::TypeAssertion { value, .. }
        | GoExpression::Spread(value)
        | GoExpression::Instantiation { function: value, .. }
        | GoExpression::Attributed { value, .. } => visit(value),
        GoExpression::Composite { fields, .. } => {
            fields.iter_mut().for_each(|(_, field)| visit(field))
        }
        GoExpression::Results(values) => values.iter_mut().for_each(visit),
        _ => {}
    }
}
