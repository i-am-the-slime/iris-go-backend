use super::Analysis;
use crate::emit::intervals::constraints::{Kind, State, Symbol, Typing, Value, ZERO, kind_of_type};
use crate::syntax::{
    GoBinaryOperator, GoBuiltin, GoExpression, GoPackage, GoType, GoUnaryOperator,
};

impl Analysis<'_, '_, '_> {
    pub(super) fn typing(&self, value: &GoExpression) -> Option<Typing> {
        match value {
            GoExpression::Integer(_) => Some(Typing::Untyped),
            GoExpression::Attributed { value, .. } => self.typing(value),
            GoExpression::Field { name, .. } if self.program.fields.contains(name) => {
                Some(Typing::Typed(Kind::Int))
            }
            GoExpression::Identifier(name) => {
                let symbol = self.lookup(name)?;
                self.bindings.get(&symbol)?.kind.map(Typing::Typed)
            }
            GoExpression::Conversion { type_, .. } => kind_of_type(type_).map(Typing::Typed),
            GoExpression::Unary {
                operator: GoUnaryOperator::Negate | GoUnaryOperator::Complement,
                operand,
            } => self.typing(operand),
            GoExpression::Binary { operator, left, right }
                if matches!(
                    *operator,
                    GoBinaryOperator::Add
                        | GoBinaryOperator::Subtract
                        | GoBinaryOperator::Multiply
                        | GoBinaryOperator::Divide
                        | GoBinaryOperator::Remainder
                        | GoBinaryOperator::BitwiseAnd
                        | GoBinaryOperator::BitwiseOr
                        | GoBinaryOperator::BitwiseXor
                ) =>
            {
                match (self.typing(left)?, self.typing(right)?) {
                    (Typing::Typed(left), Typing::Typed(right)) if left == right => {
                        Some(Typing::Typed(left))
                    }
                    (Typing::Typed(kind), Typing::Untyped)
                    | (Typing::Untyped, Typing::Typed(kind)) => Some(Typing::Typed(kind)),
                    (Typing::Untyped, Typing::Untyped) => Some(Typing::Untyped),
                    _ => None,
                }
            }
            GoExpression::Call { function, arguments } => match &**function {
                _ if function.is_one_of(&[GoBuiltin::Len, GoBuiltin::Cap]) => {
                    Some(Typing::Typed(Kind::Int))
                }
                _ if function.is_one_of(&[GoBuiltin::Min, GoBuiltin::Max]) => {
                    self.typing_of_extremum(arguments)
                }
                GoExpression::Identifier(name) => {
                    let result = self.program.signatures.get(name)?.result.as_ref()?;
                    kind_of_type(result).map(Typing::Typed)
                }
                _ if matches!(
                    function.name_in(GoPackage::Prim),
                    Some("IntDiv" | "IntMod" | "ToCharCode")
                ) =>
                {
                    Some(Typing::Typed(Kind::Int))
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn typing_of_extremum(&self, arguments: &[GoExpression]) -> Option<Typing> {
        let mut typing = Typing::Untyped;
        for argument in arguments {
            let argument = self.typing(argument).unwrap_or(Typing::Typed(Kind::Int));
            typing = match (typing, argument) {
                (Typing::Untyped, other) | (other, Typing::Untyped) => other,
                (Typing::Typed(left), Typing::Typed(right)) if left == right => typing,
                _ => return None,
            };
        }
        Some(typing)
    }

    pub(super) fn kind_of_definition(&self, value: &GoExpression) -> Option<Kind> {
        match self.typing(value)? {
            Typing::Typed(kind) => Some(kind),
            Typing::Untyped => Some(Kind::Int),
        }
    }

    pub(super) fn computed(&mut self, value: &GoExpression, state: &mut State) -> Computed {
        Computed { value: self.value(value, state), length: self.length_of(value, state) }
    }

    /// The computed value, held by temporaries so that it survives an assignment of the
    /// symbols it was read from: `j = j - 1`.
    pub(super) fn hold(&mut self, computed: Computed, state: &mut State) -> Computed {
        Computed {
            value: computed.value.map(|value| self.held(value, state)),
            length: computed.length.map(|length| self.held(length, state)),
        }
    }

    fn held(&mut self, value: Value, state: &mut State) -> Value {
        if value.symbol == ZERO {
            return value;
        }
        let temporary = Value::of(self.temporary(state, None));
        state.assume_at_most(temporary, value, 0);
        state.assume_at_most(value, temporary, 0);
        temporary
    }

    pub(super) fn value(&mut self, value: &GoExpression, state: &mut State) -> Option<Value> {
        self.value_with(value, state, None)
    }

    /// The value of an Int expression as a symbol plus a constant, when it has one that does
    /// not wrap.
    pub(super) fn value_with(
        &mut self,
        value: &GoExpression,
        state: &mut State,
        blank: Option<Symbol>,
    ) -> Option<Value> {
        if state.unreachable {
            return None;
        }
        let kind = match self.typing(value) {
            Some(Typing::Typed(kind)) => Some(kind),
            _ => None,
        };
        match value {
            GoExpression::Integer(constant) => Some(Value::constant(*constant)),
            GoExpression::Attributed { value, .. } => self.value_with(value, state, blank),
            GoExpression::Field { name, .. } if self.program.fields.contains(name) => {
                let (low, high) = Kind::Int32.range();
                let temporary = self.temporary(state, Some(Kind::Int32));
                state.add(ZERO, temporary, -low);
                state.add(temporary, ZERO, high);
                Some(Value::of(temporary))
            }
            GoExpression::Identifier(name) if name.is_empty() => blank.map(Value::of),
            GoExpression::Identifier(name) => {
                let symbol = self.lookup(name)?;
                let binding = self.bindings.get(&symbol)?;
                (binding.tracked && binding.kind.is_some()).then_some(Value::of(symbol))
            }
            GoExpression::Conversion { type_: GoType::Int, value: inner }
                if let Some(shift) = zero_filling_shift(inner) =>
            {
                let temporary = self.temporary(state, kind);
                state.add(ZERO, temporary, 0);
                state.add(temporary, ZERO, (1i128 << (64 - shift)) - 1);
                Some(Value::of(temporary))
            }
            GoExpression::Conversion { type_, value: inner } => {
                let target = kind_of_type(type_)?;
                let inner_value = self.value_with(inner, state, blank);
                match (target, self.typing(inner)?) {
                    (_, Typing::Untyped) => inner_value,
                    (Kind::Int, Typing::Typed(_)) => inner_value,
                    (Kind::Int32, Typing::Typed(Kind::Int32)) => inner_value,
                    (Kind::Int32, Typing::Typed(Kind::Int)) => {
                        let (low, high) = Kind::Int32.range();
                        let fits = inner_value.is_some_and(|inner| {
                            self.lower(state, inner).is_some_and(|lower| lower >= low)
                                && self.upper(state, inner).is_some_and(|upper| upper <= high)
                        });
                        if fits { inner_value } else { None }
                    }
                }
            }
            GoExpression::Call { function, arguments } => match &**function {
                _ if function.is_builtin(GoBuiltin::Len) && arguments.len() == 1 => {
                    self.length(&arguments[0], state)
                }
                _ if function.is_one_of(&[GoBuiltin::Min, GoBuiltin::Max])
                    && !arguments.is_empty() =>
                {
                    self.extremum(
                        function.is_builtin(GoBuiltin::Min),
                        arguments,
                        kind?,
                        state,
                        blank,
                    )
                }
                _ if arguments.len() == 2 => match function.name_in(GoPackage::Prim) {
                    Some("IntMod") => {
                        self.remainder(&arguments[0], &arguments[1], state, blank, true)
                    }
                    Some("IntDiv") => self.quotient(&arguments[0], &arguments[1], state, blank),
                    _ => None,
                },
                _ => None,
            },
            GoExpression::Binary {
                operator: operator @ (GoBinaryOperator::Add | GoBinaryOperator::Subtract),
                left,
                right,
            } => {
                let kind = kind?;
                let left_value = self.value_with(left, state, blank);
                let right_value = self.value_with(right, state, blank);
                self.sum(*operator, left_value, right_value, kind, state)
            }
            GoExpression::Binary { operator: GoBinaryOperator::Remainder, left, right } => {
                self.remainder(left, right, state, blank, false)
            }
            GoExpression::Binary { operator: GoBinaryOperator::Divide, left, right } => {
                self.quotient(left, right, state, blank)
            }
            GoExpression::Binary { operator: GoBinaryOperator::BitwiseAnd, left, right } => {
                let mask = [left, right].into_iter().find_map(|side| match &**side {
                    GoExpression::Integer(mask) if *mask >= 0 => Some(*mask),
                    _ => None,
                })?;
                let temporary = self.temporary(state, kind);
                state.add(ZERO, temporary, 0);
                state.add(temporary, ZERO, mask as i128);
                Some(Value::of(temporary))
            }
            GoExpression::Binary { operator: GoBinaryOperator::Multiply, left, right } => {
                let kind = kind?;
                let left = self.value_with(left, state, blank)?;
                let right = self.value_with(right, state, blank)?;
                let bounds = [
                    (self.lower(state, left)?, self.lower(state, right)?),
                    (self.lower(state, left)?, self.upper(state, right)?),
                    (self.upper(state, left)?, self.lower(state, right)?),
                    (self.upper(state, left)?, self.upper(state, right)?),
                ];
                let products = bounds.iter().map(|(a, b)| a.checked_mul(*b));
                let products: Vec<i128> = products.collect::<Option<_>>()?;
                let (low, high) = (*products.iter().min()?, *products.iter().max()?);
                let (least, most) = kind.range();
                if low < least || high > most {
                    return None;
                }
                let temporary = self.temporary(state, Some(kind));
                state.add(ZERO, temporary, -low);
                state.add(temporary, ZERO, high);
                Some(Value::of(temporary))
            }
            _ => None,
        }
    }

    fn extremum(
        &mut self,
        least: bool,
        arguments: &[GoExpression],
        kind: Kind,
        state: &mut State,
        blank: Option<Symbol>,
    ) -> Option<Value> {
        let values = arguments.iter().map(|argument| self.value_with(argument, state, blank));
        let values: Vec<Option<Value>> = values.collect();
        let temporary = Value::of(self.temporary(state, Some(kind)));
        let mut bounds = vec![];
        for value in &values {
            let bound = match value {
                Some(value) if least => {
                    state.assume_at_most(temporary, *value, 0);
                    self.lower(state, *value)
                }
                Some(value) => {
                    state.assume_at_most(*value, temporary, 0);
                    self.upper(state, *value)
                }
                None => None,
            };
            bounds.push(bound);
        }
        let bounds: Option<Vec<i128>> = bounds.into_iter().collect();
        if let Some(bounds) = bounds {
            match least {
                true => state.add(ZERO, temporary.symbol, -bounds.into_iter().min()?),
                false => state.add(temporary.symbol, ZERO, bounds.into_iter().max()?),
            }
        }
        Some(temporary)
    }

    /// `left ± right` of the kind, when it cannot wrap.
    fn sum(
        &mut self,
        operator: GoBinaryOperator,
        left: Option<Value>,
        right: Option<Value>,
        kind: Kind,
        state: &mut State,
    ) -> Option<Value> {
        let (left, right) = (left?, right?);
        let sign: i128 = if operator == GoBinaryOperator::Add { 1 } else { -1 };
        let (least, most) = kind.range();
        if right.symbol == ZERO || (left.symbol == ZERO && sign == 1) {
            let (base, constant) = if right.symbol == ZERO {
                (left, sign * right.offset as i128)
            } else {
                (right, left.offset as i128)
            };
            let fits = if constant >= 0 {
                base.symbol == ZERO && base.offset as i128 + constant <= most
                    || self.upper(state, base).is_some_and(|upper| upper + constant <= most)
            } else {
                base.symbol == ZERO && base.offset as i128 + constant >= least
                    || self.lower(state, base).is_some_and(|lower| lower + constant >= least)
            };
            return if fits { base.shifted(constant) } else { None };
        }
        // Two symbols: each bounds the other's distance from the result.
        let (left_low, left_high) = (self.lower(state, left)?, self.upper(state, left)?);
        let (right_low, right_high) = (self.lower(state, right)?, self.upper(state, right)?);
        let (low, high) = if sign == 1 {
            (left_low + right_low, left_high + right_high)
        } else {
            (left_low - right_high, left_high - right_low)
        };
        if low < least || high > most {
            return None;
        }
        let temporary = Value::of(self.temporary(state, Some(kind)));
        state.add(ZERO, temporary.symbol, -low);
        state.add(temporary.symbol, ZERO, high);
        if sign == 1 {
            state.assume_at_most(temporary, left, right_high);
            state.assume_at_most(left, temporary, -right_low);
            state.assume_at_most(temporary, right, left_high);
            state.assume_at_most(right, temporary, -left_low);
        } else {
            state.assume_at_most(temporary, left, -right_low);
            state.assume_at_most(left, temporary, right_high);
        }
        Some(temporary)
    }

    /// Euclidean `mod` (`euclidean`) or Go's `%`, by a divisor proven positive.
    fn remainder(
        &mut self,
        dividend: &GoExpression,
        divisor: &GoExpression,
        state: &mut State,
        blank: Option<Symbol>,
        euclidean: bool,
    ) -> Option<Value> {
        let divisor = self.value_with(divisor, state, blank)?;
        if self.lower(state, divisor).is_none_or(|lower| lower < 1) {
            return None;
        }
        let dividend = self.value_with(dividend, state, blank);
        let natural = dividend
            .is_some_and(|dividend| self.lower(state, dividend).is_some_and(|lower| lower >= 0));
        if !euclidean && !natural {
            return None;
        }
        let temporary = Value::of(self.temporary(state, Some(Kind::Int)));
        state.add(ZERO, temporary.symbol, 0);
        state.assume_at_most(temporary, divisor, -1);
        if natural && let Some(dividend) = dividend {
            state.assume_at_most(temporary, dividend, 0);
        }
        Some(temporary)
    }

    /// A non-negative dividend over a positive divisor.
    fn quotient(
        &mut self,
        dividend: &GoExpression,
        divisor: &GoExpression,
        state: &mut State,
        blank: Option<Symbol>,
    ) -> Option<Value> {
        let divisor = self.value_with(divisor, state, blank)?;
        let dividend = self.value_with(dividend, state, blank)?;
        if self.lower(state, divisor).is_none_or(|lower| lower < 1)
            || self.lower(state, dividend).is_none_or(|lower| lower < 0)
        {
            return None;
        }
        let temporary = Value::of(self.temporary(state, Some(Kind::Int)));
        state.add(ZERO, temporary.symbol, 0);
        state.assume_at_most(temporary, dividend, 0);
        Some(temporary)
    }

    /// The symbol of `len(array)`, for an array whose length is known to stay.
    pub(super) fn length(&mut self, array: &GoExpression, _state: &mut State) -> Option<Value> {
        let (name, through_pointer) = match array {
            GoExpression::Identifier(name) => (name, false),
            GoExpression::Unary { operator: GoUnaryOperator::Dereference, operand } => {
                match &**operand {
                    GoExpression::Identifier(name) => (name, true),
                    _ => return None,
                }
            }
            GoExpression::String(text) => return Some(Value::constant(text.len() as i64)),
            _ => return None,
        };
        let binding = self.bindings.get(&self.lookup(name)?)?;
        (binding.through_pointer == through_pointer).then_some(Value::of(binding.length?))
    }

    /// The length of a slice-valued expression.
    fn length_of(&mut self, value: &GoExpression, state: &mut State) -> Option<Value> {
        match value {
            GoExpression::Identifier(_)
            | GoExpression::Unary { operator: GoUnaryOperator::Dereference, .. } => {
                self.length(value, state)
            }
            GoExpression::Address(inner) => self.length_of(inner, state),
            GoExpression::Composite { type_: GoType::Slice(_), fields } => fields
                .iter()
                .all(|(key, _)| key.is_none())
                .then_some(Value::constant(fields.len() as i64)),
            GoExpression::Call { function, arguments } => match &**function {
                _ if function.is_qualified(GoPackage::Array, "Bounded") && arguments.len() == 1 => {
                    self.length_of(&arguments[0], state)
                }
                // `append` panics rather than wrap a length.
                _ if function.is_builtin(GoBuiltin::Append) && !arguments.is_empty() => {
                    if arguments.iter().any(|argument| matches!(argument, GoExpression::Spread(_)))
                    {
                        return None;
                    }
                    self.length_of(&arguments[0], state)?.shifted(arguments.len() as i128 - 1)
                }
                _ if function.is_builtin(GoBuiltin::Make) && arguments.len() >= 2 => {
                    matches!(arguments[0], GoExpression::Type(GoType::Slice(_)))
                        .then(|| self.value(&arguments[1], state))
                        .flatten()
                }
                _ => None,
            },
            _ => None,
        }
    }
}

/// What is known of an expression's value: as an integer, and as a slice's length.
#[derive(Clone, Copy, Default)]
pub(super) struct Computed {
    pub(super) value: Option<Value>,
    pub(super) length: Option<Value>,
}

fn zero_filling_shift(value: &GoExpression) -> Option<i64> {
    let GoExpression::Binary { operator: GoBinaryOperator::ShiftRight, left, right } = value else {
        return None;
    };
    let GoExpression::Conversion { type_: GoType::Named(source), .. } = left.as_ref() else {
        return None;
    };
    let GoExpression::Integer(shift) = right.as_ref() else { return None };
    (source == "uint" && (1..64).contains(shift)).then_some(*shift)
}
