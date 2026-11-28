use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GoBinaryOperator {
    LogicalOr,
    LogicalAnd,
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Add,
    Subtract,
    BitwiseOr,
    BitwiseXor,
    Multiply,
    Divide,
    Remainder,
    ShiftLeft,
    ShiftRight,
    BitwiseAnd,
}

impl GoBinaryOperator {
    pub fn symbol(self) -> &'static str {
        match self {
            GoBinaryOperator::LogicalOr => "||",
            GoBinaryOperator::LogicalAnd => "&&",
            GoBinaryOperator::Equal => "==",
            GoBinaryOperator::NotEqual => "!=",
            GoBinaryOperator::LessThan => "<",
            GoBinaryOperator::LessThanOrEqual => "<=",
            GoBinaryOperator::GreaterThan => ">",
            GoBinaryOperator::GreaterThanOrEqual => ">=",
            GoBinaryOperator::Add => "+",
            GoBinaryOperator::Subtract => "-",
            GoBinaryOperator::BitwiseOr => "|",
            GoBinaryOperator::BitwiseXor => "^",
            GoBinaryOperator::Multiply => "*",
            GoBinaryOperator::Divide => "/",
            GoBinaryOperator::Remainder => "%",
            GoBinaryOperator::ShiftLeft => "<<",
            GoBinaryOperator::ShiftRight => ">>",
            GoBinaryOperator::BitwiseAnd => "&",
        }
    }

    pub fn precedence(self) -> u8 {
        match self {
            GoBinaryOperator::LogicalOr => 1,
            GoBinaryOperator::LogicalAnd => 2,
            operator if operator.is_comparison() => 3,
            GoBinaryOperator::Add
            | GoBinaryOperator::Subtract
            | GoBinaryOperator::BitwiseOr
            | GoBinaryOperator::BitwiseXor => 4,
            _ => 5,
        }
    }

    pub fn is_comparison(self) -> bool {
        matches!(
            self,
            GoBinaryOperator::Equal
                | GoBinaryOperator::NotEqual
                | GoBinaryOperator::LessThan
                | GoBinaryOperator::LessThanOrEqual
                | GoBinaryOperator::GreaterThan
                | GoBinaryOperator::GreaterThanOrEqual
        )
    }

    pub fn is_logical(self) -> bool {
        matches!(self, GoBinaryOperator::LogicalAnd | GoBinaryOperator::LogicalOr)
    }

    pub fn is_equality(self) -> bool {
        matches!(self, GoBinaryOperator::Equal | GoBinaryOperator::NotEqual)
    }

    pub fn is_division(self) -> bool {
        matches!(self, GoBinaryOperator::Divide | GoBinaryOperator::Remainder)
    }

    pub fn may_panic(self) -> bool {
        matches!(
            self,
            GoBinaryOperator::Divide
                | GoBinaryOperator::Remainder
                | GoBinaryOperator::ShiftLeft
                | GoBinaryOperator::ShiftRight
        )
    }

    /// The operators Go has an assignment form of, `x += y` for `x = x + y`.
    pub fn has_assignment_form(self) -> bool {
        matches!(
            self,
            GoBinaryOperator::Add
                | GoBinaryOperator::Subtract
                | GoBinaryOperator::Multiply
                | GoBinaryOperator::Divide
                | GoBinaryOperator::Remainder
                | GoBinaryOperator::BitwiseAnd
                | GoBinaryOperator::BitwiseOr
                | GoBinaryOperator::BitwiseXor
                | GoBinaryOperator::ShiftLeft
                | GoBinaryOperator::ShiftRight
        )
    }

    pub fn negated_comparison(self) -> Option<GoBinaryOperator> {
        Some(match self {
            GoBinaryOperator::Equal => GoBinaryOperator::NotEqual,
            GoBinaryOperator::NotEqual => GoBinaryOperator::Equal,
            GoBinaryOperator::LessThan => GoBinaryOperator::GreaterThanOrEqual,
            GoBinaryOperator::LessThanOrEqual => GoBinaryOperator::GreaterThan,
            GoBinaryOperator::GreaterThan => GoBinaryOperator::LessThanOrEqual,
            GoBinaryOperator::GreaterThanOrEqual => GoBinaryOperator::LessThan,
            _ => return None,
        })
    }

    /// The comparison with its operands swapped.
    pub fn swapped_comparison(self) -> Option<GoBinaryOperator> {
        Some(match self {
            GoBinaryOperator::LessThan => GoBinaryOperator::GreaterThan,
            GoBinaryOperator::LessThanOrEqual => GoBinaryOperator::GreaterThanOrEqual,
            GoBinaryOperator::GreaterThan => GoBinaryOperator::LessThan,
            GoBinaryOperator::GreaterThanOrEqual => GoBinaryOperator::LessThanOrEqual,
            GoBinaryOperator::Equal => GoBinaryOperator::Equal,
            GoBinaryOperator::NotEqual => GoBinaryOperator::NotEqual,
            _ => return None,
        })
    }
}

impl fmt::Display for GoBinaryOperator {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.symbol())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GoUnaryOperator {
    Negate,
    Not,
    Complement,
    Dereference,
}

impl GoUnaryOperator {
    pub fn symbol(self) -> &'static str {
        match self {
            GoUnaryOperator::Negate => "-",
            GoUnaryOperator::Not => "!",
            GoUnaryOperator::Complement => "^",
            GoUnaryOperator::Dereference => "*",
        }
    }
}

impl fmt::Display for GoUnaryOperator {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.symbol())
    }
}
