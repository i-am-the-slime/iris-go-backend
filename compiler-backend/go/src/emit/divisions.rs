//! Euclidean `div` and `mod` where Go's own operators, or the runtime's cheaper helpers, compute
//! the same:
//!
//! - by a positive constant: a shift or a mask for a power of two, and otherwise
//!   `IntDivPositive` and `IntModPositive`;
//! - a remainder by a constant other than zero compared with zero: `x % c == 0`, as the Euclidean
//!   and the truncated remainder are zero together;
//! - a non-negative constant divided by a local that the enclosing branch shows is not zero:
//!   `/` and `%`, as truncation agrees with Euclidean division for a non-negative dividend.

use rustc_hash::FxHashSet;

use crate::go_traversal::{self, Walk};
use crate::syntax::{GoBinaryOperator, GoDeclaration, GoExpression, GoPackage, GoStatement};

pub(super) fn reduce_constant_divisions(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let changing = changing_names(declaration);
        let mut divisions = ConstantDivisions { changing, nonzero: vec![] };
        go_traversal::declaration(&mut divisions, declaration);
    }
}

struct ConstantDivisions {
    /// Names whose value a test cannot vouch for later: assigned, address taken, or declared
    /// more than once, so that one spelling may name two variables.
    changing: FxHashSet<String>,
    /// Locals the enclosing branches show are not zero.
    nonzero: Vec<String>,
}

impl Walk for ConstantDivisions {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::If { condition, then, otherwise } => {
                self.expression(condition);
                let (in_then, in_otherwise) = self.zero_test(condition);
                self.within(in_then, |divisions| divisions.block(then));
                self.within(in_otherwise, |divisions| divisions.block(otherwise));
            }
            GoStatement::Switch { value: Some(value), cases, default } => {
                self.expression(value);
                let tested = self.stable_local(value);
                let has_zero_case = cases.iter().any(|case| case.values.iter().any(is_zero));
                for case in cases.iter_mut() {
                    case.values.iter_mut().for_each(|value| self.expression(value));
                    let nonzero = case.values.iter().all(is_nonzero_integer);
                    let known = tested.clone().filter(|_| nonzero);
                    self.within(known, |divisions| divisions.block(&mut case.body));
                }
                if let Some(default) = default {
                    default.covers.iter_mut().for_each(|value| self.expression(value));
                    let known = tested.filter(|_| has_zero_case);
                    self.within(known, |divisions| divisions.block(&mut default.body));
                }
            }
            _ => go_traversal::statement(self, statement),
        }
    }

    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        if let Some(division) = Division::of(value) {
            *value = division.reduced(value);
        } else if let Some(division) = self.natural_division(value) {
            *value = division;
        } else if let Some(test) = remainder_test(value) {
            *value = test;
        }
    }
}

impl ConstantDivisions {
    fn within(&mut self, known: Option<String>, walk: impl FnOnce(&mut ConstantDivisions)) {
        let pushed = known.map(|name| self.nonzero.push(name)).is_some();
        walk(self);
        if pushed {
            self.nonzero.pop();
        }
    }

    /// The local a condition shows is not zero when it holds, and when it does not.
    fn zero_test(&self, condition: &GoExpression) -> (Option<String>, Option<String>) {
        let GoExpression::Binary { operator, left, right } = condition else { return (None, None) };
        let tested = match (&**left, &**right) {
            (local, zero) | (zero, local) if is_zero(zero) => self.stable_local(local),
            _ => None,
        };
        match *operator {
            GoBinaryOperator::Equal => (None, tested),
            GoBinaryOperator::NotEqual => (tested, None),
            _ => (None, None),
        }
    }

    fn stable_local(&self, value: &GoExpression) -> Option<String> {
        let GoExpression::Identifier(name) = value else { return None };
        (!self.changing.contains(name)).then(|| name.clone())
    }

    /// `prim.IntDiv(10, i)` where `i` is not zero is `10 / i`.
    fn natural_division(&self, value: &mut GoExpression) -> Option<GoExpression> {
        let GoExpression::Call { function, arguments } = value else { return None };
        let operator = match function.name_in(GoPackage::Prim) {
            Some("IntDiv") => GoBinaryOperator::Divide,
            Some("IntMod") => GoBinaryOperator::Remainder,
            _ => return None,
        };
        let [dividend, divisor] = arguments.as_slice() else { return None };
        let GoExpression::Integer(dividend) = dividend else { return None };
        let GoExpression::Identifier(divisor) = divisor else { return None };
        if *dividend < 0 || !self.nonzero.contains(divisor) {
            return None;
        }
        let mut arguments = std::mem::take(arguments).into_iter();
        let (left, right) = (arguments.next()?, arguments.next()?);
        Some(GoExpression::Binary { operator, left: Box::new(left), right: Box::new(right) })
    }
}

/// `prim.IntMod(x, c) == 0` is `x % c == 0` for a constant `c` other than zero.
fn remainder_test(value: &mut GoExpression) -> Option<GoExpression> {
    let GoExpression::Binary {
        operator: operator @ (GoBinaryOperator::Equal | GoBinaryOperator::NotEqual),
        left,
        right,
    } = value
    else {
        return None;
    };
    let operator = *operator;
    let remainder = match (&mut **left, &mut **right) {
        (remainder, zero) | (zero, remainder) if is_zero(zero) => remainder,
        _ => return None,
    };
    let GoExpression::Call { function, arguments } = remainder else { return None };
    let euclidean = matches!(function.name_in(GoPackage::Prim), Some("IntMod" | "IntModPositive"));
    if !euclidean || !matches!(arguments.as_slice(), [_, divisor] if is_nonzero_integer(divisor)) {
        return None;
    }
    let mut arguments = std::mem::take(arguments).into_iter();
    let (dividend, divisor) = (arguments.next()?, arguments.next()?);
    let truncated = GoExpression::Binary {
        operator: GoBinaryOperator::Remainder,
        left: Box::new(dividend),
        right: Box::new(divisor),
    };
    Some(GoExpression::Binary {
        operator,
        left: Box::new(truncated),
        right: Box::new(GoExpression::Integer(0)),
    })
}

fn is_zero(value: &GoExpression) -> bool {
    matches!(value, GoExpression::Integer(0))
}

fn is_nonzero_integer(value: &GoExpression) -> bool {
    matches!(value, GoExpression::Integer(value) if *value != 0)
}

/// The names in a declaration that [`ConstantDivisions::changing`] describes.
fn changing_names(declaration: &mut GoDeclaration) -> FxHashSet<String> {
    let mut census = Census::default();
    if let GoDeclaration::Function { parameters, .. } = declaration {
        for (name, _) in parameters.iter() {
            census.declare(name);
        }
    }
    go_traversal::declaration(&mut census, declaration);
    census.changing
}

#[derive(Default)]
struct Census {
    declared: FxHashSet<String>,
    changing: FxHashSet<String>,
}

impl Census {
    fn declare(&mut self, name: &str) {
        if !self.declared.insert(name.to_string()) {
            self.changing.insert(name.to_string());
        }
    }
}

impl Walk for Census {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, .. } => names.iter().for_each(|name| self.declare(name)),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                self.declare(name)
            }
            GoStatement::Assign { targets, .. } => {
                for target in targets.iter() {
                    if let GoExpression::Identifier(name) = target {
                        self.changing.insert(name.clone());
                    }
                }
            }
            GoStatement::Range { index, element, .. } => {
                index.iter().for_each(|name| self.declare(name));
                self.declare(element);
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.changing.insert(variable.clone());
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Address(target) => {
                if let GoExpression::Identifier(name) = &**target {
                    self.changing.insert(name.clone());
                }
            }
            GoExpression::Function { parameters, .. } => {
                parameters.iter().for_each(|(name, _)| self.declare(name));
            }
            _ => {}
        }
        go_traversal::expression(self, value);
    }
}

enum Operation {
    Quotient,
    Modulo,
}

struct Division {
    operation: Operation,
    divisor: i64,
}

impl Division {
    fn of(value: &GoExpression) -> Option<Division> {
        let GoExpression::Call { function, arguments } = value else { return None };
        if arguments.len() != 2 {
            return None;
        }
        let operation = match function.name_in(GoPackage::Prim)? {
            "IntDiv" => Operation::Quotient,
            "IntMod" => Operation::Modulo,
            _ => return None,
        };
        let [dividend, GoExpression::Integer(divisor)] = arguments.as_slice() else { return None };
        let typed = !matches!(dividend, GoExpression::Integer(_));
        let positive = (1..=i64::from(i32::MAX)).contains(divisor);
        (typed && positive).then_some(Division { operation, divisor: *divisor })
    }

    fn reduced(&self, value: &mut GoExpression) -> GoExpression {
        let GoExpression::Call { arguments, .. } = value else {
            unreachable!("a division is a call")
        };
        let dividend = std::mem::take(arguments).into_iter().next().expect("a dividend");
        if self.divisor.count_ones() == 1 {
            let (operator, right) = match self.operation {
                Operation::Quotient => {
                    (GoBinaryOperator::ShiftRight, i64::from(self.divisor.trailing_zeros()))
                }
                Operation::Modulo => (GoBinaryOperator::BitwiseAnd, self.divisor - 1),
            };
            return GoExpression::Binary {
                operator,
                left: Box::new(dividend),
                right: Box::new(GoExpression::Integer(right)),
            };
        }
        let name = match self.operation {
            Operation::Quotient => "IntDivPositive",
            Operation::Modulo => "IntModPositive",
        };
        let function = GoExpression::qualified(GoPackage::Prim, name);
        GoExpression::Call {
            function: Box::new(function),
            arguments: vec![dividend, GoExpression::Integer(self.divisor)],
        }
    }
}
