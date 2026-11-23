use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression};

pub(super) fn reduce_constant_divisions(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        go_traversal::declaration(&mut ConstantDivisions, declaration);
    }
}

struct ConstantDivisions;

impl Walk for ConstantDivisions {
    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        if let Some(division) = Division::of(value) {
            *value = division.reduced(value);
        }
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
        let GoExpression::Qualified { package, name } = &**function else { return None };
        if package != "prim" || arguments.len() != 2 {
            return None;
        }
        let operation = match name.as_str() {
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
                Operation::Quotient => (">>", i64::from(self.divisor.trailing_zeros())),
                Operation::Modulo => ("&", self.divisor - 1),
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
        let function = GoExpression::Qualified { package: "prim".into(), name: name.into() };
        GoExpression::Call {
            function: Box::new(function),
            arguments: vec![dividend, GoExpression::Integer(self.divisor)],
        }
    }
}
