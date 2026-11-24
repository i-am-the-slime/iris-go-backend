//! Shorter Go for what emission spells out:
//!
//! - an integer chosen as the larger or smaller of two, `var r int32; if x < 0 { r = 0 } else
//!   { r = x }`, is Go's `r := max(x, 0)`; for floats the two disagree on -0;
//! - a length compared with a constant, `1 < int32(len(xs))`, is `len(xs) > 1`, and a length as
//!   a Number, `float64(int32(len(xs)))`, is `float64(len(xs))`, and back as Go's `int` it is
//!   `len(xs)`: an array holds at most as many
//!   elements as an Int counts (`array.Bounded`), and a string JavaScript can hold has fewer
//!   UTF-8 bytes than that, so the conversion never wraps;
//! - a Number variable given a constant, `var x float64 = 0.0`, is `x := 0.0`.

use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

pub(super) fn use_shorthands(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        go_traversal::declaration(&mut Shorthands, declaration);
    }
}

struct Shorthands;

impl Walk for Shorthands {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        body.iter_mut().for_each(|statement| self.statement(statement));
        let mut position = 0;
        while position + 1 < body.len() {
            if let Some(chosen) = extremum(&body[position], &body[position + 1]) {
                body.splice(position..position + 2, [chosen]);
            }
            position += 1;
        }
        for statement in body.iter_mut() {
            if let GoStatement::Variable { name, type_: GoType::Float64, value: Some(value) } =
                statement
                && is_float_constant(value)
            {
                let value = std::mem::replace(value, GoExpression::Integer(0));
                *statement =
                    GoStatement::Define { names: vec![std::mem::take(name)], values: vec![value] };
            }
        }
    }

    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        match value {
            GoExpression::Conversion { type_: GoType::Float64, value: converted } => {
                if let Some(length) = int32_length(converted) {
                    **converted = length;
                }
            }
            GoExpression::Conversion { type_: GoType::Int, value: converted } => {
                if let Some(length) = int32_length(converted) {
                    *value = length;
                }
            }
            GoExpression::Binary { operator, left, right } => {
                let Some(flipped) = flipped_comparison(operator) else { return };
                if let Some(length) = int32_length(right)
                    && matches!(**left, GoExpression::Integer(_))
                {
                    *operator = flipped;
                    std::mem::swap(left, right);
                    **left = length;
                } else if let Some(length) = int32_length(left)
                    && matches!(**right, GoExpression::Integer(_))
                {
                    **left = length;
                }
            }
            _ => {}
        }
    }
}

/// `var r T; if a < b { r = b } else { r = a }` as `r := max(a, b)`, and likewise `min`.
fn extremum(declared: &GoStatement, chosen: &GoStatement) -> Option<GoStatement> {
    let GoStatement::Variable { name, type_, value: None } = declared else { return None };
    if !is_integer(type_) {
        return None;
    }
    let GoStatement::If { condition, then, otherwise } = chosen else { return None };
    let GoExpression::Binary { operator, left, right } = condition else { return None };
    let less = match *operator {
        "<" | "<=" => true,
        ">" | ">=" => false,
        _ => return None,
    };
    let (then, otherwise) = (assigned(then, name)?, assigned(otherwise, name)?);
    let picks = |taken: &GoExpression, operand: &GoExpression| same_operand(taken, operand);
    let larger = if picks(then, right) && picks(otherwise, left) {
        less
    } else if picks(then, left) && picks(otherwise, right) {
        !less
    } else {
        return None;
    };
    let function = if larger { "max" } else { "min" };
    let call = GoExpression::Call {
        function: Box::new(GoExpression::Identifier(function.into())),
        arguments: vec![(**left).clone(), (**right).clone()],
    };
    // Two untyped constants would give the result an untyped constant's default type.
    if matches!(**left, GoExpression::Integer(_)) && matches!(**right, GoExpression::Integer(_)) {
        return None;
    }
    Some(GoStatement::Define { names: vec![name.clone()], values: vec![call] })
}

/// The value of a branch that only assigns `name`.
fn assigned<'b>(branch: &'b [GoStatement], name: &str) -> Option<&'b GoExpression> {
    let [GoStatement::Assign { targets, values }] = branch else { return None };
    let ([GoExpression::Identifier(target)], [value]) = (targets.as_slice(), values.as_slice())
    else {
        return None;
    };
    (target == name).then_some(value)
}

/// The same operand, read without calling anything.
fn same_operand(left: &GoExpression, right: &GoExpression) -> bool {
    match (left, right) {
        (GoExpression::Identifier(left), GoExpression::Identifier(right)) => left == right,
        (GoExpression::Integer(left), GoExpression::Integer(right)) => left == right,
        (
            GoExpression::Field { value: left, name: left_name },
            GoExpression::Field { value: right, name: right_name },
        ) => left_name == right_name && same_operand(left, right),
        (
            GoExpression::Binary { operator, left, right },
            GoExpression::Binary { operator: other, left: other_left, right: other_right },
        ) => {
            operator == other && same_operand(left, other_left) && same_operand(right, other_right)
        }
        _ => false,
    }
}

fn is_integer(type_: &GoType) -> bool {
    match type_ {
        GoType::Int => true,
        GoType::Named(name) => matches!(name.as_str(), "int32" | "int64" | "uint64"),
        _ => false,
    }
}

/// A constant that Go reads as a float without a type: it has a point or an exponent.
fn is_float_constant(value: &GoExpression) -> bool {
    matches!(value, GoExpression::Float(text) if text.contains(['.', 'e', 'E']))
}

/// `len(xs)` of `int32(len(xs))`.
fn int32_length(value: &GoExpression) -> Option<GoExpression> {
    let GoExpression::Conversion { type_: GoType::Named(type_), value } = value else {
        return None;
    };
    let GoExpression::Call { function, arguments } = &**value else { return None };
    let is_len = matches!(&**function, GoExpression::Identifier(name) if name == "len");
    (type_ == "int32" && is_len && arguments.len() == 1).then(|| (**value).clone())
}

/// The comparison with its operands swapped.
fn flipped_comparison(operator: &str) -> Option<&'static str> {
    Some(match operator {
        "<" => ">",
        "<=" => ">=",
        ">" => "<",
        ">=" => "<=",
        "==" => "==",
        "!=" => "!=",
        _ => return None,
    })
}
