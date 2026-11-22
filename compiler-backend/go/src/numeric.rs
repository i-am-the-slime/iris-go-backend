use crate::foreign::Operator;

pub(crate) fn fold_bitwise(operator: Operator, x: i32, y: i32) -> i64 {
    let count = (y & 31) as u32;
    i64::from(match operator {
        Operator::IntAnd => x & y,
        Operator::IntOr => x | y,
        Operator::IntXor => x ^ y,
        Operator::IntShiftLeft => x.wrapping_shl(count),
        Operator::IntShiftRight => x >> count,
        _ => ((x as u32) >> count) as i32,
    })
}
