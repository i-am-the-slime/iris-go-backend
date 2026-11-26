use crate::foreign::Operator;

/// A Data.Int.Bits operator on Int constants, at Go's `int` width on the 64-bit targets: shift
/// counts are taken modulo 64, as the generated Go masks them, and `zshr` shifts the unsigned
/// bits.
pub(crate) fn fold_bitwise(operator: Operator, x: i64, y: i64) -> i64 {
    let count = (y & 63) as u32;
    match operator {
        Operator::IntAnd => x & y,
        Operator::IntOr => x | y,
        Operator::IntXor => x ^ y,
        Operator::IntShiftLeft => x.wrapping_shl(count),
        Operator::IntShiftRight => x >> count,
        _ => ((x as u64) >> count) as i64,
    }
}
