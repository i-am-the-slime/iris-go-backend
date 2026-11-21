#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Primitive {
    MakeExists,
    RunExists,
    Inject,
    On,
    Default,
    Case,
    Expand,
    Match,
    OnMatch,
    ReifyType,
    /// `Data.Int64.Internal.signedToUnsigned` and `unsignedToSigned`, whose
    /// bodies would need a Long of each signedness at once: Go's conversion
    /// between `int64` and `uint64`, which keeps the bits as long.js does.
    ToUnsigned,
    ToSigned,
}

pub fn known(module: &str, name: &str) -> Option<Primitive> {
    match (module, name) {
        ("Data.Exists", "mkExists") => Some(Primitive::MakeExists),
        ("Data.Exists", "runExists") => Some(Primitive::RunExists),
        ("Data.Variant", "inj") => Some(Primitive::Inject),
        ("Data.Variant", "on") => Some(Primitive::On),
        ("Data.Variant", "default") => Some(Primitive::Default),
        ("Data.Variant", "case_") => Some(Primitive::Case),
        ("Data.Variant", "expand") => Some(Primitive::Expand),
        ("Data.Variant", "match") => Some(Primitive::Match),
        ("Data.Variant", "onMatch") => Some(Primitive::OnMatch),
        ("Data.Reflectable", "reifyType") => Some(Primitive::ReifyType),
        ("Data.Int64.Internal", "signedToUnsigned") => Some(Primitive::ToUnsigned),
        ("Data.Int64.Internal", "unsignedToSigned") => Some(Primitive::ToSigned),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KnownType {
    Maybe,
    Variant,
    /// Control.Monad.Free's `Val`, the constructorless type that stands for the
    /// result of every step a `Free` hides behind `unsafeCoerce`.
    FreeValue,
    /// purescript-int64's foreign `Long`, a long.js value that carries its
    /// signedness. Its Go type is the signedness of the definition it is used
    /// in: an `int64` where that is `Signed`, a `uint64` where `Unsigned`.
    Long,
    /// `Long' s`, the newtype `Int64` (`Long' Signed`) and `UInt64`
    /// (`Long' Unsigned`) wrap, whose phantom fixes the Long's signedness.
    SignedLong,
    Signed,
    Unsigned,
}

pub fn known_type(module: &str, name: &str) -> Option<KnownType> {
    match (module, name) {
        ("Data.Maybe", "Maybe") => Some(KnownType::Maybe),
        ("Data.Variant", "Variant") => Some(KnownType::Variant),
        ("Control.Monad.Free", "Val") => Some(KnownType::FreeValue),
        ("Data.Int64.Internal", "Long") => Some(KnownType::Long),
        ("Data.Int64.Internal", "Long'") => Some(KnownType::SignedLong),
        ("Data.Int64.Internal", "Signed") => Some(KnownType::Signed),
        ("Data.Int64.Internal", "Unsigned") => Some(KnownType::Unsigned),
        _ => None,
    }
}

/// Whether a Long is read as signed or unsigned, which purescript-int64 keeps
/// in the type `Long' s` and long.js in the value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Signedness {
    Signed,
    Unsigned,
}

impl Signedness {
    pub fn go_type(self) -> &'static str {
        match self {
            Signedness::Signed => "int64",
            Signedness::Unsigned => "uint64",
        }
    }
}

/// What a `Data.Int64.Internal` foreign over `Long` is at one signedness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Int64Foreign {
    /// Go's own operators and conversions on `int64` and `uint64`.
    Inline(Int64Operation),
    /// A function of iris-go's `Data_Int64_Internal_ffi`: one generic in the
    /// Long's Go type, or one per signedness where only the result has it.
    Runtime {
        signed: &'static str,
        unsigned: &'static str,
        arity: usize,
        effectful: bool,
        /// The arguments the function declares as Go's `int32`.
        ints: &'static [usize],
        /// The function is a three-way comparison of its two Longs in the
        /// order of Go's operators on their type, as `Boundary::three_way` says.
        three_way: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Int64Operation {
    /// The Long with these bits.
    Constant(i64),
    /// `fromInt_ i flag`: the Int, sign-extended as long.js's `fromInt` does
    /// also for an unsigned Long.
    FromInt,
    /// `unsigned_ l`, which the Go type of `l` answers.
    IsUnsigned,
    Add,
    Subtract,
    Multiply,
    Negate,
    And,
    Or,
    Xor,
    Not,
    /// Shifts use the low six bits of the amount, as long.js does.
    ShiftLeft,
    /// Arithmetic, also for an unsigned Long, as in long.js.
    ShiftRight,
    ShiftRightUnsigned,
    Compare(crate::foreign::Comparison),
    IsZero,
    IsEven,
    IsOdd,
    IsNegative,
    /// Zero included, as long.js's `isPositive`.
    IsPositive,
    /// The low 32 bits.
    ToInt,
    ToNumber,
    /// The high or low 32 bits as a Number, read as signed or unsigned.
    HighBits { unsigned: bool },
    LowBits { unsigned: bool },
    /// `toSigned_` and `toUnsigned_`, whose Long has the definition's one Go
    /// type on both sides.
    Same,
    /// The bits of a Long of the other signedness.
    Convert,
}

impl Int64Operation {
    pub fn arity(self) -> usize {
        match self {
            Int64Operation::Constant(_) => 0,
            Int64Operation::FromInt
            | Int64Operation::Add
            | Int64Operation::Subtract
            | Int64Operation::Multiply
            | Int64Operation::And
            | Int64Operation::Or
            | Int64Operation::Xor
            | Int64Operation::ShiftLeft
            | Int64Operation::ShiftRight
            | Int64Operation::ShiftRightUnsigned
            | Int64Operation::Compare(_) => 2,
            Int64Operation::IsUnsigned
            | Int64Operation::Negate
            | Int64Operation::Not
            | Int64Operation::IsZero
            | Int64Operation::IsEven
            | Int64Operation::IsOdd
            | Int64Operation::IsNegative
            | Int64Operation::IsPositive
            | Int64Operation::ToInt
            | Int64Operation::ToNumber
            | Int64Operation::HighBits { .. }
            | Int64Operation::LowBits { .. }
            | Int64Operation::Same
            | Int64Operation::Convert => 1,
        }
    }
}

/// purescript-int64 3.0.0's `Data.Int64.Internal` foreigns over `Long`. The
/// ones it does not list (`isLong_`, `numberBitsToInt`, `isWholeNumber_`)
/// take no Long and come from iris-go's package like any library foreign.
pub fn int64_foreign(module: &str, name: &str) -> Option<Int64Foreign> {
    use crate::foreign::Comparison;
    use Int64Operation as Operation;
    if module != "Data.Int64.Internal" {
        return None;
    }
    let inline = |operation| Some(Int64Foreign::Inline(operation));
    let generic = |name: &'static str, arity, ints| {
        Some(Int64Foreign::Runtime {
            signed: name,
            unsigned: name,
            arity,
            effectful: false,
            ints,
            three_way: false,
        })
    };
    let typed = |signed: &'static str, unsigned: &'static str, arity, ints| {
        Some(Int64Foreign::Runtime {
            signed,
            unsigned,
            arity,
            effectful: false,
            ints,
            three_way: false,
        })
    };
    match name {
        "zero_" | "uzero_" => inline(Operation::Constant(0)),
        "one_" | "uone_" => inline(Operation::Constant(1)),
        "negOne_" | "maxUnsignedValue_" => inline(Operation::Constant(-1)),
        "maxValue_" => inline(Operation::Constant(i64::MAX)),
        "minValue_" => inline(Operation::Constant(i64::MIN)),
        "fromInt_" => inline(Operation::FromInt),
        "unsigned_" => inline(Operation::IsUnsigned),
        "add_" => inline(Operation::Add),
        "subtract_" => inline(Operation::Subtract),
        "multiply_" => inline(Operation::Multiply),
        "negate_" => inline(Operation::Negate),
        "and_" => inline(Operation::And),
        "or_" => inline(Operation::Or),
        "xor_" => inline(Operation::Xor),
        "not_" => inline(Operation::Not),
        "shiftLeft_" => inline(Operation::ShiftLeft),
        "shiftRight_" => inline(Operation::ShiftRight),
        "shiftRightUnsigned_" => inline(Operation::ShiftRightUnsigned),
        "equals_" => inline(Operation::Compare(Comparison::Equal)),
        "notEquals_" => inline(Operation::Compare(Comparison::NotEqual)),
        "lessThan_" => inline(Operation::Compare(Comparison::LessThan)),
        "lessThanOrEqual_" => inline(Operation::Compare(Comparison::LessThanOrEqual)),
        "greaterThan_" => inline(Operation::Compare(Comparison::GreaterThan)),
        "greaterThanOrEqual_" => inline(Operation::Compare(Comparison::GreaterThanOrEqual)),
        "isZero_" => inline(Operation::IsZero),
        "isEven_" => inline(Operation::IsEven),
        "isOdd_" => inline(Operation::IsOdd),
        "isNegative_" => inline(Operation::IsNegative),
        "isPositive_" => inline(Operation::IsPositive),
        "toInt_" => inline(Operation::ToInt),
        "toNumber_" => inline(Operation::ToNumber),
        "getHighBits_" => inline(Operation::HighBits { unsigned: false }),
        "getHighBitsUnsigned_" => inline(Operation::HighBits { unsigned: true }),
        "getLowBits_" => inline(Operation::LowBits { unsigned: false }),
        "getLowBitsUnsigned_" => inline(Operation::LowBits { unsigned: true }),
        "toSigned_" | "toUnsigned_" => inline(Operation::Same),
        "divide_" => generic("Divide_", 2, &[]),
        "modulo_" => generic("Modulo_", 2, &[]),
        "compare_" => Some(Int64Foreign::Runtime {
            signed: "Compare_",
            unsigned: "Compare_",
            arity: 2,
            effectful: false,
            ints: &[],
            three_way: true,
        }),
        "toString_" => generic("ToString_", 2, &[1]),
        "rotateLeft_" => generic("RotateLeft_", 2, &[]),
        "rotateRight_" => generic("RotateRight_", 2, &[]),
        "getNumBitsAbs" => generic("GetNumBitsAbs", 1, &[]),
        "toBytes_" => generic("ToBytes_", 2, &[]),
        "fromBits_" => typed("FromBits_Int64", "FromBits_UInt64", 3, &[0, 1]),
        "fromBytes_" => typed("FromBytes_Int64", "FromBytes_UInt64", 3, &[]),
        "fromBytesLE_" => typed("FromBytesLE_Int64", "FromBytesLE_UInt64", 2, &[]),
        "fromBytesBE_" => typed("FromBytesBE_Int64", "FromBytesBE_UInt64", 2, &[]),
        "fromNumber_" => typed("FromNumber_Int64", "FromNumber_UInt64", 2, &[]),
        "fromValue_" => typed("FromValue_Int64", "FromValue_UInt64", 2, &[]),
        "safeReadLong_" => typed("SafeReadLong_Int64", "SafeReadLong_UInt64", 3, &[2]),
        "fromString_" => Some(Int64Foreign::Runtime {
            signed: "FromString_Int64",
            unsigned: "FromString_UInt64",
            arity: 3,
            effectful: true,
            ints: &[2],
            three_way: false,
        }),
        _ => None,
    }
}
