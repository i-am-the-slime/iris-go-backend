//! Go implementations of foreign imports and of library functions whose PureScript
//! definitions have a direct Go equivalent. The runtime functions live in the
//! purs-backend-go `go-support` module.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Foreign {
    Operator(Operator),
    Call { function: GoFunction, arity: usize, integers: Integers },
    RunEffect,
    Constant(GoFunction),
    Unit,
    UnsafeCoerce,
    Identity,
    EffectPure,
    EffectBind,
    EffectForEach,
    EffectTraverseArray,
    EffectForArray,
    MaybeIndex,
    Range,
    EffectCall { function: GoFunction, arity: usize },
    Print,
    ReferenceNew,
    ReferenceRead,
    ReferenceWrite,
    ReferenceModify,
}

/// Which arguments and whether the result of a go-support function are Go `int`
/// where generated code uses `int32`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Integers {
    pub arguments: &'static [usize],
    pub result: bool,
}

const NO_INTEGERS: Integers = Integers { arguments: &[], result: false };

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GoFunction {
    pub package: GoPackage,
    pub name: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GoPackage {
    Prim,
    Array,
}

impl GoPackage {
    pub fn path(self) -> &'static str {
        match self {
            GoPackage::Prim => "github.com/i-am-the-slime/purs-backend-go/go-support/prim",
            GoPackage::Array => "github.com/i-am-the-slime/purs-backend-go/go-support/array",
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            GoPackage::Prim => "prim",
            GoPackage::Array => "array",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    IntAdd,
    IntSubtract,
    IntMultiply,
    IntNegate,
    NumberAdd,
    NumberSubtract,
    NumberMultiply,
    NumberDivide,
    NumberNegate,
    BooleanAnd,
    BooleanOr,
    BooleanNot,
    StringAppend,
    ArrayLength,
    ArrayIndex,
    IntToNumber,
    Compare(Comparison),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Comparison {
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
}

impl Operator {
    pub fn arity(self) -> usize {
        match self {
            Operator::IntNegate
            | Operator::NumberNegate
            | Operator::BooleanNot
            | Operator::ArrayLength
            | Operator::IntToNumber => 1,
            _ => 2,
        }
    }
}

impl Foreign {
    pub fn arity(self) -> usize {
        match self {
            Foreign::Operator(operator) => operator.arity(),
            Foreign::Call { arity, .. } | Foreign::EffectCall { arity, .. } => arity,
            Foreign::Constant(_) | Foreign::Unit => 0,
            Foreign::UnsafeCoerce | Foreign::Identity | Foreign::EffectPure | Foreign::Print => 1,
            Foreign::RunEffect => 1,
            Foreign::ReferenceNew | Foreign::ReferenceRead => 1,
            Foreign::EffectBind | Foreign::EffectForEach => 2,
            Foreign::EffectTraverseArray | Foreign::EffectForArray => 2,
            Foreign::MaybeIndex => 4,
            Foreign::Range => 2,
            Foreign::ReferenceWrite | Foreign::ReferenceModify => 2,
        }
    }

    pub fn is_effectful(self) -> bool {
        matches!(
            self,
            Foreign::EffectPure
                | Foreign::EffectBind
                | Foreign::EffectForEach
                | Foreign::EffectTraverseArray
                | Foreign::EffectForArray
                | Foreign::EffectCall { .. }
                | Foreign::Print
                | Foreign::ReferenceNew
                | Foreign::ReferenceRead
                | Foreign::ReferenceWrite
                | Foreign::ReferenceModify
        )
    }
}

const fn prim(name: &'static str, arity: usize) -> Foreign {
    let function = GoFunction { package: GoPackage::Prim, name };
    Foreign::Call { function, arity, integers: NO_INTEGERS }
}

const fn prim_integers(
    name: &'static str,
    arity: usize,
    arguments: &'static [usize],
    result: bool,
) -> Foreign {
    let function = GoFunction { package: GoPackage::Prim, name };
    Foreign::Call { function, arity, integers: Integers { arguments, result } }
}

const fn array(name: &'static str, arity: usize) -> Foreign {
    let function = GoFunction { package: GoPackage::Array, name };
    Foreign::Call { function, arity, integers: NO_INTEGERS }
}

const fn array_integers(
    name: &'static str,
    arity: usize,
    arguments: &'static [usize],
    result: bool,
) -> Foreign {
    let function = GoFunction { package: GoPackage::Array, name };
    Foreign::Call { function, arity, integers: Integers { arguments, result } }
}

const fn constant(name: &'static str) -> Foreign {
    Foreign::Constant(GoFunction { package: GoPackage::Prim, name })
}

const fn compare(comparison: Comparison) -> Foreign {
    Foreign::Operator(Operator::Compare(comparison))
}

const FOREIGN_IMPORTS: &[(&str, &str, Foreign)] = &[
    ("Data.Semiring", "intAdd", Foreign::Operator(Operator::IntAdd)),
    ("Data.Semiring", "intMul", Foreign::Operator(Operator::IntMultiply)),
    ("Data.Semiring", "numAdd", Foreign::Operator(Operator::NumberAdd)),
    ("Data.Semiring", "numMul", Foreign::Operator(Operator::NumberMultiply)),
    ("Data.Ring", "intSub", Foreign::Operator(Operator::IntSubtract)),
    ("Data.Ring", "numSub", Foreign::Operator(Operator::NumberSubtract)),
    ("Data.EuclideanRing", "intDiv", prim_integers("IntDiv", 2, &[0, 1], true)),
    ("Data.EuclideanRing", "intMod", prim_integers("IntMod", 2, &[0, 1], true)),
    ("Data.EuclideanRing", "numDiv", Foreign::Operator(Operator::NumberDivide)),
    ("Data.EuclideanRing", "intDegree", prim_integers("IntDegree", 1, &[0], true)),
    ("Data.Eq", "eqBooleanImpl", compare(Comparison::Equal)),
    ("Data.Eq", "eqIntImpl", compare(Comparison::Equal)),
    ("Data.Eq", "eqNumberImpl", compare(Comparison::Equal)),
    ("Data.Eq", "eqCharImpl", compare(Comparison::Equal)),
    ("Data.Eq", "eqStringImpl", compare(Comparison::Equal)),
    ("Data.Eq", "eqArrayImpl", array("Eq", 3)),
    ("Data.Ord", "ordBooleanImpl", prim("OrdBoolean", 5)),
    ("Data.Ord", "ordIntImpl", prim_integers("OrdInt", 5, &[3, 4], false)),
    ("Data.Ord", "ordNumberImpl", prim("OrdNumber", 5)),
    ("Data.Ord", "ordStringImpl", prim("OrdString", 5)),
    ("Data.Ord", "ordCharImpl", prim("OrdChar", 5)),
    ("Data.HeytingAlgebra", "boolConj", Foreign::Operator(Operator::BooleanAnd)),
    ("Data.HeytingAlgebra", "boolDisj", Foreign::Operator(Operator::BooleanOr)),
    ("Data.HeytingAlgebra", "boolNot", Foreign::Operator(Operator::BooleanNot)),
    ("Data.Semigroup", "concatString", Foreign::Operator(Operator::StringAppend)),
    ("Data.Semigroup", "concatArray", array("Append", 2)),
    ("Data.Show", "showIntImpl", prim_integers("ShowInt", 1, &[0], false)),
    ("Data.Show", "showNumberImpl", prim("ShowNumber", 1)),
    ("Data.Show", "showCharImpl", prim("ShowChar", 1)),
    ("Data.Show", "showStringImpl", prim("ShowString", 1)),
    ("Data.Show", "showArrayImpl", prim("ShowArray", 2)),
    ("Data.Unit", "unit", Foreign::Unit),
    ("Data.Functor", "arrayMap", array("Map", 2)),
    ("Data.Bounded", "topInt", constant("TopInt")),
    ("Data.Bounded", "bottomInt", constant("BottomInt")),
    ("Data.Bounded", "topNumber", constant("TopNumber")),
    ("Data.Bounded", "bottomNumber", constant("BottomNumber")),
    ("Data.Bounded", "topChar", constant("TopChar")),
    ("Data.Bounded", "bottomChar", constant("BottomChar")),
    ("Data.Foldable", "foldrArray", array("Foldr", 3)),
    ("Data.Foldable", "foldlArray", array("Foldl", 3)),
    ("Data.Array", "length", Foreign::Operator(Operator::ArrayLength)),
    ("Data.Array", "reverse", array("Reverse", 1)),
    ("Data.Array", "concat", array("Concat", 1)),
    ("Data.Array", "indexImpl", Foreign::MaybeIndex),
    ("Data.Array", "unsafeIndexImpl", Foreign::Operator(Operator::ArrayIndex)),
    ("Data.Array", "filterImpl", array("Filter", 2)),
    ("Data.Array", "sliceImpl", array_integers("Slice", 3, &[0, 1], false)),
    ("Data.Array", "rangeImpl", Foreign::Range),
    ("Control.Bind", "arrayBind", array("Bind", 2)),
    ("Data.String.Common", "joinWith", prim("StringJoinWith", 2)),
    ("Data.String.Common", "split", prim("StringSplit", 2)),
    ("Data.String.Common", "toUpper", prim("StringToUpper", 1)),
    ("Data.String.Common", "toLower", prim("StringToLower", 1)),
    ("Data.String.Common", "trim", prim("StringTrim", 1)),
    ("Data.String.Common", "replace", prim("StringReplace", 3)),
    ("Data.String.Common", "replaceAll", prim("StringReplaceAll", 3)),
    ("Data.Int", "toNumber", Foreign::Operator(Operator::IntToNumber)),
    ("Data.Int", "quot", prim_integers("IntQuot", 2, &[0, 1], true)),
    ("Data.Int", "rem", prim_integers("IntRem", 2, &[0, 1], true)),
    ("Data.Int", "pow", prim_integers("IntPow", 2, &[0, 1], true)),
    ("Partial.Unsafe", "_unsafePartial", Foreign::Identity),
    ("Effect.Unsafe", "unsafePerformEffect", Foreign::RunEffect),
    ("Unsafe.Coerce", "unsafeCoerce", Foreign::UnsafeCoerce),
    ("Effect", "pureE", Foreign::EffectPure),
    ("Effect", "bindE", Foreign::EffectBind),
    ("Effect", "foreachE", Foreign::EffectForEach),
    ("Effect.Console", "log", Foreign::Print),
    ("Effect.Console", "info", Foreign::Print),
    ("Effect.Console", "warn", Foreign::Print),
    ("Effect.Console", "error", Foreign::Print),
    ("Effect.Ref", "_new", Foreign::ReferenceNew),
    ("Effect.Ref", "read", Foreign::ReferenceRead),
    ("Effect.Ref", "write", Foreign::ReferenceWrite),
    ("Effect.Ref", "modifyImpl", Foreign::ReferenceModify),
    ("Control.Monad.ST.Internal", "new", Foreign::ReferenceNew),
    ("Control.Monad.ST.Internal", "read", Foreign::ReferenceRead),
    ("Control.Monad.ST.Internal", "pure_", Foreign::EffectPure),
    ("Control.Monad.ST.Internal", "bind_", Foreign::EffectBind),
    ("Control.Monad.ST.Internal", "foreach", Foreign::EffectForEach),
];

/// Library functions replaced wholesale, keyed by the instance of their first
/// dictionary when they are overloaded.
const INTRINSICS: &[(&str, &str, &[&str], Foreign)] = &[
    ("Data.Array", "snoc", &[], array("Snoc", 2)),
    (
        "Data.Foldable",
        "traverse_",
        &["applicativeEffect", "foldableArray"],
        Foreign::EffectTraverseArray,
    ),
    ("Data.Foldable", "for_", &["applicativeEffect", "foldableArray"], Foreign::EffectForArray),
    ("Data.Ord", "lessThan", &["ordInt"], compare(Comparison::LessThan)),
    ("Data.Ord", "lessThanOrEq", &["ordInt"], compare(Comparison::LessThanOrEqual)),
    ("Data.Ord", "greaterThan", &["ordInt"], compare(Comparison::GreaterThan)),
    ("Data.Ord", "greaterThanOrEq", &["ordInt"], compare(Comparison::GreaterThanOrEqual)),
    ("Data.Ord", "lessThan", &["ordNumber"], compare(Comparison::LessThan)),
    ("Data.Ord", "lessThanOrEq", &["ordNumber"], compare(Comparison::LessThanOrEqual)),
    ("Data.Ord", "greaterThan", &["ordNumber"], compare(Comparison::GreaterThan)),
    ("Data.Ord", "greaterThanOrEq", &["ordNumber"], compare(Comparison::GreaterThanOrEqual)),
    ("Data.Ord", "lessThan", &["ordString"], compare(Comparison::LessThan)),
    ("Data.Ord", "lessThanOrEq", &["ordString"], compare(Comparison::LessThanOrEqual)),
    ("Data.Ord", "greaterThan", &["ordString"], compare(Comparison::GreaterThan)),
    ("Data.Ord", "greaterThanOrEq", &["ordString"], compare(Comparison::GreaterThanOrEqual)),
    ("Data.Ord", "lessThan", &["ordChar"], compare(Comparison::LessThan)),
    ("Data.Ord", "lessThanOrEq", &["ordChar"], compare(Comparison::LessThanOrEqual)),
    ("Data.Ord", "greaterThan", &["ordChar"], compare(Comparison::GreaterThan)),
    ("Data.Ord", "greaterThanOrEq", &["ordChar"], compare(Comparison::GreaterThanOrEqual)),
    ("Data.Eq", "notEq", &["eqInt"], compare(Comparison::NotEqual)),
    ("Data.Eq", "notEq", &["eqNumber"], compare(Comparison::NotEqual)),
    ("Data.Eq", "notEq", &["eqString"], compare(Comparison::NotEqual)),
    ("Data.Eq", "notEq", &["eqChar"], compare(Comparison::NotEqual)),
    ("Data.Eq", "notEq", &["eqBoolean"], compare(Comparison::NotEqual)),
    ("Data.Ring", "negate", &["ringInt"], Foreign::Operator(Operator::IntNegate)),
    ("Data.Ring", "negate", &["ringNumber"], Foreign::Operator(Operator::NumberNegate)),
];

pub fn foreign_import(module_name: &str, name: &str) -> Option<Foreign> {
    if let Some(identity) = uncurried_conversion(module_name, name) {
        return Some(identity);
    }
    FOREIGN_IMPORTS
        .iter()
        .find(|(module, item, _)| *module == module_name && *item == name)
        .map(|(_, _, foreign)| *foreign)
}

pub fn intrinsic(module_name: &str, name: &str, instances: &[&str]) -> Option<Foreign> {
    if let Some(identity) = uncurried_conversion(module_name, name) {
        return Some(identity);
    }
    INTRINSICS
        .iter()
        .find(|(module, item, expected, _)| {
            *module == module_name && *item == name && instances.starts_with(expected)
        })
        .map(|(_, _, _, foreign)| *foreign)
}

/// `FnN` types are curried functions in Go, so converting to and from them is free.
fn uncurried_conversion(module_name: &str, name: &str) -> Option<Foreign> {
    let arity = name.strip_prefix("runFn").or_else(|| name.strip_prefix("mkFn"))?;
    (module_name == "Data.Function.Uncurried" && arity.parse::<u8>().is_ok())
        .then_some(Foreign::Identity)
}
