use std::sync::OnceLock;

use super::{
    Boundary, CONS_LIST_ACCUMULATOR, Comparison, Constructed, Foreign, GoFunction, GoPackage,
    INSTANTIATE, Iteration, MaybeDestructor, Operator, PLAIN, RECORD, RESULT_PARAMETER,
    RecordOperation, Signature, Spelled, UNIT_VALUES, Utility, ignoring, int32_parameters, maybe,
    maybe_of_maybes, maybe_search, maybe_witnessed,
};

const fn call(package: GoPackage, name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    let function = GoFunction { package, name };
    Foreign::Call { function, arity, boundary }
}

const fn prim(name: &'static str, arity: usize) -> Foreign {
    call(GoPackage::Prim, name, arity, PLAIN)
}

const fn prim_with(name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    call(GoPackage::Prim, name, arity, boundary)
}

const fn regex(name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    call(GoPackage::Regex, name, arity, boundary)
}

const fn array(name: &'static str, arity: usize) -> Foreign {
    call(GoPackage::Array, name, arity, PLAIN)
}

const fn array_with(name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    call(GoPackage::Array, name, arity, boundary)
}

const fn iteration(
    package: GoPackage,
    name: &'static str,
    arity: usize,
    iteration: Iteration,
) -> Foreign {
    call(package, name, arity, Boundary { iteration: Some(iteration), ..PLAIN })
}

const fn uncurried(foreign: Foreign, callbacks: &'static [(usize, usize)]) -> Foreign {
    match foreign {
        Foreign::Call { function, arity, boundary } => Foreign::Call {
            function,
            arity,
            boundary: Boundary { uncurried: callbacks, ..boundary },
        },
        Foreign::Perform { function, arity, boundary } => Foreign::Perform {
            function,
            arity,
            boundary: Boundary { uncurried: callbacks, ..boundary },
        },
        foreign => foreign,
    }
}

const fn direct(name: &'static str, arity: usize) -> Foreign {
    call(GoPackage::Direct, name, arity, PLAIN)
}

const fn direct_with(name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    call(GoPackage::Direct, name, arity, boundary)
}

const fn js_bigint(name: &'static str, arity: usize) -> Foreign {
    call(GoPackage::JsBigInt, name, arity, PLAIN)
}

const fn js_bigint_with(name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    call(GoPackage::JsBigInt, name, arity, boundary)
}

const fn js_bigint_constant(name: &'static str) -> Foreign {
    Foreign::Constant(GoFunction { package: GoPackage::JsBigInt, name })
}

pub const SEQUENCE_ARRAY: Foreign = perform("SequenceArray", 1);

const fn perform(name: &'static str, arity: usize) -> Foreign {
    let function = GoFunction { package: GoPackage::Direct, name };
    Foreign::Perform { function, arity, boundary: PLAIN }
}

const fn thunk(
    package: GoPackage,
    name: &'static str,
    arity: usize,
    boundary: Boundary,
) -> Foreign {
    let function = GoFunction { package, name };
    Foreign::Perform { function, arity, boundary: Boundary { thunk: true, ..boundary } }
}

const fn perform_in(
    package: GoPackage,
    name: &'static str,
    arity: usize,
    boundary: Boundary,
) -> Foreign {
    let function = GoFunction { package, name };
    Foreign::Perform { function, arity, boundary }
}

const fn perform_with(name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    let function = GoFunction { package: GoPackage::Direct, name };
    Foreign::Perform { function, arity, boundary }
}

const fn object(name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    call(GoPackage::Object, name, arity, boundary)
}

const fn exception(name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    call(GoPackage::Exception, name, arity, boundary)
}

const fn foreign_value(name: &'static str, arity: usize) -> Foreign {
    call(GoPackage::ForeignValue, name, arity, PLAIN)
}

const fn argonaut(name: &'static str, arity: usize) -> Foreign {
    call(GoPackage::Argonaut, name, arity, PLAIN)
}

/// An `Effect.AVar` foreign, which receives the constructors it uses in place
/// of its `FFIUtil` record, the first argument.
const fn avar(name: &'static str, arity: usize, constructors: &'static [Constructed]) -> Foreign {
    let utility = Some(Utility { position: 0, constructors });
    perform_in(GoPackage::AVar, name, arity, Boundary { utility, ..ignoring(&[0]) })
}

const AVAR_PUT_CALLBACK: &[Constructed] =
    &[Constructed::CallbackParameter(3, "Left"), Constructed::CallbackParameter(3, "Right")];

const AVAR_CALLBACK: &[Constructed] =
    &[Constructed::CallbackParameter(2, "Left"), Constructed::CallbackParameter(2, "Right")];

const AVAR_MAYBE: &[Constructed] = &[Constructed::Result("Just"), Constructed::Result("Nothing")];

const fn constant(name: &'static str) -> Foreign {
    Foreign::Constant(GoFunction { package: GoPackage::Prim, name })
}

const fn compare(comparison: Comparison) -> Foreign {
    Foreign::Operator(Operator::Compare(comparison))
}

pub const ARRAY_FOLD: Foreign =
    uncurried(iteration(GoPackage::Array, "Foldl", 3, Iteration::FoldLeft), &[(0, 2)]);

pub const ARRAY_ANY: Foreign = iteration(GoPackage::Array, "Any", 2, Iteration::Any);

pub const ARRAY_ALL: Foreign = iteration(GoPackage::Direct, "All", 2, Iteration::All);

pub const EFFECT_FOLD: Foreign = direct_with(
    "FoldlEffect",
    3,
    Boundary { uncurried: &[(0, 2)], uncurried_perform: true, ..PLAIN },
);

pub fn array_fold() -> &'static Foreign {
    static FOLD: OnceLock<Foreign> = OnceLock::new();
    static SIGNATURE: OnceLock<Signature> = OnceLock::new();
    FOLD.get_or_init(|| {
        with_signature(ARRAY_FOLD, SIGNATURE.get_or_init(|| fold_signature(Spelled::Opaque)))
    })
}

pub fn effect_fold() -> &'static Foreign {
    static FOLD: OnceLock<Foreign> = OnceLock::new();
    static SIGNATURE: OnceLock<Signature> = OnceLock::new();
    let effect = || Spelled::Effect(Box::new(Spelled::Opaque));
    FOLD.get_or_init(|| {
        with_signature(EFFECT_FOLD, SIGNATURE.get_or_init(|| fold_signature(effect())))
    })
}

fn fold_signature(result: Spelled) -> Signature {
    let element = Box::new(Spelled::Function(Box::new(Spelled::Opaque), Box::new(result.clone())));
    let step = Spelled::Function(Box::new(Spelled::Opaque), element);
    let array = Spelled::Array(Box::new(Spelled::Opaque));
    Signature { parameters: vec![step, Spelled::Opaque, array], result }
}

fn with_signature(foreign: Foreign, signature: &'static Signature) -> Foreign {
    match foreign {
        Foreign::Call { function, arity, boundary } => Foreign::Call {
            function,
            arity,
            boundary: Boundary { signature: Some(signature), ..boundary },
        },
        foreign => foreign,
    }
}

pub const OBJECT_KEYS: Foreign = object("Keys", 1, PLAIN);

pub const OBJECT_INDEX: Foreign = object("UnsafeIndex", 2, PLAIN);

pub const OBJECT_FROM_ENTRIES: Foreign = object("FromEntries", 2, PLAIN);

pub const ARRAY_SLICE: Foreign = array_with("Slice", 3, int32_parameters(&[0, 1]));

pub const ARRAY_SORT_BY: Foreign = uncurried(direct("SortBy", 3), &[(0, 2)]);

pub const ARRAY_SCANL: Foreign = uncurried(array("Scanl", 3), &[(0, 2)]);

pub const ARRAY_REPLICATE: Foreign = array_with("Replicate", 2, int32_parameters(&[0]));

pub const FOREIGN_RECORD: Foreign = direct("ForeignRecord", 2);

pub const FROM_CHAR_ARRAY: Foreign = prim("CharArrayToString", 1);

pub const TO_CHAR_ARRAY: Foreign = prim("StringToCharArray", 1);

pub const INT_DIVIDE: Foreign = prim_with("IntDiv", 2, int32_parameters(&[0, 1]));

pub const INT_MODULO: Foreign = prim_with("IntMod", 2, int32_parameters(&[0, 1]));

pub const ARRAY_APPEND: Foreign = array("Append", 2);
/// Data.Array.ST.Partial's peek, read without a bounds test.
pub const MUTABLE_PEEK_UNSAFE: Foreign =
    thunk(GoPackage::Array, "PeekUnsafe", 2, int32_parameters(&[0]));
/// Whether an index is within a mutable array: the bounds test of Data.Array.ST's peek, which
/// the simplifier makes explicit (simplify/choice.rs) and the emitter writes in place.
pub const MUTABLE_WITHIN: Foreign = thunk(GoPackage::Array, "Within", 2, int32_parameters(&[0]));
pub const APPENDER: Foreign = perform_in(GoPackage::Direct, "Appender", 0, INSTANTIATE);

pub(super) const FOREIGN_IMPORTS: &[(&str, &str, Foreign)] = &[
    ("Data.Semiring", "intAdd", Foreign::Operator(Operator::IntAdd)),
    ("Data.Semiring", "intMul", Foreign::Operator(Operator::IntMultiply)),
    ("Data.Semiring", "numAdd", Foreign::Operator(Operator::NumberAdd)),
    ("Data.Semiring", "numMul", Foreign::Operator(Operator::NumberMultiply)),
    ("Data.Ring", "intSub", Foreign::Operator(Operator::IntSubtract)),
    ("Data.Ring", "numSub", Foreign::Operator(Operator::NumberSubtract)),
    ("Data.EuclideanRing", "intDiv", INT_DIVIDE),
    ("Data.EuclideanRing", "intMod", INT_MODULO),
    ("Data.EuclideanRing", "numDiv", Foreign::Operator(Operator::NumberDivide)),
    ("Data.EuclideanRing", "intDegree", prim_with("IntDegree", 1, int32_parameters(&[0]))),
    ("Data.Eq", "eqBooleanImpl", compare(Comparison::Equal)),
    ("Data.Eq", "eqIntImpl", compare(Comparison::Equal)),
    ("Data.Eq", "eqNumberImpl", compare(Comparison::Equal)),
    ("Data.Eq", "eqCharImpl", compare(Comparison::Equal)),
    ("Data.Eq", "eqStringImpl", compare(Comparison::Equal)),
    ("Data.Eq", "eqArrayImpl", uncurried(array("Eq", 3), &[(0, 2)])),
    ("Data.Ord", "ordBooleanImpl", prim("OrdBoolean", 5)),
    ("Data.Ord", "ordIntImpl", Foreign::Ordering),
    ("Data.Ord", "ordNumberImpl", Foreign::Ordering),
    ("Data.Ord", "ordStringImpl", Foreign::Ordering),
    ("Data.Ord", "ordCharImpl", Foreign::Ordering),
    ("Data.Ord", "ordArrayImpl", uncurried(direct("CompareArray", 3), &[(0, 2)])),
    ("Data.Show", "intercalate", prim("StringJoinWith", 2)),
    ("Data.Show.Generic", "intercalate", prim("StringJoinWith", 2)),
    ("Control.Apply", "arrayApply", array("Apply", 2)),
    ("Record.Unsafe", "unsafeGet", Foreign::RecordGet),
    // Whether a record has a field of a label; `Data.Variant` asks it before
    // reading a handler with `unsafeGet`.
    ("Record.Unsafe", "unsafeHas", Foreign::RecordHas),
    ("Record.Unsafe", "unsafeSet", Foreign::Record(RecordOperation::Insert)),
    ("Record.Unsafe", "unsafeDelete", Foreign::Record(RecordOperation::Delete)),
    ("Record.Unsafe.Union", "unsafeUnionFn", Foreign::Record(RecordOperation::Union)),
    ("Record.Studio.Shrink", "shrinkImpl", Foreign::Record(RecordOperation::Shrink)),
    ("Record.Builder", "copyRecord", Foreign::Identity),
    ("Record.Builder", "unsafeInsert", Foreign::Record(RecordOperation::Insert)),
    ("Record.Builder", "unsafeModify", Foreign::Record(RecordOperation::Modify)),
    ("Record.Builder", "unsafeDelete", Foreign::Record(RecordOperation::Delete)),
    ("Record.Builder", "unsafeRename", Foreign::Record(RecordOperation::Rename)),
    ("Data.HeytingAlgebra", "boolConj", Foreign::Operator(Operator::BooleanAnd)),
    ("Data.HeytingAlgebra", "boolDisj", Foreign::Operator(Operator::BooleanOr)),
    ("Data.HeytingAlgebra", "boolNot", Foreign::Operator(Operator::BooleanNot)),
    ("Data.Semigroup", "concatString", Foreign::Operator(Operator::StringAppend)),
    ("Data.Semigroup", "concatArray", ARRAY_APPEND),
    ("Data.Show", "showIntImpl", prim_with("ShowInt", 1, int32_parameters(&[0]))),
    ("Data.Show", "showNumberImpl", prim("ShowNumber", 1)),
    ("Data.Show", "showCharImpl", prim("ShowChar", 1)),
    ("Data.Show", "showStringImpl", prim("ShowString", 1)),
    ("Data.Show", "showArrayImpl", prim("ShowArray", 2)),
    ("Data.Unit", "unit", Foreign::Unit),
    ("Data.Functor", "arrayMap", iteration(GoPackage::Array, "Map", 2, Iteration::Map)),
    ("Data.Bounded", "topInt", constant("TopInt")),
    ("Data.Bounded", "bottomInt", constant("BottomInt")),
    ("Data.Bounded", "topNumber", constant("TopNumber")),
    ("Data.Bounded", "bottomNumber", constant("BottomNumber")),
    ("Data.Bounded", "topChar", constant("TopChar")),
    ("Data.Bounded", "bottomChar", constant("BottomChar")),
    (
        "Data.Foldable",
        "foldrArray",
        uncurried(iteration(GoPackage::Array, "Foldr", 3, Iteration::FoldRight), &[(0, 2)]),
    ),
    ("Data.Foldable", "foldlArray", ARRAY_FOLD),
    ("Data.Array", "length", Foreign::Operator(Operator::ArrayLength)),
    ("Data.Array", "reverse", array("Reverse", 1)),
    ("Data.Array", "concat", array("Concat", 1)),
    ("Data.Array", "indexImpl", Foreign::MaybeIndex),
    ("Data.Array", "unsafeIndexImpl", Foreign::Operator(Operator::ArrayIndex)),
    ("Data.Array", "filterImpl", iteration(GoPackage::Array, "Filter", 2, Iteration::Filter)),
    ("Data.Array", "sliceImpl", array_with("Slice", 3, int32_parameters(&[0, 1]))),
    ("Data.Array", "rangeImpl", Foreign::Range),
    ("Data.Array", "replicateImpl", ARRAY_REPLICATE),
    (
        "Data.Array",
        "zipWithImpl",
        uncurried(iteration(GoPackage::Array, "ZipWith", 3, Iteration::ZipWith), &[(0, 2)]),
    ),
    ("Data.Array", "anyImpl", ARRAY_ANY),
    ("Data.Array", "partitionImpl", direct_with("Partition", 2, RECORD)),
    ("Data.Array", "fromFoldableImpl", direct_with("FromFoldable", 2, CONS_LIST_ACCUMULATOR)),
    ("Data.Array", "allImpl", ARRAY_ALL),
    ("Data.Array", "scanlImpl", ARRAY_SCANL),
    ("Data.Array", "scanrImpl", uncurried(array("Scanr", 3), &[(0, 2)])),
    ("Data.Array", "unconsImpl", uncurried(direct("Uncons", 3), &[(1, 2)])),
    ("Data.Array", "sortByImpl", ARRAY_SORT_BY),
    ("Data.Array", "findMapImpl", direct_with("FindMap", 4, maybe_search(0, 1))),
    ("Data.Array.Parallel", "parallelMap", array("ParallelMap", 2)),
    (
        "Data.Array",
        "findIndexImpl",
        array_with(
            "FindIndex",
            4,
            Boundary { iteration: Some(Iteration::FindIndex), ..maybe(0, 1) },
        ),
    ),
    (
        "Data.Array",
        "findLastIndexImpl",
        array_with(
            "FindLastIndex",
            4,
            Boundary { iteration: Some(Iteration::FindLastIndex), ..maybe(0, 1) },
        ),
    ),
    (
        "Data.Array",
        "_insertAt",
        array_with("InsertAt", 5, Boundary { int32_parameters: &[2], ..maybe(0, 1) }),
    ),
    ("Data.Array", "_deleteAt", direct_with("DeleteAt", 4, maybe(0, 1))),
    ("Data.Array", "_updateAt", direct_with("UpdateAt", 5, maybe(0, 1))),
    ("Data.Array.NonEmpty.Internal", "foldr1Impl", uncurried(array("Foldr1", 2), &[(0, 2)])),
    ("Data.Array.NonEmpty.Internal", "foldl1Impl", uncurried(array("Foldl1", 2), &[(0, 2)])),
    ("Data.Array.ST", "new", Foreign::MutableArrayNew),
    ("Data.Array.ST", "unsafeFreezeImpl", thunk(GoPackage::Array, "UnsafeFreeze", 1, PLAIN)),
    ("Data.Array.ST", "unsafeThawImpl", thunk(GoPackage::Array, "UnsafeThaw", 1, PLAIN)),
    ("Data.Array.ST", "thawImpl", thunk(GoPackage::Array, "Thaw", 1, PLAIN)),
    ("Data.Array.ST", "freezeImpl", thunk(GoPackage::Array, "Freeze", 1, PLAIN)),
    ("Data.Array.ST", "cloneImpl", thunk(GoPackage::Array, "Clone", 1, PLAIN)),
    ("Data.Array.ST", "peekImpl", thunk(GoPackage::Array, "Peek", 4, int32_parameters(&[2]))),
    ("Data.Array.ST", "pokeImpl", thunk(GoPackage::Array, "Poke", 3, int32_parameters(&[0]))),
    ("Data.Array.ST", "lengthImpl", thunk(GoPackage::Array, "Length", 1, PLAIN)),
    ("Data.Array.ST", "popImpl", thunk(GoPackage::Array, "Pop", 3, maybe(0, 1))),
    ("Data.Array.ST", "shiftImpl", thunk(GoPackage::Array, "Shift", 3, maybe(0, 1))),
    ("Data.Array.ST", "pushImpl", thunk(GoPackage::Array, "Push", 2, PLAIN)),
    ("Data.Array.ST", "pushAllImpl", thunk(GoPackage::Array, "PushAll", 2, PLAIN)),
    ("Data.Array.ST", "unshiftAllImpl", thunk(GoPackage::Array, "UnshiftAll", 2, PLAIN)),
    (
        "Data.Array.ST",
        "spliceImpl",
        thunk(GoPackage::Array, "Splice", 4, int32_parameters(&[0, 1])),
    ),
    ("Data.Array.ST", "sortByImpl", uncurried(perform("SortByMutable", 3), &[(0, 2)])),
    ("Data.Array.ST", "toAssocArrayImpl", Foreign::AssocArray),
    ("Data.Array.ST.Partial", "peekImpl", MUTABLE_PEEK_UNSAFE),
    (
        "Data.Array.ST.Partial",
        "pokeImpl",
        thunk(GoPackage::Array, "PokeUnsafe", 3, int32_parameters(&[0])),
    ),
    ("Effect.Exception", "showErrorImpl", exception("ShowErrorImpl", 1, PLAIN)),
    ("Effect.Exception", "error", exception("NewError", 1, PLAIN)),
    ("Effect.Exception", "errorWithCause", exception("ErrorWithCause", 2, PLAIN)),
    ("Effect.Exception", "errorWithName", exception("ErrorWithName", 2, PLAIN)),
    ("Effect.Exception", "message", exception("Message", 1, PLAIN)),
    ("Effect.Exception", "name", exception("Name", 1, PLAIN)),
    ("Effect.Exception", "stackImpl", exception("StackImpl", 3, maybe(0, 1))),
    ("Effect.Exception", "throwException", Foreign::Throw),
    ("Effect.Exception", "catchException", perform_with("CatchException", 2, UNIT_VALUES)),
    ("Effect.Aff", "_pure", Foreign::EffectPure),
    ("Effect.Aff", "_bind", Foreign::EffectBind),
    ("Effect.Aff", "_map", Foreign::EffectMap),
    ("Effect.Aff", "_liftEffect", Foreign::Identity),
    ("Effect.Aff", "_throwError", Foreign::Throw),
    ("Effect.Aff", "_catchError", perform_with("CatchError", 2, UNIT_VALUES)),
    ("Effect.Aff", "_delay", perform_in(GoPackage::Aff, "DelayDirect", 2, ignoring(&[0]))),
    ("Effect.Aff", "_parAffMap", Foreign::EffectMap),
    ("Effect.Aff", "_parAffApply", perform_in(GoPackage::Aff, "ParApplyDirect", 2, UNIT_VALUES)),
    ("Effect.Aff", "_parAffAlt", perform_in(GoPackage::Aff, "ParAltDirect", 2, UNIT_VALUES)),
    ("Effect.Aff", "_sequential", Foreign::Identity),
    (
        "Effect.Aff",
        "generalBracket",
        perform_in(
            GoPackage::Aff,
            "GeneralBracketDirect",
            3,
            Boundary { record_arguments: &[1], ..UNIT_VALUES },
        ),
    ),
    ("Effect.Aff", "makeAff", Foreign::MakeAff),
    ("Effect.Aff", "_fork", Foreign::ForkFiber),
    ("Effect.Aff", "_makeFiber", Foreign::NewFiber),
    ("Effect.Aff", "_makeSupervisedFiber", Foreign::NewSupervisedFiber),
    ("Effect.Aff", "_killAll", perform_in(GoPackage::Aff, "KillAllDirect", 3, PLAIN)),
    ("Promise.Internal", "resolve", call(GoPackage::Promise, "Resolve", 1, PLAIN)),
    ("Promise.Internal", "reject", call(GoPackage::Promise, "Reject", 1, PLAIN)),
    ("Promise.Internal", "then_", perform_in(GoPackage::Promise, "Then", 2, PLAIN)),
    ("Promise.Internal", "thenOrCatch", perform_in(GoPackage::Promise, "ThenOrCatch", 3, PLAIN)),
    ("Promise.Internal", "catch", perform_in(GoPackage::Promise, "Catch", 2, PLAIN)),
    ("Promise.Internal", "all", perform_in(GoPackage::Promise, "All", 1, PLAIN)),
    ("Promise.Internal", "race", perform_in(GoPackage::Promise, "Race", 1, PLAIN)),
    ("Promise.Rejection", "fromError", call(GoPackage::Promise, "FromError", 1, PLAIN)),
    ("Promise.Rejection", "_toError", call(GoPackage::Promise, "ToError", 3, maybe(0, 1))),
    ("Foreign", "typeOf", foreign_value("TypeOf", 1)),
    ("Foreign", "tagOf", foreign_value("TagOf", 1)),
    ("Foreign", "isNull", foreign_value("IsNull", 1)),
    ("Foreign", "isUndefined", foreign_value("IsUndefined", 1)),
    ("Foreign", "isArray", foreign_value("IsArray", 1)),
    (
        "Foreign.Index",
        "unsafeReadPropImpl",
        call(GoPackage::ForeignValue, "UnsafeReadPropImpl", 4, Boundary { lazy: &[0], ..PLAIN }),
    ),
    ("Foreign.Index", "unsafeHasOwnProperty", foreign_value("UnsafeHasOwnProperty", 2)),
    ("Foreign.Index", "unsafeHasProperty", foreign_value("UnsafeHasProperty", 2)),
    (
        "Yoga.JSON",
        "_undefined",
        Foreign::Constant(GoFunction { package: GoPackage::ForeignValue, name: "Undefined" }),
    ),
    (
        "Yoga.JSON",
        "_unsafeStringify",
        call(
            GoPackage::ForeignValue,
            "UnsafeStringify",
            1,
            Boundary { foreign_arguments: &[0], ..PLAIN },
        ),
    ),
    (
        "Yoga.JSON",
        "_unsafePrettyStringify",
        call(
            GoPackage::ForeignValue,
            "UnsafePrettyStringify",
            2,
            Boundary { int32_parameters: &[0], foreign_arguments: &[1], ..PLAIN },
        ),
    ),
    ("Yoga.JSON", "_parseJSON", perform_in(GoPackage::ForeignValue, "ParseJSON", 1, PLAIN)),
    ("Data.Argonaut.Core", "fromBoolean", argonaut("FromBoolean", 1)),
    ("Data.Argonaut.Core", "fromNumber", argonaut("FromNumber", 1)),
    ("Data.Argonaut.Core", "fromString", argonaut("FromString", 1)),
    ("Data.Argonaut.Core", "fromArray", argonaut("FromArray", 1)),
    ("Data.Argonaut.Core", "fromObject", argonaut("FromObject", 1)),
    (
        "Data.Argonaut.Core",
        "jsonNull",
        Foreign::Constant(GoFunction { package: GoPackage::Argonaut, name: "JsonNull" }),
    ),
    ("Data.Argonaut.Core", "stringify", argonaut("Stringify", 1)),
    (
        "Data.Argonaut.Core",
        "stringifyWithIndent",
        call(GoPackage::Argonaut, "StringifyWithIndent", 2, int32_parameters(&[0])),
    ),
    ("Data.Argonaut.Core", "_caseJson", argonaut("CaseJson", 7)),
    ("Data.Argonaut.Core", "_compare", argonaut("Compare", 5)),
    ("Data.Argonaut.Parser", "_jsonParser", argonaut("JsonParser", 3)),
    ("Effect.AVar", "empty", perform_in(GoPackage::AVar, "Empty", 0, INSTANTIATE)),
    ("Effect.AVar", "_newVar", perform_in(GoPackage::AVar, "NewVar", 1, PLAIN)),
    ("Effect.AVar", "_killVar", avar("KillVar", 3, &[])),
    ("Effect.AVar", "_putVar", avar("PutVar", 4, AVAR_PUT_CALLBACK)),
    ("Effect.AVar", "_tryPutVar", avar("TryPutVar", 3, &[])),
    ("Effect.AVar", "_takeVar", avar("TakeVar", 3, AVAR_CALLBACK)),
    ("Effect.AVar", "_tryTakeVar", avar("TryTakeVar", 2, AVAR_MAYBE)),
    ("Effect.AVar", "_readVar", avar("ReadVar", 3, AVAR_CALLBACK)),
    ("Effect.AVar", "_tryReadVar", avar("TryReadVar", 2, AVAR_MAYBE)),
    (
        "Effect.AVar",
        "_status",
        avar(
            "Status",
            2,
            &[
                Constructed::Result("Killed"),
                Constructed::Result("Filled"),
                Constructed::Result("Empty"),
            ],
        ),
    ),
    ("Yoga.Om.Error", "newParallelError", call(GoPackage::YogaOm, "NewParallelError", 1, PLAIN)),
    (
        "Yoga.Om.Error",
        "getParallelError",
        call(GoPackage::YogaOm, "GetParallelError", 1, RESULT_PARAMETER),
    ),
    (
        "Yoga.Om.Error",
        "toParallelErrorImpl",
        call(GoPackage::YogaOm, "ToParallelErrorImpl", 3, maybe(0, 1)),
    ),
    ("Data.Nullable", "null", call(GoPackage::Nullable, "Null", 0, INSTANTIATE)),
    ("Data.Nullable", "notNull", call(GoPackage::Nullable, "NotNull", 1, PLAIN)),
    ("Data.Nullable", "nullable", call(GoPackage::Nullable, "Nullable", 3, PLAIN)),
    ("Foreign.Object", "empty", object("Empty", 0, INSTANTIATE)),
    ("Foreign.Object", "_copyST", thunk(GoPackage::Object, "CopyST", 1, PLAIN)),
    ("Foreign.Object", "runST", Foreign::RunEffect),
    ("Foreign.Object", "_fmapObject", object("FmapObject", 2, PLAIN)),
    ("Foreign.Object", "_mapWithKey", uncurried(object("MapWithKey", 2, PLAIN), &[(1, 2)])),
    ("Foreign.Object", "_foldM", Foreign::ObjectFoldM),
    (
        "Foreign.Object",
        "_foldSCObject",
        direct_with(
            "FoldSCObject",
            4,
            Boundary {
                ignored: &[3],
                maybe_destructor: Some(MaybeDestructor { position: 3, witness: 2 }),
                uncurried: &[(2, 3)],
                ..PLAIN
            },
        ),
    ),
    ("Foreign.Object", "all", uncurried(object("All", 2, PLAIN), &[(0, 2)])),
    ("Foreign.Object", "size", object("Size", 1, PLAIN)),
    ("Foreign.Object", "_lookup", object("Lookup", 4, PLAIN)),
    ("Foreign.Object", "_lookupST", thunk(GoPackage::Object, "LookupST", 4, PLAIN)),
    ("Foreign.Object", "toArrayWithKey", uncurried(object("ToArrayWithKey", 2, PLAIN), &[(0, 2)])),
    ("Foreign.Object", "keys", object("Keys", 1, PLAIN)),
    ("Foreign.Object.ST", "new", thunk(GoPackage::Object, "New", 0, INSTANTIATE)),
    ("Foreign.Object.ST", "peekImpl", thunk(GoPackage::Object, "PeekImpl", 4, PLAIN)),
    ("Foreign.Object.ST", "poke", thunk(GoPackage::Object, "Poke", 3, PLAIN)),
    ("Foreign.Object.ST", "delete", thunk(GoPackage::Object, "Delete", 2, PLAIN)),
    (
        "Foreign.Object.ST.Unsafe",
        "unsafeFreeze",
        thunk(GoPackage::Object, "UnsafeFreeze", 1, PLAIN),
    ),
    (
        "Data.FunctorWithIndex",
        "mapWithIndexArray",
        uncurried(
            iteration(GoPackage::Direct, "MapWithIndex", 2, Iteration::MapWithIndex),
            &[(0, 2)],
        ),
    ),
    ("Data.Unfoldable", "unfoldrArrayImpl", Foreign::Unfoldr),
    ("Data.Unfoldable1", "unfoldr1ArrayImpl", Foreign::Unfoldr1),
    ("Control.Bind", "arrayBind", iteration(GoPackage::Array, "Bind", 2, Iteration::Bind)),
    ("Data.String.Common", "joinWith", prim("StringJoinWith", 2)),
    ("Data.String.Common", "split", prim("StringSplit", 2)),
    ("Data.String.Common", "toUpper", prim("StringToUpper", 1)),
    ("Data.String.Common", "toLower", prim("StringToLower", 1)),
    ("Data.String.Common", "trim", prim("StringTrim", 1)),
    ("Data.String.Common", "replace", prim("StringReplace", 3)),
    ("Data.String.Common", "replaceAll", prim("StringReplaceAll", 3)),
    ("Data.String.CodeUnits", "singleton", prim("CharSingleton", 1)),
    ("Data.String.CodeUnits", "fromCharArray", FROM_CHAR_ARRAY),
    ("Data.String.CodeUnits", "toCharArray", TO_CHAR_ARRAY),
    ("Data.String.CodeUnits", "length", prim_with("CodeUnitLength", 1, PLAIN)),
    ("Data.String.CodeUnits", "countPrefix", prim_with("CodeUnitCountPrefix", 2, PLAIN)),
    ("Data.String.CodeUnits", "take", prim_with("CodeUnitTake", 2, int32_parameters(&[0]))),
    ("Data.String.CodeUnits", "drop", prim_with("CodeUnitDrop", 2, int32_parameters(&[0]))),
    ("Data.String.CodeUnits", "slice", prim_with("CodeUnitSlice", 3, int32_parameters(&[0, 1]))),
    (
        "Data.String.CodeUnits",
        "splitAt",
        direct_with("SplitAt", 2, Boundary { int32_parameters: &[0], ..RECORD }),
    ),
    (
        "Data.String.CodeUnits",
        "_charAt",
        prim_with("CodeUnitCharAt", 4, Boundary { int32_parameters: &[2], ..maybe(0, 1) }),
    ),
    ("Data.String.CodeUnits", "_toChar", prim_with("CodeUnitToChar", 3, maybe(0, 1))),
    ("Data.String.CodeUnits", "_indexOf", prim_with("CodeUnitIndexOf", 4, maybe(0, 1))),
    (
        "Data.String.CodeUnits",
        "_indexOfStartingAt",
        prim_with(
            "CodeUnitIndexOfStartingAt",
            5,
            Boundary { int32_parameters: &[3], ..maybe(0, 1) },
        ),
    ),
    ("Data.String.CodeUnits", "_lastIndexOf", prim_with("CodeUnitLastIndexOf", 4, maybe(0, 1))),
    (
        "Data.String.CodeUnits",
        "_lastIndexOfStartingAt",
        prim_with(
            "CodeUnitLastIndexOfStartingAt",
            5,
            Boundary { int32_parameters: &[3], ..maybe(0, 1) },
        ),
    ),
    (
        "Data.String.CodePoints",
        "_singleton",
        direct_with("CodePointSingleton", 2, Boundary { int32_parameters: &[1], ..ignoring(&[0]) }),
    ),
    (
        "Data.String.CodePoints",
        "_fromCodePointArray",
        direct_with("CodePointsFromArray", 2, ignoring(&[0])),
    ),
    (
        "Data.String.CodePoints",
        "_toCodePointArray",
        direct_with("ToCodePointArray", 3, ignoring(&[0, 1])),
    ),
    (
        "Data.String.CodePoints",
        "_codePointAt",
        direct_with(
            "CodePointAt",
            6,
            Boundary { ignored: &[0, 3], int32_parameters: &[4], ..maybe(1, 2) },
        ),
    ),
    (
        "Data.String.CodePoints",
        "_countPrefix",
        direct_with("CodePointCountPrefix", 4, ignoring(&[0, 1])),
    ),
    (
        "Data.String.CodePoints",
        "_take",
        direct_with("CodePointTake", 3, Boundary { int32_parameters: &[1], ..ignoring(&[0]) }),
    ),
    (
        "Data.String.CodePoints",
        "_unsafeCodePointAt0",
        direct_with("CodePointAt0", 2, ignoring(&[0])),
    ),
    ("Data.String.Unsafe", "char", prim("CharFromString", 1)),
    ("Data.String.Unsafe", "charAt", prim_with("CharAt", 2, int32_parameters(&[0]))),
    ("Data.Number", "nan", constant("NumberNaN")),
    ("Data.Number", "infinity", constant("NumberInfinity")),
    ("Data.Number", "isNaN", prim("NumberIsNaN", 1)),
    ("Data.Number", "isFinite", prim("NumberIsFinite", 1)),
    ("Data.Number", "fromStringImpl", prim_with("NumberFromString", 4, maybe(2, 3))),
    ("Data.Number", "abs", prim("NumberAbs", 1)),
    ("Data.Number", "acos", prim("NumberAcos", 1)),
    ("Data.Number", "asin", prim("NumberAsin", 1)),
    ("Data.Number", "atan", prim("NumberAtan", 1)),
    ("Data.Number", "atan2", prim("NumberAtan2", 2)),
    ("Data.Number", "ceil", prim("NumberCeil", 1)),
    ("Data.Number", "cos", prim("NumberCos", 1)),
    ("Data.Number", "exp", prim("NumberExp", 1)),
    ("Data.Number", "floor", prim("NumberFloor", 1)),
    ("Data.Number", "log", prim("NumberLog", 1)),
    ("Data.Number", "max", prim("NumberMax", 2)),
    ("Data.Number", "min", prim("NumberMin", 2)),
    ("Data.Number", "pow", prim("NumberPow", 2)),
    ("Data.Number", "remainder", prim("NumberRemainder", 2)),
    ("Data.Number", "round", prim("NumberRound", 1)),
    ("Data.Number", "sign", prim("NumberSign", 1)),
    ("Data.Number", "sin", prim("NumberSin", 1)),
    ("Data.Number", "sqrt", prim("NumberSqrt", 1)),
    ("Data.Number", "tan", prim("NumberTan", 1)),
    ("Data.Number", "trunc", prim("NumberTrunc", 1)),
    (
        "Data.Number.Format",
        "toPrecisionNative",
        prim_with("NumberToPrecision", 2, int32_parameters(&[0])),
    ),
    ("Data.Number.Format", "toFixedNative", prim_with("NumberToFixed", 2, int32_parameters(&[0]))),
    (
        "Data.Number.Format",
        "toExponentialNative",
        prim_with("NumberToExponential", 2, int32_parameters(&[0])),
    ),
    ("Data.Number.Format", "toString", prim("NumberToString", 1)),
    ("Data.Int", "fromNumberImpl", Foreign::IntFromNumber),
    (
        "Data.Int",
        "fromStringAsImpl",
        prim_with("IntFromStringAs", 4, Boundary { int32_parameters: &[2], ..maybe(0, 1) }),
    ),
    ("Data.Int", "toStringAs", prim_with("IntToStringAs", 2, int32_parameters(&[0, 1]))),
    ("Data.Int.Bits", "and", Foreign::Operator(Operator::IntAnd)),
    ("Data.Int.Bits", "or", Foreign::Operator(Operator::IntOr)),
    ("Data.Int.Bits", "xor", Foreign::Operator(Operator::IntXor)),
    ("Data.Int.Bits", "shl", Foreign::Operator(Operator::IntShiftLeft)),
    ("Data.Int.Bits", "shr", Foreign::Operator(Operator::IntShiftRight)),
    ("Data.Int.Bits", "zshr", Foreign::Operator(Operator::IntZeroFillShiftRight)),
    ("Data.Int.Bits", "complement", Foreign::Operator(Operator::IntComplement)),
    ("Data.Enum", "toCharCode", prim_with("ToCharCode", 1, PLAIN)),
    ("Data.Enum", "fromCharCode", prim_with("FromCharCode", 1, int32_parameters(&[0]))),
    ("Data.String.Common", "_localeCompare", prim("LocaleCompare", 5)),
    ("Data.String.Regex", "showRegexImpl", regex("Show", 1, PLAIN)),
    ("Data.String.Regex", "regexImpl", regex("New", 4, PLAIN)),
    ("Data.String.Regex", "source", regex("Source", 1, PLAIN)),
    ("Data.String.Regex", "flagsImpl", regex("Flags", 1, RECORD)),
    ("Data.String.Regex", "test", regex("Test", 2, PLAIN)),
    ("Data.String.Regex", "_match", regex("Match", 4, maybe_of_maybes(0, 1))),
    ("Data.String.Regex", "replace", regex("Replace", 3, PLAIN)),
    ("Data.String.Regex", "split", regex("Split", 2, PLAIN)),
    ("Data.String.Regex", "_replaceBy", regex("ReplaceBy", 5, maybe_witnessed(0, 1, 3))),
    ("Data.String.Regex", "_search", regex("Search", 4, maybe(0, 1))),
    ("Data.Int", "toNumber", Foreign::Operator(Operator::IntToNumber)),
    ("Data.Int", "quot", prim_with("IntQuot", 2, int32_parameters(&[0, 1]))),
    ("Data.Int", "rem", prim_with("IntRem", 2, int32_parameters(&[0, 1]))),
    ("Data.Int", "pow", prim_with("IntPow", 2, int32_parameters(&[0, 1]))),
    ("JS.BigInt", "fromStringImpl", js_bigint_with("FromString", 3, maybe(0, 1))),
    (
        "JS.BigInt",
        "fromStringAsImpl",
        js_bigint_with("FromStringAs", 4, Boundary { int32_parameters: &[2], ..maybe(0, 1) }),
    ),
    ("JS.BigInt", "fromNumberImpl", js_bigint_with("FromNumber", 3, maybe(0, 1))),
    ("JS.BigInt", "fromInt", js_bigint_with("FromInt", 1, int32_parameters(&[0]))),
    ("JS.BigInt", "fromTypeLevelInt", js_bigint("FromTypeLevelInt", 1)),
    ("JS.BigInt", "toNumber", js_bigint("ToNumber", 1)),
    ("JS.BigInt", "biAdd", js_bigint("Add", 2)),
    ("JS.BigInt", "biMul", js_bigint("Mul", 2)),
    ("JS.BigInt", "biSub", js_bigint("Sub", 2)),
    ("JS.BigInt", "biMod", js_bigint("Mod", 2)),
    ("JS.BigInt", "biDiv", js_bigint("Div", 2)),
    ("JS.BigInt", "biDegree", js_bigint("Degree", 1)),
    ("JS.BigInt", "biZero", js_bigint_constant("Zero")),
    ("JS.BigInt", "biOne", js_bigint_constant("One")),
    ("JS.BigInt", "pow", js_bigint("Pow", 2)),
    ("JS.BigInt", "not", js_bigint("Not", 1)),
    ("JS.BigInt", "or", js_bigint("Or", 2)),
    ("JS.BigInt", "xor", js_bigint("Xor", 2)),
    ("JS.BigInt", "and", js_bigint("And", 2)),
    ("JS.BigInt", "shl", js_bigint("Shl", 2)),
    ("JS.BigInt", "shr", js_bigint("Shr", 2)),
    ("JS.BigInt", "biEquals", js_bigint("Equals", 2)),
    ("JS.BigInt", "biCompare", js_bigint("Compare", 2)),
    ("JS.BigInt", "toString", js_bigint("ToString", 1)),
    ("JS.BigInt", "toStringAs", js_bigint_with("ToStringAs", 2, int32_parameters(&[0]))),
    ("JS.BigInt", "asIntN", js_bigint_with("AsIntN", 2, int32_parameters(&[0]))),
    ("JS.BigInt", "asUintN", js_bigint_with("AsUintN", 2, int32_parameters(&[0]))),
    ("Data.BigInt", "fromTypeLevelInt", call(GoPackage::BigInts, "FromTypeLevelInt", 1, PLAIN)),
    (
        "Data.BigInt",
        "fromBaseImpl",
        call(
            GoPackage::BigInts,
            "FromBaseImpl",
            4,
            Boundary { int32_parameters: &[2], ..maybe(0, 1) },
        ),
    ),
    ("Data.BigInt", "fromInt", call(GoPackage::BigInts, "FromInt", 1, int32_parameters(&[0]))),
    ("Data.BigInt", "fromNumberImpl", call(GoPackage::BigInts, "FromNumberImpl", 3, maybe(0, 1))),
    ("Data.BigInt", "toNumber", call(GoPackage::BigInts, "ToNumber", 1, PLAIN)),
    ("Data.BigInt", "pow", call(GoPackage::BigInts, "Pow", 2, PLAIN)),
    ("Data.BigInt", "abs", call(GoPackage::BigInts, "Abs", 1, PLAIN)),
    ("Data.BigInt", "even", call(GoPackage::BigInts, "Even", 1, PLAIN)),
    ("Data.BigInt", "odd", call(GoPackage::BigInts, "Odd", 1, PLAIN)),
    ("Data.BigInt", "prime", call(GoPackage::BigInts, "Prime", 1, PLAIN)),
    ("Data.BigInt", "not", call(GoPackage::BigInts, "Not", 1, PLAIN)),
    ("Data.BigInt", "or", call(GoPackage::BigInts, "Or", 2, PLAIN)),
    ("Data.BigInt", "xor", call(GoPackage::BigInts, "Xor", 2, PLAIN)),
    ("Data.BigInt", "and", call(GoPackage::BigInts, "And", 2, PLAIN)),
    ("Data.BigInt", "shl", call(GoPackage::BigInts, "Shl", 2, PLAIN)),
    ("Data.BigInt", "shr", call(GoPackage::BigInts, "Shr", 2, PLAIN)),
    ("Data.BigInt", "biEquals", call(GoPackage::BigInts, "BiEquals", 2, PLAIN)),
    ("Data.BigInt", "biCompare", call(GoPackage::BigInts, "BiCompare", 2, PLAIN)),
    (
        "Data.BigInt",
        "digitsInBase",
        call(GoPackage::BigInts, "DigitsInBase", 2, Boundary { int32_parameters: &[0], ..RECORD }),
    ),
    ("Data.BigInt", "toBase", call(GoPackage::BigInts, "ToBase", 2, int32_parameters(&[0]))),
    ("Data.BigInt", "biAdd", call(GoPackage::BigInts, "BiAdd", 2, PLAIN)),
    ("Data.BigInt", "biMul", call(GoPackage::BigInts, "BiMul", 2, PLAIN)),
    ("Data.BigInt", "biSub", call(GoPackage::BigInts, "BiSub", 2, PLAIN)),
    ("Data.BigInt", "biDiv", call(GoPackage::BigInts, "BiDiv", 2, PLAIN)),
    ("Data.BigInt", "biMod", call(GoPackage::BigInts, "BiMod", 2, PLAIN)),
    ("Effect.Now", "now", perform_in(GoPackage::Now, "Now", 0, PLAIN)),
    ("Effect.Now", "getTimezoneOffset", perform_in(GoPackage::Now, "GetTimezoneOffset", 0, PLAIN)),
    (
        "Data.Date",
        "canonicalDateImpl",
        uncurried(
            call(GoPackage::DateTime, "CanonicalDateImpl", 4, int32_parameters(&[1, 2, 3])),
            &[(0, 3)],
        ),
    ),
    (
        "Data.Date",
        "calcWeekday",
        call(GoPackage::DateTime, "CalcWeekday", 3, int32_parameters(&[0, 1, 2])),
    ),
    (
        "Data.Date",
        "calcDiff",
        call(GoPackage::DateTime, "CalcDiff", 6, int32_parameters(&[0, 1, 2, 3, 4, 5])),
    ),
    (
        "Data.DateTime",
        "calcDiff",
        call(
            GoPackage::DateTime,
            "CalcDiffDateTime",
            2,
            Boundary { record_arguments: &[0, 1], ..PLAIN },
        ),
    ),
    (
        "Data.DateTime.Instant",
        "fromDateTimeImpl",
        call(GoPackage::DateTime, "FromDateTimeImpl", 7, int32_parameters(&[0, 1, 2, 3, 4, 5, 6])),
    ),
    (
        "Data.DateTime.Instant",
        "toDateTimeImpl",
        uncurried(call(GoPackage::DateTime, "ToDateTimeImpl", 2, PLAIN), &[(0, 7)]),
    ),
    ("Test.Spec.Console", "write", perform_in(GoPackage::Spec, "Write", 1, PLAIN)),
    ("Test.Spec.Runner", "exit", perform_in(GoPackage::Spec, "Exit", 1, int32_parameters(&[0]))),
    ("Test.Spec.Assertions.String", "_startsWith", call(GoPackage::Spec, "StartsWith", 2, PLAIN)),
    ("Test.Spec.Assertions.String", "_endsWith", call(GoPackage::Spec, "EndsWith", 2, PLAIN)),
    ("Effect.Synchronized", "newMutex", Foreign::MutexNew),
    ("Effect.Synchronized", "withMutex", Foreign::WithMutex),
    ("Data.Lazy", "defer", Foreign::LazyDefer),
    ("Data.Lazy", "force", Foreign::LazyForce),
    ("Partial.Unsafe", "_unsafePartial", Foreign::Identity),
    ("Partial", "_crashWith", Foreign::Crash),
    ("Effect.Unsafe", "unsafePerformEffect", Foreign::UnsafePerformEffect),
    ("Unsafe.Coerce", "unsafeCoerce", Foreign::UnsafeCoerce),
    ("Unsafe.Reference", "reallyUnsafeRefEq", Foreign::ReferenceEqual),
    ("Effect", "pureE", Foreign::EffectPure),
    ("Effect", "bindE", Foreign::EffectBind),
    ("Effect", "foreachE", Foreign::EffectForEach),
    ("Effect", "whileE", Foreign::EffectWhile),
    ("Effect", "untilE", Foreign::EffectUntil),
    ("Effect", "forE", Foreign::EffectFor),
    ("Effect.Console", "log", perform_in(GoPackage::Console, "Print", 1, PLAIN)),
    ("Effect.Console", "info", perform_in(GoPackage::Console, "Print", 1, PLAIN)),
    ("Effect.Console", "debug", perform_in(GoPackage::Console, "Print", 1, PLAIN)),
    ("Effect.Console", "warn", perform_in(GoPackage::Console, "PrintError", 1, PLAIN)),
    ("Effect.Console", "error", perform_in(GoPackage::Console, "PrintError", 1, PLAIN)),
    ("Effect.Console", "group", perform_in(GoPackage::Console, "Group", 1, PLAIN)),
    (
        "Effect.Console",
        "groupCollapsed",
        perform_in(GoPackage::Console, "GroupCollapsed", 1, PLAIN),
    ),
    ("Effect.Console", "groupEnd", perform_in(GoPackage::Console, "GroupEnd", 0, PLAIN)),
    ("Effect.Console", "time", perform_in(GoPackage::Console, "Time", 1, PLAIN)),
    ("Effect.Console", "timeLog", perform_in(GoPackage::Console, "TimeLog", 1, PLAIN)),
    ("Effect.Console", "timeEnd", perform_in(GoPackage::Console, "TimeEnd", 1, PLAIN)),
    ("Effect.Console", "clear", perform_in(GoPackage::Console, "Clear", 0, PLAIN)),
    ("Effect.Ref", "_new", Foreign::ReferenceNew),
    ("Effect.Ref", "read", Foreign::ReferenceRead),
    ("Effect.Ref", "write", Foreign::ReferenceWrite),
    ("Effect.Ref", "modifyImpl", Foreign::ReferenceModify),
    ("Control.Monad.ST.Internal", "new", Foreign::ReferenceNew),
    ("Control.Monad.ST.Internal", "read", Foreign::ReferenceRead),
    ("Control.Monad.ST.Internal", "pure_", Foreign::EffectPure),
    ("Control.Monad.ST.Internal", "bind_", Foreign::EffectBind),
    ("Control.Monad.ST.Internal", "foreach", Foreign::EffectForEach),
    ("Control.Monad.ST.Internal", "map_", Foreign::EffectMap),
    ("Control.Monad.ST.Internal", "while", Foreign::EffectWhile),
    ("Control.Monad.ST.Internal", "for", Foreign::EffectFor),
    ("Control.Monad.ST.Internal", "write", Foreign::ReferenceWriteThrough),
    ("Control.Monad.ST.Internal", "modifyImpl", Foreign::ReferenceModify),
    ("Control.Monad.ST.Internal", "run", Foreign::RunEffect),
];

/// Library functions replaced wholesale, keyed by the instance of their first
/// dictionary when they are overloaded.
pub(super) const INTRINSICS: &[(&str, &str, &[&str], Foreign)] = &[
    ("Data.Array", "snoc", &[], Foreign::Snoc),
    ("Data.Array", "nub", &["ordInt"], array("NubComparable", 1)),
    ("Data.Array", "nub", &["ordChar"], array("NubComparable", 1)),
    ("Data.Array", "nub", &["ordString"], array("NubComparable", 1)),
    ("Data.Array", "nub", &["ordBoolean"], array("NubComparable", 1)),
    ("Data.Array", "groupBy", &[], uncurried(array("GroupBy", 2), &[(0, 2)])),
    (
        "Data.Foldable",
        "traverse_",
        &["applicativeEffect", "foldableArray"],
        Foreign::EffectTraverseArray,
    ),
    ("Data.Foldable", "for_", &["applicativeEffect", "foldableArray"], Foreign::EffectForArray),
    (
        "Data.Foldable",
        "traverse_",
        &["applicativeST", "foldableArray"],
        Foreign::EffectTraverseArray,
    ),
    ("Data.Foldable", "for_", &["applicativeST", "foldableArray"], Foreign::EffectForArray),
    (
        "Data.FoldableWithIndex",
        "traverseWithIndex_",
        &["applicativeEffect", "foldableWithIndexArray"],
        Foreign::EffectTraverseArrayWithIndex,
    ),
    (
        "Data.FoldableWithIndex",
        "forWithIndex_",
        &["applicativeEffect", "foldableWithIndexArray"],
        Foreign::EffectForArrayWithIndex,
    ),
    (
        "Data.FoldableWithIndex",
        "traverseWithIndex_",
        &["applicativeST", "foldableWithIndexArray"],
        Foreign::EffectTraverseArrayWithIndex,
    ),
    (
        "Data.FoldableWithIndex",
        "forWithIndex_",
        &["applicativeST", "foldableWithIndexArray"],
        Foreign::EffectForArrayWithIndex,
    ),
    ("Data.Foldable", "foldM", &["foldableArray", "monadEffect"], Foreign::EffectFoldArray),
    ("Data.Foldable", "foldM", &["foldableArray", "monadST"], Foreign::EffectFoldArray),
    ("Data.Array", "foldM", &["monadEffect"], Foreign::EffectFoldArray),
    ("Data.Array", "foldM", &["monadST"], Foreign::EffectFoldArray),
    (
        "Data.Traversable",
        "traverse",
        &["traversableArray", "applicativeEffect"],
        Foreign::EffectTraverseArrayResults,
    ),
    (
        "Data.Traversable",
        "traverse",
        &["traversableArray", "applicativeST"],
        Foreign::EffectTraverseArrayResults,
    ),
    (
        "Data.Traversable",
        "for",
        &["applicativeEffect", "traversableArray"],
        Foreign::EffectForArrayResults,
    ),
    (
        "Data.Traversable",
        "for",
        &["applicativeST", "traversableArray"],
        Foreign::EffectForArrayResults,
    ),
    (
        "Data.Traversable",
        "traverse",
        &["traversableArray", "applicativeParAff"],
        perform_in(GoPackage::Aff, "TraverseParArrayDirect", 2, UNIT_VALUES),
    ),
    (
        "Data.Traversable",
        "sequence",
        &["traversableArray", "applicativeParAff"],
        perform_in(GoPackage::Aff, "SequenceParArrayDirect", 1, PLAIN),
    ),
    (
        "Data.Traversable",
        "sequence",
        &["traversableArray", "applicativeEffect"],
        perform("SequenceArray", 1),
    ),
    ("Control.Parallel.Class", "parallel", &["parallelAff"], Foreign::Identity),
    ("Control.Parallel.Class", "sequential", &["parallelAff"], Foreign::Identity),
    ("Data.Ord", "lessThan", &["ordInt"], compare(Comparison::LessThan)),
    ("Data.Ord", "lessThanOrEq", &["ordInt"], compare(Comparison::LessThanOrEqual)),
    ("Data.Ord", "greaterThan", &["ordInt"], compare(Comparison::GreaterThan)),
    ("Data.Ord", "greaterThanOrEq", &["ordInt"], compare(Comparison::GreaterThanOrEqual)),
    ("Data.Ord", "lessThan", &["ordNumber"], compare(Comparison::LessThan)),
    ("Data.Ord", "lessThanOrEq", &["ordNumber"], compare(Comparison::LessThanOrEqual)),
    ("Data.Ord", "greaterThan", &["ordNumber"], compare(Comparison::GreaterThanOrUnordered)),
    (
        "Data.Ord",
        "greaterThanOrEq",
        &["ordNumber"],
        compare(Comparison::GreaterThanOrEqualOrUnordered),
    ),
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
    ("Data.Int", "floor", &[], prim("IntFloor", 1)),
    ("Data.Int", "ceil", &[], prim("IntCeil", 1)),
    ("Data.Int", "trunc", &[], prim("IntTrunc", 1)),
    ("Data.Int", "round", &[], prim("IntRound", 1)),
];

/// `foreign import data` types that a go-support package declares, as the
/// package and the name of their Go type.
pub(super) const SUPPORT_DATA: &[(&str, &str, GoPackage, &str)] = &[
    ("Data.Argonaut.Core", "Json", GoPackage::Argonaut, "Json"),
    ("Data.Argonaut.Core", "JNull", GoPackage::Argonaut, "JNull"),
    ("Effect.AVar", "AVar", GoPackage::AVar, "AVar"),
    ("Effect.Aff", "Supervisor", GoPackage::Aff, "Supervisor"),
];
