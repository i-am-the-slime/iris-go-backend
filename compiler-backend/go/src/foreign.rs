//! Go implementations of foreign imports and of library functions whose PureScript
//! definitions have a direct Go equivalent. The runtime functions live in the
//! purs-backend-go `go-support` module.

mod host;

pub use host::is_opaque_foreign_data;

use files::FileId;
use indexing::TermItemId;

#[derive(Debug, Clone, Default)]
pub struct ForeignPackages {
    pub module_path: String,
    pub modules: Vec<String>,
}

impl ForeignPackages {
    pub fn provides(&self, module_name: &str) -> bool {
        self.modules.iter().any(|module| module == module_name)
    }

    pub fn package_name(module_name: &str) -> String {
        format!("{}_ffi", module_name.replace('.', "_"))
    }

    pub fn import_path(&self, module_name: &str) -> String {
        format!("{}/{}", self.module_path, ForeignPackages::package_name(module_name))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Foreign {
    Operator(Operator),
    Project { file_id: FileId, term: TermItemId, arity: usize, effectful: bool },
    Call { function: GoFunction, arity: usize, boundary: Boundary },
    Perform { function: GoFunction, arity: usize, boundary: Boundary },
    RunEffect,
    Constant(GoFunction),
    Unit,
    UnsafeCoerce,
    Identity,
    EffectPure,
    EffectBind,
    EffectMap,
    EffectForEach,
    EffectTraverseArray,
    EffectForArray,
    EffectWhile,
    EffectUntil,
    EffectFor,
    MaybeIndex,
    IntFromNumber,
    Range,
    Snoc,
    Ordering,
    RecordGet,
    RecordHas,
    Record(RecordOperation),
    AssocArray,
    ObjectFoldM,
    Unfoldr,
    Unfoldr1,
    Print,
    ReferenceNew,
    ReferenceRead,
    ReferenceWrite,
    ReferenceWriteThrough,
    ReferenceModify,
    MutableArrayNew,
    Throw,
    Crash,
    MakeAff,
    ForkFiber,
    NewFiber,
    NewSupervisedFiber,
    MutexNew,
    WithMutex,
    LazyDefer,
    LazyForce,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RecordOperation {
    Insert,
    Modify,
    Delete,
    Rename,
    Union,
    /// `Record.Studio.Shrink.shrinkImpl`: the fields of a record that a
    /// smaller record type names. Its keys argument lists exactly those
    /// labels (the `Keys` class reflects them), which the type already fixes.
    Shrink,
}

impl RecordOperation {
    pub fn arity(self) -> usize {
        match self {
            RecordOperation::Insert | RecordOperation::Modify | RecordOperation::Rename => 3,
            RecordOperation::Delete | RecordOperation::Union | RecordOperation::Shrink => 2,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Boundary {
    /// The Int arguments the Go helper declares as `int32` rather than as a
    /// type parameter, where an Int literal needs no conversion.
    pub int32_parameters: &'static [usize],
    pub ignored: &'static [usize],
    pub maybe: Option<MaybeConstructors>,
    pub thunk: bool,
    pub record_result: bool,
    pub instantiate: bool,
    pub unit_values: bool,
    pub record_arguments: &'static [usize],
    pub maybe_destructor: Option<MaybeDestructor>,
    /// For each parameter, the arrows its declared PureScript type spells out
    /// (zero for non-functions). Filled in from the declaration when the
    /// foreign is referenced; generic helpers see an effect after exactly that
    /// many applications as a value, where direct style would perform it.
    pub callback_arities: &'static [usize],
    /// A `Maybe b -> Boolean` argument rebuilt as a tag test on the result's Maybe.
    pub is_just: Option<usize>,
    pub iteration: Option<Iteration>,
    pub uncurried: &'static [(usize, usize)],
    pub uncurried_perform: bool,
    pub signature: Option<&'static Signature>,
    pub utility: Option<Utility>,
    /// The Go helper's one type parameter is its result type, which its
    /// arguments do not determine.
    pub result_parameter: bool,
}

/// A record of polymorphic constructors that JavaScript passes a foreign (the
/// `FFIUtil` of `Effect.AVar`, say). Go cannot pass polymorphic values, so the
/// foreign receives, in place of the record, the constructors it uses at the
/// types its own signature fixes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Utility {
    pub position: usize,
    pub constructors: &'static [Constructed],
}

/// A constructor of the data type at one place of a foreign's signature: a
/// function of its field, or the value of a nullary constructor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Constructed {
    /// Of the foreign's result, inside its effect.
    Result(&'static str),
    /// Of the parameter of the callback at a position.
    CallbackParameter(usize, &'static str),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Signature {
    pub parameters: Vec<Spelled>,
    pub result: Spelled,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Spelled {
    Opaque,
    Function(Box<Spelled>, Box<Spelled>),
    Array(Box<Spelled>),
    Effect(Box<Spelled>),
}

impl Spelled {
    pub fn arrows(&self) -> usize {
        match self {
            Spelled::Function(_, result) => 1 + result.arrows(),
            _ => 0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Iteration {
    FoldLeft,
    FoldRight,
    Map,
    MapWithIndex,
    Filter,
    Any,
    All,
    Bind,
    FindIndex,
    FindLastIndex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MaybeConstructors {
    pub just: usize,
    pub nothing: usize,
    pub witness: Option<usize>,
    /// The foreign uses `just` and `nothing` at two types: the Maybe its result
    /// holds an array of, and the result's Maybe. Each is passed twice, in
    /// that order.
    pub elements: bool,
}

const PLAIN: Boundary = Boundary {
    int32_parameters: &[],
    ignored: &[],
    maybe: None,
    thunk: false,
    record_result: false,
    instantiate: false,
    unit_values: false,
    record_arguments: &[],
    maybe_destructor: None,
    is_just: None,
    callback_arities: &[],
    iteration: None,
    uncurried: &[],
    uncurried_perform: false,
    signature: None,
    utility: None,
    result_parameter: false,
};

const RESULT_PARAMETER: Boundary = Boundary { result_parameter: true, ..PLAIN };

const fn int32_parameters(positions: &'static [usize]) -> Boundary {
    Boundary { int32_parameters: positions, ..PLAIN }
}

const fn ignoring(arguments: &'static [usize]) -> Boundary {
    Boundary { ignored: arguments, ..PLAIN }
}

const INSTANTIATE: Boundary = Boundary { instantiate: true, ..PLAIN };

const UNIT_VALUES: Boundary = Boundary { unit_values: true, ..PLAIN };

const RECORD: Boundary = Boundary { record_result: true, ..PLAIN };

const fn maybe(just: usize, nothing: usize) -> Boundary {
    let constructors = MaybeConstructors { just, nothing, witness: None, elements: false };
    Boundary { maybe: Some(constructors), ..PLAIN }
}

const fn maybe_witnessed(just: usize, nothing: usize, witness: usize) -> Boundary {
    let witness = Some(witness);
    let constructors = MaybeConstructors { just, nothing, witness, elements: false };
    Boundary { maybe: Some(constructors), ..PLAIN }
}

/// A search that returns its `nothing` argument or one of the callback's results,
/// whose Maybe is the foreign's result type.
const fn maybe_search(nothing: usize, is_just: usize) -> Boundary {
    let constructors =
        MaybeConstructors { just: usize::MAX, nothing, witness: None, elements: false };
    Boundary { maybe: Some(constructors), is_just: Some(is_just), ..PLAIN }
}

/// Both a Maybe of arrays of Maybes, `Maybe (Array (Maybe a))`, and its elements.
const fn maybe_of_maybes(just: usize, nothing: usize) -> Boundary {
    let constructors = MaybeConstructors { just, nothing, witness: None, elements: true };
    Boundary { maybe: Some(constructors), ..PLAIN }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MaybeDestructor {
    pub position: usize,
    pub witness: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GoFunction {
    pub package: GoPackage,
    pub name: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GoPackage {
    Prim,
    Array,
    Direct,
    Object,
    Nullable,
    Exception,
    Aff,
    Promise,
    ForeignValue,
    Tauri,
    Regex,
    Lazy,
    Alloc,
    Argonaut,
    AVar,
    YogaOm,
    BigInts,
    DateTime,
    Now,
    Spec,
}

impl GoPackage {
    pub fn path(self) -> &'static str {
        match self {
            GoPackage::Prim => "github.com/i-am-the-slime/purs-backend-go/go-support/prim",
            GoPackage::Array => "github.com/i-am-the-slime/purs-backend-go/go-support/array",
            GoPackage::Direct => "github.com/i-am-the-slime/purs-backend-go/go-support/direct",
            GoPackage::Object => "github.com/i-am-the-slime/purs-backend-go/go-support/object",
            GoPackage::Nullable => "github.com/i-am-the-slime/purs-backend-go/go-support/nullable",
            GoPackage::Aff => "github.com/i-am-the-slime/purs-backend-go/go-support/aff",
            GoPackage::Promise => "github.com/i-am-the-slime/purs-backend-go/go-support/promise",
            GoPackage::ForeignValue => {
                "github.com/i-am-the-slime/purs-backend-go/go-support/foreignvalue"
            }
            GoPackage::Tauri => "github.com/i-am-the-slime/purs-backend-go/go-support/tauri",
            GoPackage::Regex => "github.com/i-am-the-slime/purs-backend-go/go-support/regex",
            GoPackage::Lazy => "github.com/i-am-the-slime/purs-backend-go/go-support/lazy",
            GoPackage::Alloc => "github.com/i-am-the-slime/purs-backend-go/go-support/alloc",
            GoPackage::Argonaut => "github.com/i-am-the-slime/purs-backend-go/go-support/argonaut",
            GoPackage::AVar => "github.com/i-am-the-slime/purs-backend-go/go-support/avar",
            GoPackage::YogaOm => "github.com/i-am-the-slime/purs-backend-go/go-support/yogaom",
            GoPackage::BigInts => "github.com/i-am-the-slime/purs-backend-go/go-support/bigints",
            GoPackage::DateTime => "github.com/i-am-the-slime/purs-backend-go/go-support/datetime",
            GoPackage::Now => "github.com/i-am-the-slime/purs-backend-go/go-support/now",
            GoPackage::Spec => "github.com/i-am-the-slime/purs-backend-go/go-support/spec",
            GoPackage::Exception => {
                "github.com/i-am-the-slime/purs-backend-go/go-support/exception"
            }
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            GoPackage::Prim => "prim",
            GoPackage::Array => "array",
            GoPackage::Direct => "direct",
            GoPackage::Object => "object",
            GoPackage::Nullable => "nullable",
            GoPackage::Exception => "exception",
            GoPackage::Aff => "aff",
            GoPackage::Promise => "promise",
            GoPackage::ForeignValue => "foreignvalue",
            GoPackage::Tauri => "tauri",
            GoPackage::Regex => "regex",
            GoPackage::Lazy => "lazy",
            GoPackage::Alloc => "alloc",
            GoPackage::Argonaut => "argonaut",
            GoPackage::AVar => "avar",
            GoPackage::YogaOm => "yogaom",
            GoPackage::BigInts => "bigints",
            GoPackage::DateTime => "datetime",
            GoPackage::Now => "now",
            GoPackage::Spec => "spec",
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
    IntAnd,
    IntOr,
    IntXor,
    IntShiftLeft,
    IntShiftRight,
    IntZeroFillShiftRight,
    IntComplement,
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
            | Operator::IntToNumber
            | Operator::IntComplement => 1,
            _ => 2,
        }
    }
}

impl Foreign {
    /// Whether this calls the same Go function as `other`, whatever the
    /// boundary learned from the declaration that references it.
    pub fn calls(self, other: Foreign) -> bool {
        match (self, other) {
            (Foreign::Call { function, .. }, Foreign::Call { function: other, .. }) => {
                function == other
            }
            _ => false,
        }
    }

    pub fn arity(self) -> usize {
        match self {
            Foreign::Operator(operator) => operator.arity(),
            Foreign::Call { arity, .. }
            | Foreign::Perform { arity, .. }
            | Foreign::Project { arity, .. } => arity,
            Foreign::Constant(_) | Foreign::Unit | Foreign::MutableArrayNew => 0,
            Foreign::MutexNew => 0,
            Foreign::WithMutex => 2,
            Foreign::LazyDefer | Foreign::LazyForce => 1,
            Foreign::UnsafeCoerce | Foreign::Identity | Foreign::EffectPure | Foreign::Print => 1,
            Foreign::Throw | Foreign::Crash | Foreign::MakeAff | Foreign::AssocArray => 1,
            Foreign::ForkFiber | Foreign::NewFiber | Foreign::NewSupervisedFiber => 2,
            Foreign::RunEffect | Foreign::EffectUntil => 1,
            Foreign::ReferenceNew | Foreign::ReferenceRead => 1,
            Foreign::EffectBind | Foreign::EffectMap | Foreign::EffectForEach => 2,
            Foreign::EffectTraverseArray | Foreign::EffectForArray | Foreign::EffectWhile => 2,
            Foreign::EffectFor => 3,
            Foreign::ObjectFoldM => 4,
            Foreign::MaybeIndex => 4,
            Foreign::IntFromNumber => 3,
            Foreign::Ordering => 5,
            Foreign::Range | Foreign::Snoc | Foreign::RecordGet | Foreign::RecordHas => 2,
            Foreign::Record(operation) => operation.arity(),
            Foreign::Unfoldr | Foreign::Unfoldr1 => 6,
            Foreign::ReferenceWrite | Foreign::ReferenceWriteThrough | Foreign::ReferenceModify => {
                2
            }
        }
    }

    pub fn ignored_arguments(self) -> &'static [usize] {
        match self {
            Foreign::Call { boundary, .. } | Foreign::Perform { boundary, .. } => boundary.ignored,
            Foreign::NewFiber | Foreign::NewSupervisedFiber => &[0],
            _ => &[],
        }
    }

    pub fn is_effectful(self) -> bool {
        if let Foreign::Project { effectful, .. } = self {
            return effectful;
        }
        matches!(
            self,
            Foreign::EffectPure
                | Foreign::EffectBind
                | Foreign::EffectMap
                | Foreign::EffectForEach
                | Foreign::EffectTraverseArray
                | Foreign::EffectForArray
                | Foreign::EffectWhile
                | Foreign::EffectUntil
                | Foreign::EffectFor
                | Foreign::Perform { .. }
                | Foreign::Print
                | Foreign::ReferenceNew
                | Foreign::ReferenceRead
                | Foreign::ReferenceWrite
                | Foreign::ReferenceWriteThrough
                | Foreign::ReferenceModify
                | Foreign::MutableArrayNew
                | Foreign::AssocArray
                | Foreign::Throw
                | Foreign::MakeAff
                | Foreign::ForkFiber
                | Foreign::NewFiber
                | Foreign::NewSupervisedFiber
                | Foreign::MutexNew
                | Foreign::WithMutex
        )
    }
}

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
    perform_in(GoPackage::AVar, name, arity, Boundary { utility, ..PLAIN })
}

const AVAR_PUT_CALLBACK: &[Constructed] =
    &[Constructed::CallbackParameter(3, "Left"), Constructed::CallbackParameter(3, "Right")];

const AVAR_CALLBACK: &[Constructed] =
    &[Constructed::CallbackParameter(2, "Left"), Constructed::CallbackParameter(2, "Right")];

const AVAR_MAYBE: &[Constructed] = &[Constructed::Result("Just"), Constructed::Result("Nothing")];

const fn constant(name: &'static str) -> Foreign {
    Foreign::Constant(GoFunction { package: GoPackage::Prim, name })
}

const fn direct_constant(name: &'static str) -> Foreign {
    Foreign::Constant(GoFunction { package: GoPackage::Direct, name })
}

const fn compare(comparison: Comparison) -> Foreign {
    Foreign::Operator(Operator::Compare(comparison))
}

pub const ARRAY_FOLD: Foreign =
    uncurried(iteration(GoPackage::Array, "Foldl", 3, Iteration::FoldLeft), &[(0, 2)]);

pub const EFFECT_FOLD: Foreign = direct_with(
    "FoldlEffect",
    3,
    Boundary { uncurried: &[(0, 2)], uncurried_perform: true, ..PLAIN },
);

pub const OBJECT_KEYS: Foreign = object("Keys", 1, PLAIN);

pub const OBJECT_INDEX: Foreign = object("UnsafeIndex", 2, PLAIN);

pub const OBJECT_FROM_ENTRIES: Foreign = object("FromEntries", 2, PLAIN);

pub const ARRAY_SLICE: Foreign = array_with("Slice", 3, int32_parameters(&[0, 1]));

pub const FOREIGN_RECORD: Foreign = direct("ForeignRecord", 2);

pub const INT_DIVIDE: Foreign = prim_with("IntDiv", 2, int32_parameters(&[0, 1]));

pub const INT_MODULO: Foreign = prim_with("IntMod", 2, int32_parameters(&[0, 1]));

pub const ARRAY_APPEND: Foreign = array("Append", 2);
pub const APPENDER: Foreign = perform_in(GoPackage::Direct, "Appender", 0, INSTANTIATE);

const FOREIGN_IMPORTS: &[(&str, &str, Foreign)] = &[
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
    ("Data.Array", "replicateImpl", array_with("Replicate", 2, int32_parameters(&[0]))),
    ("Data.Array", "zipWithImpl", uncurried(array("ZipWith", 3), &[(0, 2)])),
    ("Data.Array", "anyImpl", iteration(GoPackage::Array, "Any", 2, Iteration::Any)),
    ("Data.Array", "partitionImpl", direct_with("Partition", 2, RECORD)),
    ("Data.Array", "fromFoldableImpl", direct("FromFoldable", 2)),
    ("Data.Array", "allImpl", iteration(GoPackage::Direct, "All", 2, Iteration::All)),
    ("Data.Array", "scanlImpl", uncurried(array("Scanl", 3), &[(0, 2)])),
    ("Data.Array", "scanrImpl", uncurried(array("Scanr", 3), &[(0, 2)])),
    ("Data.Array", "unconsImpl", uncurried(direct("Uncons", 3), &[(1, 2)])),
    ("Data.Array", "sortByImpl", uncurried(direct("SortBy", 3), &[(0, 2)])),
    ("Data.Array", "findMapImpl", direct_with("FindMap", 4, maybe_search(0, 1))),
    ("Data.Array.Parallel", "parallelMap", array("Map", 2)),
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
    (
        "Data.Array.ST.Partial",
        "peekImpl",
        thunk(GoPackage::Array, "PeekUnsafe", 2, int32_parameters(&[0])),
    ),
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
    ("Foreign.Index", "unsafeReadPropImpl", foreign_value("UnsafeReadPropImpl", 4)),
    ("Foreign.Index", "unsafeHasOwnProperty", foreign_value("UnsafeHasOwnProperty", 2)),
    ("Foreign.Index", "unsafeHasProperty", foreign_value("UnsafeHasProperty", 2)),
    (
        "Yoga.JSON",
        "_undefined",
        Foreign::Constant(GoFunction { package: GoPackage::ForeignValue, name: "Undefined" }),
    ),
    ("Yoga.JSON", "_unsafeStringify", foreign_value("UnsafeStringify", 1)),
    (
        "Yoga.JSON",
        "_unsafePrettyStringify",
        call(GoPackage::ForeignValue, "UnsafePrettyStringify", 2, int32_parameters(&[0])),
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
    ("Data.String.CodeUnits", "fromCharArray", prim("CharArrayToString", 1)),
    ("Data.String.CodeUnits", "toCharArray", prim("StringToCharArray", 1)),
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
    ("JS.BigInt", "fromStringImpl", direct_with("BigIntFromString", 3, maybe(0, 1))),
    (
        "JS.BigInt",
        "fromStringAsImpl",
        direct_with("BigIntFromStringAs", 4, Boundary { int32_parameters: &[2], ..maybe(0, 1) }),
    ),
    ("JS.BigInt", "fromNumberImpl", direct_with("BigIntFromNumber", 3, maybe(0, 1))),
    ("JS.BigInt", "fromInt", direct_with("BigIntFromInt", 1, int32_parameters(&[0]))),
    ("JS.BigInt", "fromTypeLevelInt", direct("BigIntFromTypeLevelInt", 1)),
    ("JS.BigInt", "toNumber", direct("BigIntToNumber", 1)),
    ("JS.BigInt", "biAdd", direct("BigIntAdd", 2)),
    ("JS.BigInt", "biMul", direct("BigIntMul", 2)),
    ("JS.BigInt", "biSub", direct("BigIntSub", 2)),
    ("JS.BigInt", "biMod", direct("BigIntMod", 2)),
    ("JS.BigInt", "biDiv", direct("BigIntDiv", 2)),
    ("JS.BigInt", "biDegree", direct("BigIntDegree", 1)),
    ("JS.BigInt", "biZero", direct_constant("BigIntZero")),
    ("JS.BigInt", "biOne", direct_constant("BigIntOne")),
    ("JS.BigInt", "pow", direct("BigIntPow", 2)),
    ("JS.BigInt", "not", direct("BigIntNot", 1)),
    ("JS.BigInt", "or", direct("BigIntOr", 2)),
    ("JS.BigInt", "xor", direct("BigIntXor", 2)),
    ("JS.BigInt", "and", direct("BigIntAnd", 2)),
    ("JS.BigInt", "shl", direct("BigIntShl", 2)),
    ("JS.BigInt", "shr", direct("BigIntShr", 2)),
    ("JS.BigInt", "biEquals", direct("BigIntEquals", 2)),
    ("JS.BigInt", "biCompare", direct("BigIntCompare", 2)),
    ("JS.BigInt", "toString", direct("BigIntToString", 1)),
    ("JS.BigInt", "toStringAs", direct_with("BigIntToStringAs", 2, int32_parameters(&[0]))),
    ("JS.BigInt", "asIntN", direct_with("BigIntAsIntN", 2, int32_parameters(&[0]))),
    ("JS.BigInt", "asUintN", direct_with("BigIntAsUintN", 2, int32_parameters(&[0]))),
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
    ("Effect.Unsafe", "unsafePerformEffect", Foreign::RunEffect),
    ("Unsafe.Coerce", "unsafeCoerce", Foreign::UnsafeCoerce),
    ("Effect", "pureE", Foreign::EffectPure),
    ("Effect", "bindE", Foreign::EffectBind),
    ("Effect", "foreachE", Foreign::EffectForEach),
    ("Effect", "whileE", Foreign::EffectWhile),
    ("Effect", "untilE", Foreign::EffectUntil),
    ("Effect", "forE", Foreign::EffectFor),
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
    ("Control.Monad.ST.Internal", "map_", Foreign::EffectMap),
    ("Control.Monad.ST.Internal", "while", Foreign::EffectWhile),
    ("Control.Monad.ST.Internal", "for", Foreign::EffectFor),
    ("Control.Monad.ST.Internal", "write", Foreign::ReferenceWriteThrough),
    ("Control.Monad.ST.Internal", "modifyImpl", Foreign::ReferenceModify),
    ("Control.Monad.ST.Internal", "run", Foreign::RunEffect),
];

/// Library functions replaced wholesale, keyed by the instance of their first
/// dictionary when they are overloaded.
const INTRINSICS: &[(&str, &str, &[&str], Foreign)] = &[
    ("Data.Array", "snoc", &[], Foreign::Snoc),
    (
        "Data.Foldable",
        "traverse_",
        &["applicativeEffect", "foldableArray"],
        Foreign::EffectTraverseArray,
    ),
    ("Data.Foldable", "for_", &["applicativeEffect", "foldableArray"], Foreign::EffectForArray),
    (
        "Data.Traversable",
        "traverse",
        &["traversableArray", "applicativeEffect"],
        perform("TraverseArray", 2),
    ),
    ("Data.Traversable", "for", &["applicativeEffect", "traversableArray"], perform("ForArray", 2)),
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

/// `foreign import data` types that a go-support package declares, as the
/// package and the name of their Go type.
const SUPPORT_DATA: &[(&str, &str, GoPackage, &str)] = &[
    ("Data.Argonaut.Core", "Json", GoPackage::Argonaut, "Json"),
    ("Data.Argonaut.Core", "JNull", GoPackage::Argonaut, "JNull"),
    ("Effect.AVar", "AVar", GoPackage::AVar, "AVar"),
    ("Effect.Aff", "Supervisor", GoPackage::Aff, "Supervisor"),
];

pub fn support_data(module_name: &str, name: &str) -> Option<(GoPackage, &'static str)> {
    SUPPORT_DATA
        .iter()
        .find(|(module, item, _, _)| *module == module_name && *item == name)
        .map(|(_, _, package, type_name)| (*package, *type_name))
}

pub fn foreign_import(module_name: &str, name: &str) -> Option<Foreign> {
    if let Some(identity) = uncurried_conversion(module_name, name) {
        return Some(identity);
    }
    FOREIGN_IMPORTS
        .iter()
        .chain(host::HOST_IMPORTS)
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
    let (run, make) = match module_name {
        "Data.Function.Uncurried" => ("runFn", "mkFn"),
        "Effect.Uncurried" => ("runEffectFn", "mkEffectFn"),
        "Control.Monad.ST.Uncurried" => ("runSTFn", "mkSTFn"),
        _ => return None,
    };
    let arity = name.strip_prefix(run).or_else(|| name.strip_prefix(make))?;
    arity.parse::<u8>().is_ok().then_some(Foreign::Identity)
}
