//! Go implementations of foreign imports and of library functions whose PureScript
//! definitions have a direct Go equivalent. The runtime functions live in the
//! iris-go runtime module.

mod embeds;
mod host;
mod imports;
mod opacity;
mod packages;
mod sources;

pub use embeds::{EmbedError, embedded_files};
pub use host::is_opaque_foreign_data;
pub use imports::{
    APPENDER, ARRAY_ALL, ARRAY_ANY, ARRAY_APPEND, ARRAY_FROM_LIST, ARRAY_MAP_WITH_INDEX,
    ARRAY_REPLICATE, ARRAY_SCANL, ARRAY_SLICE, ARRAY_SORT_BY, ARRAY_TAIL, ARRAY_THAW,
    ARRAY_THAW_OWNED, ARRAY_UNCONS, ARRAY_UNZIP, FOREIGN_RECORD, FROM_CHAR_ARRAY, INT_DIVIDE,
    INT_MODULO, MUTABLE_PEEK_UNSAFE, MUTABLE_WITHIN, OBJECT_DELETE, OBJECT_FROM_ENTRIES,
    OBJECT_INDEX, OBJECT_INSERT, OBJECT_KEYS, OBJECT_LOOKUP, OBJECT_SIZE, SEQUENCE_ARRAY,
    TO_CHAR_ARRAY, WELL_FORMED_STRING, array_fold, effect_fold,
};
pub use opacity::{Opacity, OpaqueDeclaration, foreign_opacity};
pub use packages::{ForeignPackages, ForeignSource, LineCoverage, LineDirectives};
pub use sources::{
    foreign_declarations, foreign_files, foreign_source, foreign_structs, recovers, uses_event_loop,
};

use std::sync::{Mutex, OnceLock};

use files::FileId;
use imports::{FOREIGN_IMPORTS, INTRINSICS, SUPPORT_DATA};
use indexing::TermItemId;
use rustc_hash::FxHashMap;

use crate::monotype::MonotypeId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Foreign {
    Operator(Operator),
    /// A `Data.Int64.Internal` operation on Longs of one signedness, which
    /// Go's `int64` or `uint64` does itself.
    Int64 {
        operation: crate::primitives::Int64Operation,
        signedness: crate::primitives::Signedness,
    },
    /// A foreign of a Go foreign package; `type_arguments` instantiate a
    /// quantified one without arguments, a generic Go function.
    Project {
        file_id: FileId,
        term: TermItemId,
        arity: usize,
        effectful: bool,
        type_arguments: &'static [MonotypeId],
    },
    Call {
        function: GoFunction,
        arity: usize,
        boundary: Boundary,
    },
    Perform {
        function: GoFunction,
        arity: usize,
        boundary: Boundary,
    },
    RunEffect,
    UnsafePerformEffect,
    Constant(GoFunction),
    Unit,
    UnsafeCoerce,
    /// `Unsafe.Reference.reallyUnsafeRefEq`, decided per instantiation from
    /// the Go type both arguments share.
    ReferenceEqual,
    Identity,
    EffectPure,
    EffectBind,
    EffectMap,
    EffectForEach,
    EffectTraverseArray,
    EffectForArray,
    EffectTraverseArrayWithIndex,
    EffectForArrayWithIndex,
    EffectTraverseArrayResults,
    EffectForArrayResults,
    EffectFoldArray,
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
    /// Yoga.JSON's readJSON or writeJSON at a type whose codec is Yoga.JSON's
    /// own instances throughout: [`JsonCodec`].
    Json(JsonCodec),
    /// `show` of the `NonEmptyList ForeignError` a Yoga.JSON read fails with. It takes the
    /// `show` of one ForeignError and the errors, and shows them with go-support's
    /// `foreignvalue.ShowErrors`.
    ShowForeignErrors,
}

/// A typed Yoga.JSON codec, which reads the text straight into the program's
/// values or writes them straight out. A read takes Yoga.JSON's own reading
/// of the text and the text; it evaluates the first only when the text does
/// not decode, so that the errors are Yoga.JSON's own.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum JsonCodec {
    Read,
    Write,
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
    pub accumulator: Option<Accumulator>,
    /// The parameters the Go helper takes as `func() T` and calls only on the path that uses
    /// them, such as the failure value of a property read: a pure argument is built there and
    /// not on every call.
    pub lazy: &'static [usize],
    /// The foreign is a three-way comparison of its two arguments: an Int that is -1, 0 or 1 as
    /// the first is less than, equal to or greater than the second, in the order Go's operators
    /// give the arguments' Go type. Where that order is also PureScript's, a test of the result
    /// is a comparison of the arguments themselves.
    pub three_way: bool,
    /// The arguments the Go helper takes as a `Foreign`, an `any` in Foreign's representation,
    /// whatever their PureScript type: `JSON.stringify` of an `Array (Array String)` reads it
    /// as nested `[]any`.
    pub foreign_arguments: &'static [usize],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Accumulator {
    pub parameter: usize,
    pub element: usize,
}

/// A record of polymorphic constructors that JavaScript passes a foreign (the
/// `FFIUtil` of `Effect.AVar`, say). Go cannot pass polymorphic values, so the
/// foreign receives, in place of the record, the constructors it uses at the
/// types its own signature fixes. The record's position is also ignored, so
/// the record itself is never built.
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
    /// `Int`, `Number` or `Char`, which a Go helper takes at its own Go type rather than as a
    /// type parameter, so that a constant argument needs no conversion.
    Scalar,
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
    ZipWith,
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
    accumulator: None,
    lazy: &[],
    three_way: false,
    foreign_arguments: &[],
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

const CONS_LIST_ACCUMULATOR: Boundary =
    Boundary { accumulator: Some(Accumulator { parameter: 0, element: 1 }), ..PLAIN };

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
    EventLoop,
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
    RefEq,
    Console,
    JsBigInt,
    Int64,
}

impl GoPackage {
    pub fn path(self) -> &'static str {
        match self {
            GoPackage::Prim => "github.com/i-am-the-slime/iris-go/prim",
            GoPackage::Array => "github.com/i-am-the-slime/iris-go/array",
            GoPackage::Direct => "github.com/i-am-the-slime/iris-go/direct",
            GoPackage::Object => "github.com/i-am-the-slime/iris-go/object",
            GoPackage::Nullable => "github.com/i-am-the-slime/iris-go/nullable",
            GoPackage::Aff => "github.com/i-am-the-slime/iris-go/aff",
            GoPackage::EventLoop => "github.com/i-am-the-slime/iris-go/eventloop",
            GoPackage::Promise => "github.com/i-am-the-slime/iris-go/promise",
            GoPackage::ForeignValue => "github.com/i-am-the-slime/iris-go/foreignvalue",
            GoPackage::Tauri => "github.com/i-am-the-slime/iris-go/tauri",
            GoPackage::Regex => "github.com/i-am-the-slime/iris-go/regex",
            GoPackage::Lazy => "github.com/i-am-the-slime/iris-go/lazy",
            GoPackage::Alloc => "github.com/i-am-the-slime/iris-go/alloc",
            GoPackage::Argonaut => "github.com/i-am-the-slime/iris-go/argonaut",
            GoPackage::AVar => "github.com/i-am-the-slime/iris-go/avar",
            GoPackage::YogaOm => "github.com/i-am-the-slime/iris-go/yogaom",
            GoPackage::BigInts => "github.com/i-am-the-slime/iris-go/bigints",
            GoPackage::DateTime => "github.com/i-am-the-slime/iris-go/datetime",
            GoPackage::Now => "github.com/i-am-the-slime/iris-go/now",
            GoPackage::Spec => "github.com/i-am-the-slime/iris-go/spec",
            GoPackage::RefEq => "github.com/i-am-the-slime/iris-go/refeq",
            GoPackage::Console => "github.com/i-am-the-slime/iris-go/console",
            GoPackage::JsBigInt => "github.com/i-am-the-slime/iris-go/jsbigint",
            GoPackage::Int64 => "github.com/i-am-the-slime/iris-go/ffi/Data_Int64_Internal_ffi",
            GoPackage::Exception => "github.com/i-am-the-slime/iris-go/exception",
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
            GoPackage::EventLoop => "eventloop",
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
            GoPackage::RefEq => "refeq",
            GoPackage::Console => "console",
            GoPackage::JsBigInt => "jsbigint",
            GoPackage::Int64 => "Data_Int64_Internal_ffi",
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
    GreaterThanOrUnordered,
    GreaterThanOrEqualOrUnordered,
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
    /// The one static copy of this description, which expressions refer to:
    /// a boundary learned from a declaration is interned like the tables'.
    pub fn interned(self) -> &'static Foreign {
        static INTERNED: OnceLock<Mutex<FxHashMap<Foreign, &'static Foreign>>> = OnceLock::new();
        let interned = INTERNED.get_or_init(Mutex::default);
        let mut interned = interned.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        interned.entry(self).or_insert_with(|| Box::leak(Box::new(self)))
    }

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
            Foreign::Int64 { operation, .. } => operation.arity(),
            Foreign::Call { arity, .. }
            | Foreign::Perform { arity, .. }
            | Foreign::Project { arity, .. } => arity,
            Foreign::Constant(_) | Foreign::Unit | Foreign::MutableArrayNew => 0,
            Foreign::MutexNew => 0,
            Foreign::WithMutex | Foreign::ReferenceEqual => 2,
            Foreign::LazyDefer | Foreign::LazyForce => 1,
            Foreign::Json(JsonCodec::Read) => 2,
            Foreign::Json(JsonCodec::Write) => 1,
            Foreign::ShowForeignErrors => 2,
            Foreign::UnsafeCoerce | Foreign::Identity | Foreign::EffectPure => 1,
            Foreign::Throw | Foreign::Crash | Foreign::MakeAff | Foreign::AssocArray => 1,
            Foreign::ForkFiber | Foreign::NewFiber | Foreign::NewSupervisedFiber => 2,
            Foreign::RunEffect | Foreign::UnsafePerformEffect | Foreign::EffectUntil => 1,
            Foreign::ReferenceNew | Foreign::ReferenceRead => 1,
            Foreign::EffectBind | Foreign::EffectMap | Foreign::EffectForEach => 2,
            Foreign::EffectTraverseArray | Foreign::EffectForArray | Foreign::EffectWhile => 2,
            Foreign::EffectTraverseArrayWithIndex | Foreign::EffectForArrayWithIndex => 2,
            Foreign::EffectTraverseArrayResults | Foreign::EffectForArrayResults => 2,
            Foreign::EffectFor | Foreign::EffectFoldArray => 3,
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
                | Foreign::EffectTraverseArrayWithIndex
                | Foreign::EffectForArrayWithIndex
                | Foreign::EffectTraverseArrayResults
                | Foreign::EffectForArrayResults
                | Foreign::EffectFoldArray
                | Foreign::EffectWhile
                | Foreign::EffectUntil
                | Foreign::EffectFor
                | Foreign::Perform { .. }
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

pub fn support_data(module_name: &str, name: &str) -> Option<(GoPackage, &'static str)> {
    SUPPORT_DATA
        .iter()
        .find(|(module, item, _, _)| *module == module_name && *item == name)
        .map(|(_, _, package, type_name)| (*package, *type_name))
}

/// A `Data.Int64.Internal` foreign over `Long` at the signedness of the
/// definition that uses it.
pub fn int64_import(
    module_name: &str,
    name: &str,
    signedness: crate::primitives::Signedness,
) -> Option<&'static Foreign> {
    use crate::primitives::{Int64Foreign, Signedness};
    let foreign = match crate::primitives::int64_foreign(module_name, name)? {
        Int64Foreign::Inline(operation) => Foreign::Int64 { operation, signedness },
        Int64Foreign::Runtime {
            signed,
            unsigned,
            arity,
            effectful,
            int32_arguments,
            three_way,
        } => {
            let name = match signedness {
                Signedness::Signed => signed,
                Signedness::Unsigned => unsigned,
            };
            let function = GoFunction { package: GoPackage::Int64, name };
            let boundary = Boundary { three_way, ..int32_parameters(int32_arguments) };
            match effectful {
                true => Foreign::Perform { function, arity, boundary },
                false => Foreign::Call { function, arity, boundary },
            }
        }
    };
    Some(foreign.interned())
}

pub fn foreign_import(module_name: &str, name: &str) -> Option<&'static Foreign> {
    if let Some(identity) = uncurried_conversion(module_name, name) {
        return Some(identity);
    }
    FOREIGN_IMPORTS
        .iter()
        .chain(host::HOST_IMPORTS)
        .find(|(module, item, _)| *module == module_name && *item == name)
        .map(|(_, _, foreign)| foreign)
}

pub fn intrinsic(module_name: &str, name: &str, instances: &[&str]) -> Option<&'static Foreign> {
    if let Some(identity) = uncurried_conversion(module_name, name) {
        return Some(identity);
    }
    INTRINSICS
        .iter()
        .find(|(module, item, expected, _)| {
            *module == module_name && *item == name && instances.starts_with(expected)
        })
        .map(|(_, _, _, foreign)| foreign)
}

/// `FnN` types are curried functions in Go, so converting to and from them is free.
fn uncurried_conversion(module_name: &str, name: &str) -> Option<&'static Foreign> {
    let (run, make) = match module_name {
        "Data.Function.Uncurried" => ("runFn", "mkFn"),
        "Effect.Uncurried" => ("runEffectFn", "mkEffectFn"),
        "Control.Monad.ST.Uncurried" => ("runSTFn", "mkSTFn"),
        _ => return None,
    };
    let arity = name.strip_prefix(run).or_else(|| name.strip_prefix(make))?;
    arity.parse::<u8>().is_ok().then_some(&Foreign::Identity)
}
