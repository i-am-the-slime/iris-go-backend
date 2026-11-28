use std::sync::Arc;

use building_types::{QueryError, QueryResult};
use checking::TypeId;
use files::FileId;
use indexing::{TermItemId, TypeItemId};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::erasure::Erasure;
use crate::error::{GoError, UnsupportedState};
use crate::scheme::{Read, SchemeInstantiations};

pub use self::hash_map::native_hash_map;
pub use self::longs::{LongMentions, long_mentions, spell_longs};
pub use self::types::{data_argument, expand_synonyms, is_partial, newtype_unwrapped};

mod convert;
mod data;
mod hash_map;
mod longs;
mod types;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MonotypeId(u32);

#[cfg(test)]
impl MonotypeId {
    /// A type for expressions in unit tests, which do not look types up.
    pub(crate) fn for_tests() -> MonotypeId {
        MonotypeId(0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Monotype {
    Int,
    Number,
    Boolean,
    Char,
    String,
    Unit,
    Array(MonotypeId),
    Record(Arc<[RecordField]>),
    Function(MonotypeId, MonotypeId),
    Effect(MonotypeId),
    Reference(MonotypeId),
    MutableArray(MonotypeId),
    Object(MonotypeId),
    Nullable(MonotypeId),
    Error,
    Opaque,
    Regex,
    Mutex,
    BigInt,
    /// purescript-int64's `Long' Signed`, the `Int64` newtype's Go `int64`.
    Int64,
    /// `Long' Unsigned`, `UInt64`'s Go `uint64`.
    UInt64,
    Lazy(MonotypeId),
    ConsList(MonotypeId),
    Data(DataType),
    /// A `foreign import data` type that a go-support package or the
    /// project's Go foreign package for its module declares, as a named Go type.
    ForeignData(DataType),
    Recursive(DataType),
    Erased(Erasure),
    /// A `Data.Map` of a key and a value that the program owns along its whole life and uses
    /// only by key, as a Go `map[K]V` ([`crate::maps`]).
    HashMap(MonotypeId, MonotypeId),
    /// A `Data.Map` that the program owns along its whole life and also asks for its order, as a
    /// B-tree it changes in place, of the key and the value ([`crate::maps`]).
    OrderedMap(MonotypeId, MonotypeId),
}

impl Monotype {
    /// The one type a container holds: an array's element, an effect's result.
    pub fn element(&self) -> Option<MonotypeId> {
        match self {
            Monotype::Array(element)
            | Monotype::Effect(element)
            | Monotype::Reference(element)
            | Monotype::MutableArray(element)
            | Monotype::Object(element)
            | Monotype::Nullable(element)
            | Monotype::Lazy(element)
            | Monotype::ConsList(element) => Some(*element),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordField {
    pub label: SmolStr,
    pub monotype: MonotypeId,
}

/// What stops a type from converting: the checker's queries failing, or a type the backend
/// cannot compile.
#[derive(Debug)]
pub enum Failure {
    Query(QueryError),
    Unsupported(UnsupportedState),
}

pub type Converted<T> = Result<T, Failure>;

pub type UncurriedFields = Vec<(SmolStr, Arc<[usize]>)>;

pub type RecordSpelling = (FileId, TypeItemId, Arc<[TypeId]>);

/// What converted, or nothing when the backend cannot compile the type.
pub fn supported<T>(converted: Converted<T>) -> QueryResult<Option<T>> {
    match converted {
        Ok(value) => Ok(Some(value)),
        Err(Failure::Unsupported(_)) => Ok(None),
        Err(Failure::Query(error)) => Err(error),
    }
}

impl From<QueryError> for Failure {
    fn from(error: QueryError) -> Failure {
        Failure::Query(error)
    }
}

impl From<UnsupportedState> for Failure {
    fn from(state: UnsupportedState) -> Failure {
        Failure::Unsupported(state)
    }
}

impl Failure {
    /// The error as reported by the emitter, which has no definition to name.
    pub fn in_code_generation(self) -> GoError {
        self.at("code generation")
    }

    /// The error as reported against the definition being compiled.
    pub fn at(self, definition: &str) -> GoError {
        match self {
            Failure::Query(error) => GoError::Query(error),
            Failure::Unsupported(state) => {
                GoError::Unsupported { definition: definition.to_string(), state }
            }
        }
    }
}

/// The definition an `unsafeCoerce` is written in, and its offset in the module's source.
#[derive(Debug, Clone)]
pub struct CoercionSite {
    pub definition: String,
    pub file_id: FileId,
    pub offset: Option<u32>,
}

/// A data type applied to closed type arguments. Arguments stay checker types rather
/// than monotypes because they may be higher-kinded, as in `Free f a`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DataType {
    pub file_id: FileId,
    pub item: TypeItemId,
    pub arguments: Arc<[TypeId]>,
}

#[derive(Debug, Clone)]
pub struct DataConstructor {
    pub term: Option<TermItemId>,
    pub name: SmolStr,
    pub fields: Vec<MonotypeId>,
    /// One of the fields is a type equality between apart types, as
    /// `IntValue (a ~ Int)` has at `Value String`. No value of the data type
    /// is built with the constructor, so a match on it is unreachable.
    pub refuted: bool,
}

const NEWTYPE_EXPANSION_LIMIT: usize = 64;

#[derive(Default)]
pub struct Monotypes {
    interned: Vec<Monotype>,
    lookup: FxHashMap<Monotype, MonotypeId>,
    converted: FxHashMap<TypeId, MonotypeId>,
    converted_reads: FxHashMap<TypeId, Vec<Read>>,
    constructors: FxHashMap<DataType, Arc<[DataConstructor]>>,
    constructors_reads: FxHashMap<DataType, Vec<Read>>,
    used_parameters: FxHashMap<(FileId, TypeItemId), Arc<[bool]>>,
    unfolded: FxHashMap<DataType, MonotypeId>,
    unfolded_reads: FxHashMap<DataType, Vec<Read>>,
    regular: FxHashMap<(FileId, TypeItemId), bool>,
    expanding: Vec<TypeId>,
    /// The newtype each function type is the representation of, or none when
    /// several newtypes share it.
    function_newtypes: FxHashMap<MonotypeId, Option<DataType>>,
    pub schemes: SchemeInstantiations,
    /// Rank-N field types met in this pass that the schemes do not list yet.
    pub new_rank_n_keys: Vec<(crate::scheme::SchemeKey, String)>,
    /// Owners of rank-N fields met with erased types in this pass.
    pub new_erased_owners: Vec<String>,
    /// Rank-N field types met in this pass that an erased owner holds.
    pub new_erased_keys: Vec<crate::scheme::SchemeKey>,
    /// Modules whose foreign imports the project implements in Go.
    pub foreign_modules: Vec<String>,
    /// The records a foreign package's struct represents, with that package's module and the
    /// struct's name.
    pub foreign_records: FxHashMap<MonotypeId, (String, String)>,
    pub native_foreigns: rustc_hash::FxHashSet<(FileId, TermItemId)>,
    pub row_free_foreigns: rustc_hash::FxHashSet<(FileId, TermItemId)>,
    pub native_foreign_data: rustc_hash::FxHashSet<(FileId, TypeItemId)>,
    pub empty_interface_foreign_data: rustc_hash::FxHashSet<(FileId, TypeItemId)>,
    pub uncurried_fields: FxHashMap<MonotypeId, UncurriedFields>,
    /// What the Go files next to each module's source declare.
    pub foreign_sources: Vec<crate::foreign::ForeignSource>,
    /// Where each `unsafeCoerce` between two types was written, for a coercion Go cannot make.
    pub coercion_sites: FxHashMap<(MonotypeId, MonotypeId), CoercionSite>,
    /// How the names of specialized and lifted functions were formed, which
    /// travels with the types those names spell.
    pub function_spellings: crate::monomorphic::FunctionSpellings,
    /// The synonyms and newtypes, with their arguments, that each record was
    /// spelled by where a type was converted, in the order met.
    pub record_spellings: FxHashMap<MonotypeId, Vec<RecordSpelling>>,
    /// The name of each type constructor met, which names its values.
    pub type_names: FxHashMap<(FileId, TypeItemId), SmolStr>,
    /// The newtypes specialization erased to the types they wrap.
    pub erased_newtypes: Vec<crate::context::ErasedNewtype>,
    /// The records that hold a rank-N value specialized at each of its
    /// instantiations, one field per instantiation.
    instantiated_records: rustc_hash::FxHashSet<MonotypeId>,
    existential: Option<(FileId, TypeItemId)>,
    variant: Option<(FileId, TypeItemId)>,
    collapsed: FxHashMap<MonotypeId, MonotypeId>,
}

impl Monotypes {
    pub fn intern(&mut self, monotype: Monotype) -> MonotypeId {
        if let Some(&id) = self.lookup.get(&monotype) {
            return id;
        }
        let id = MonotypeId(self.interned.len() as u32);
        self.interned.push(monotype.clone());
        self.lookup.insert(monotype, id);
        id
    }

    pub fn same_without_causes(&self, left: MonotypeId, right: MonotypeId) -> bool {
        if left == right {
            return true;
        }
        match (self.get(left), self.get(right)) {
            (Monotype::Erased(_), Monotype::Erased(_)) => true,
            (
                Monotype::Function(left_argument, left_result),
                Monotype::Function(argument, result),
            ) => {
                self.same_without_causes(*left_argument, *argument)
                    && self.same_without_causes(*left_result, *result)
            }
            (Monotype::Record(left_fields), Monotype::Record(fields)) => {
                left_fields.len() == fields.len()
                    && left_fields.iter().zip(fields.iter()).all(|(left_field, field)| {
                        left_field.label == field.label
                            && self.same_without_causes(left_field.monotype, field.monotype)
                    })
            }
            (left, right) => {
                std::mem::discriminant(left) == std::mem::discriminant(right)
                    && match (left.element(), right.element()) {
                        (Some(left_element), Some(element)) => {
                            self.same_without_causes(left_element, element)
                        }
                        _ => false,
                    }
            }
        }
    }

    pub fn without_causes(&mut self, id: MonotypeId) -> MonotypeId {
        if let Some(&collapsed) = self.collapsed.get(&id) {
            return collapsed;
        }
        let collapsed = match self.get(id).clone() {
            Monotype::Erased(_) => Monotype::Erased(Erasure::TypeVariable),
            Monotype::Function(argument, result) => {
                Monotype::Function(self.without_causes(argument), self.without_causes(result))
            }
            Monotype::Record(fields) => {
                let fields = fields.iter().map(|field| RecordField {
                    label: field.label.clone(),
                    monotype: self.without_causes(field.monotype),
                });
                Monotype::Record(fields.collect())
            }
            Monotype::Array(element) => Monotype::Array(self.without_causes(element)),
            Monotype::Effect(element) => Monotype::Effect(self.without_causes(element)),
            Monotype::Reference(element) => Monotype::Reference(self.without_causes(element)),
            Monotype::MutableArray(element) => Monotype::MutableArray(self.without_causes(element)),
            Monotype::Object(element) => Monotype::Object(self.without_causes(element)),
            Monotype::Nullable(element) => Monotype::Nullable(self.without_causes(element)),
            Monotype::Lazy(element) => Monotype::Lazy(self.without_causes(element)),
            Monotype::ConsList(element) => Monotype::ConsList(self.without_causes(element)),
            Monotype::HashMap(key, value) => {
                Monotype::HashMap(self.without_causes(key), self.without_causes(value))
            }
            Monotype::OrderedMap(key, value) => {
                Monotype::OrderedMap(self.without_causes(key), self.without_causes(value))
            }
            monotype => monotype,
        };
        let collapsed = self.intern(collapsed);
        if self.instantiated_records.contains(&id) {
            self.instantiated_records.insert(collapsed);
        }
        self.collapsed.insert(id, collapsed);
        collapsed
    }

    /// Every monotype interned so far.
    pub fn ids(&self) -> impl Iterator<Item = MonotypeId> + use<> {
        (0..self.interned.len() as u32).map(MonotypeId)
    }

    pub fn get(&self, id: MonotypeId) -> &Monotype {
        &self.interned[id.0 as usize]
    }

    /// Whether a record holds a rank-N value, one field per instantiation,
    /// rather than a PureScript record.
    pub fn is_instantiated_record(&self, id: MonotypeId) -> bool {
        self.instantiated_records.contains(&id)
    }

    /// The one newtype whose representation a function type is, as `Lazy Int`
    /// is `Unit -> Int`.
    pub fn function_newtype(&self, id: MonotypeId) -> Option<&DataType> {
        self.function_newtypes.get(&id)?.as_ref()
    }

    pub fn function(&mut self, argument: MonotypeId, result: MonotypeId) -> MonotypeId {
        self.intern(Monotype::Function(argument, result))
    }

    pub fn function_parts(&self, id: MonotypeId) -> Option<(MonotypeId, MonotypeId)> {
        match self.get(id) {
            Monotype::Function(argument, result) => Some((*argument, *result)),
            _ => None,
        }
    }

    pub fn effect_result(&self, id: MonotypeId) -> Option<MonotypeId> {
        match self.get(id) {
            Monotype::Effect(result) => Some(*result),
            _ => None,
        }
    }

    /// Strips `count` arguments off a curried function type.
    pub fn result_after(&self, mut id: MonotypeId, count: usize) -> MonotypeId {
        for _ in 0..count {
            match self.function_parts(id) {
                Some((_, result)) => id = result,
                None => break,
            }
        }
        id
    }
}
