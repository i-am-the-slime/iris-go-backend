//! Why a type became Go `any`. Every erasure carries its cause from the point
//! where the specializer or the monotype conversion gave up on a concrete type,
//! so `IRIS_GO_ANY_CENSUS=1` can report how many `any` each cause emits. The
//! census build tells causes apart, so its output can differ slightly (more
//! conversions between differently-erased types) from a normal build.

use std::fmt;

use rustc_hash::FxHashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Erasure {
    /// A type variable without an instantiation.
    TypeVariable,
    /// A variable bound by an unconstrained rank-N `forall`, such as the answer
    /// type of a CPS parser.
    RankN,
    /// A type variable left in the arguments of a data type or newtype.
    ArgumentVariable,
    /// A type variable applied to arguments (`f a` with `f` unknown).
    VariableApplication,
    /// The payload of a `Variant` or the row of a `VariantF`, whose types the
    /// label chooses at run time.
    VariantRow,
    /// `Data.Exists.Exists`, an existential by construction.
    Existential,
    /// A newtype that unfolds into itself without a recursive data type.
    NewtypeCycle,
    /// A data type with no constructors.
    EmptyData,
    /// The arguments of a non-regular data type (`data T a = ... (T (f a))`).
    NonRegular,
    /// A specialization request that embeds its own requester's types and
    /// would grow without bound (polymorphic recursion).
    PolymorphicRecursion,
    /// The canonical boxed form of a value stored at an erased position.
    Boxing,
    /// A definition the backend could not compile, kept as a failing stub.
    FailedDefinition,
    /// A JavaScript value (`Foreign`, promises, host handles).
    Foreign,
    /// `any` written by the backend itself rather than derived from a type.
    Runtime,
    /// A type the checker left unsolved, so that nothing in the program fixes
    /// it: the value comes from an `unsafeCoerce` or a foreign whose result
    /// type is free (`Data.Variant`'s payloads, say).
    Unsolved,
}

impl Erasure {
    /// The cause as the program's types record it. Distinct causes make
    /// distinct (if equally erased) types, which changes the emitted
    /// conversions, so causes are told apart only while taking the census.
    pub fn tracked(self) -> Erasure {
        static CENSUS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        let census = *CENSUS.get_or_init(|| std::env::var_os("IRIS_GO_ANY_CENSUS").is_some());
        if census || matches!(self, Erasure::Foreign | Erasure::Runtime) {
            self
        } else {
            Erasure::TypeVariable
        }
    }

    pub const ALL: [Erasure; 15] = [
        Erasure::ArgumentVariable,
        Erasure::TypeVariable,
        Erasure::RankN,
        Erasure::VariableApplication,
        Erasure::VariantRow,
        Erasure::Existential,
        Erasure::NewtypeCycle,
        Erasure::EmptyData,
        Erasure::NonRegular,
        Erasure::PolymorphicRecursion,
        Erasure::Boxing,
        Erasure::FailedDefinition,
        Erasure::Foreign,
        Erasure::Runtime,
        Erasure::Unsolved,
    ];

    pub fn code(self) -> u32 {
        Erasure::ALL.iter().position(|&erasure| erasure == self).unwrap_or(0) as u32
    }

    pub fn from_code(code: u32) -> Option<Erasure> {
        Erasure::ALL.get(code as usize).copied()
    }
}

impl fmt::Display for Erasure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Erasure::TypeVariable => "uninstantiated type variable",
            Erasure::RankN => "rank-N forall (unconstrained)",
            Erasure::ArgumentVariable => "type variable in data type arguments",
            Erasure::VariableApplication => "type variable application",
            Erasure::VariantRow => "Variant payload or VariantF row",
            Erasure::Existential => "Data.Exists",
            Erasure::NewtypeCycle => "newtype cycle",
            Erasure::EmptyData => "empty data type",
            Erasure::NonRegular => "non-regular data type",
            Erasure::PolymorphicRecursion => "polymorphic recursion",
            Erasure::Boxing => "boxing at an erased position",
            Erasure::FailedDefinition => "failed definition",
            Erasure::Foreign => "foreign (JavaScript) value",
            Erasure::Runtime => "backend runtime plumbing",
            Erasure::Unsolved => "type the checker left unsolved",
        };
        f.write_str(text)
    }
}

/// Rendered `any` occurrences per cause.
#[derive(Debug, Default, Clone)]
pub struct Census {
    pub counts: FxHashMap<Erasure, usize>,
    pub assertions: usize,
}

impl Census {
    pub fn record(&mut self, erasure: Erasure) {
        *self.counts.entry(erasure).or_default() += 1;
    }

    pub fn absorb(&mut self, other: Census) {
        for (erasure, count) in other.counts {
            *self.counts.entry(erasure).or_default() += count;
        }
        self.assertions += other.assertions;
    }

    pub fn total(&self) -> usize {
        self.counts.values().sum()
    }
}

impl fmt::Display for Census {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut rows: Vec<(Erasure, usize)> =
            self.counts.iter().map(|(&erasure, &count)| (erasure, count)).collect();
        rows.sort_by(|left, right| right.1.cmp(&left.1).then(left.0.cmp(&right.0)));
        writeln!(f, "any census: {} `any`, {} type assertions", self.total(), self.assertions)?;
        for (erasure, count) in rows {
            writeln!(f, "  {count:>8}  {erasure}")?;
        }
        Ok(())
    }
}
