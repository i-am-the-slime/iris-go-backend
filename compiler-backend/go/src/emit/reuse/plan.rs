use rustc_hash::{FxHashMap, FxHashSet};

use super::facts::Variant;
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Literal, LocalId, Pattern,
};
use crate::monotype::DataType;

#[derive(Clone)]
pub(super) struct Spare {
    pub(super) local: LocalId,
    pub(super) data: DataType,
    pub(super) origin: Origin,
    pub(super) owners: Vec<LocalId>,
    pub(super) condition: Option<Expression>,
}

#[derive(Clone)]
pub(super) struct Token {
    pub(super) cell: LocalId,
    pub(super) condition: Option<Expression>,
}

#[derive(Clone, PartialEq)]
pub(super) enum Held {
    Shared,
    Owned,
    Fresh,
    Unique(Expression),
}

impl Held {
    pub(super) fn is_owned(&self) -> bool {
        matches!(self, Held::Owned)
    }

    pub(super) fn is_fresh(&self) -> bool {
        match self {
            Held::Owned | Held::Fresh => true,
            Held::Unique(companion) => is_true(companion),
            Held::Shared => false,
        }
    }

    pub(super) fn join(self, other: Held) -> Held {
        match (self, other) {
            (Held::Owned, Held::Owned) => Held::Owned,
            (left, right) if left.is_fresh() && right.is_fresh() => Held::Fresh,
            (Held::Unique(left), Held::Unique(right)) if left == right => Held::Unique(left),
            _ => Held::Shared,
        }
    }
}

#[derive(Clone)]
pub(super) struct Dynamic {
    pub(super) companion: Expression,
    pub(super) ancestors: Vec<LocalId>,
}

#[derive(Clone, Copy)]
pub(super) enum Origin {
    Donor,
    Scrutinee { alternative: usize },
    Hoisted { case: *const Expression, position: usize, alternative: usize },
    Field { pattern: *const Pattern, alternative: usize },
}

#[derive(Default, Clone)]
pub(super) struct Plan {
    pub(super) result_owned: bool,
    pub(super) result_fresh: bool,
    pub(super) donor_used: bool,
    pub(super) writes: bool,
    pub(super) donor: Option<LocalId>,
    pub(super) companions: Vec<(usize, LocalId)>,
    pub(super) constructs: FxHashMap<*const Expression, Token>,
    pub(super) edges: FxHashMap<*const Expression, Vec<(usize, Expression)>>,
    pub(super) calls: FxHashMap<*const Expression, (Variant, Option<LocalId>, Vec<Expression>)>,
    pub(super) callbacks: FxHashMap<*const Expression, Variant>,
    pub(super) hoisted: FxHashMap<(*const Expression, usize), LocalId>,
    pub(super) pattern_cells: FxHashMap<*const Pattern, LocalId>,
    pub(super) bindings: FxHashMap<*const Alternative, Vec<Binding>>,
    pub(super) materialized: FxHashSet<LocalId>,
    pub(super) next_local: u32,
}

pub(super) fn is_true(expression: &Expression) -> bool {
    matches!(expression.kind, ExpressionKind::Literal(Literal::Boolean(true)))
}
