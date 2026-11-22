//! A closed, monomorphic tree: every node carries a concrete type, every reference
//! names one specialization, and no dictionaries remain.
//!
//! A `Closure` is a value of a function type that `emit::closures` represents as a
//! cell: the tag of the lambda that created it and the values that lambda captures.
//! A `Closure` pattern matches one tag and binds its captures.

use std::sync::Arc;

use checking::TypeId;
use files::FileId;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::foreign::Foreign;
use crate::monotype::{DataType, MonotypeId};

pub(crate) mod walk;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

#[derive(Debug)]
pub struct Program {
    pub functions: Vec<Function>,
    pub entry: FunctionId,
}

pub type FunctionSpellings = FxHashMap<SmolStr, FunctionSpelling>;

/// How a function's name was formed, so that the emitter can spell the types
/// in it with the short names it gives them.
#[derive(Debug, Clone)]
pub enum FunctionSpelling {
    /// A definition's name followed by the types it is specialized at. A member's name is
    /// followed first by the types of its instance's head, which are spelled only where they
    /// tell apart members of the same name: `show` of `Show Int` and of `Show String`.
    Specialized { name: SmolStr, head: Arc<[TypeId]>, types: Arc<[TypeId]> },
    /// A local function lifted out of another, named after both.
    Lifted { parent: SmolStr, local: SmolStr },
    /// The function that runs the cells of a closed function type, `run`
    /// followed by the type's name.
    Dispatch { closure: crate::monotype::MonotypeId },
}

impl Program {
    pub fn function(&self, id: FunctionId) -> &Function {
        &self.functions[id.0 as usize]
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: SmolStr,
    /// The module whose definition the function specializes, or whose
    /// definition it was lifted out of; none once it stands for identical
    /// functions of modules that do not see each other.
    pub origin: Option<FileId>,
    pub parameters: Vec<Local>,
    pub result: MonotypeId,
    pub body: Expression,
    pub position: Option<SourcePosition>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Local {
    pub id: LocalId,
    pub name: SmolStr,
    pub monotype: MonotypeId,
}

impl Local {
    /// A reference to the local.
    pub fn expression(&self) -> Expression {
        Expression::new(ExpressionKind::Local(self.id), self.monotype)
    }

    /// A local no other has the id of, taking the next one from `next_local`.
    pub fn fresh(next_local: &mut u32, name: SmolStr, monotype: MonotypeId) -> Local {
        let id = LocalId(*next_local);
        *next_local += 1;
        Local { id, name, monotype }
    }
}

/// Expressions are equal when they compute the same value: where they are written does not
/// matter, so that identical code from different places still merges.
#[derive(Debug, Clone)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub monotype: MonotypeId,
    /// Where the PureScript the expression comes from is written, if anywhere.
    pub position: Option<SourcePosition>,
}

impl PartialEq for Expression {
    fn eq(&self, other: &Expression) -> bool {
        self.kind == other.kind && self.monotype == other.monotype
    }
}

impl Eq for Expression {}

impl std::hash::Hash for Expression {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        self.monotype.hash(state);
    }
}

/// A byte offset into a source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourcePosition {
    pub file: FileId,
    pub offset: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Int(i64),
    Number(SmolStr),
    String(String),
    /// A string holding a lone surrogate, which a Rust `String` cannot, as its UTF-16 code units.
    Utf16(Arc<[u16]>),
    Char(char),
    Boolean(bool),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpressionKind {
    Literal(Literal),
    Unit,
    Array(Vec<Expression>),
    Record(Vec<(SmolStr, Expression)>),
    Access { record: Box<Expression>, label: SmolStr },
    Update { record: Box<Expression>, updates: Vec<RecordUpdate> },
    Local(LocalId),
    Function(FunctionId),
    Construct { data: DataType, constructor: usize, arguments: Vec<Expression> },
    Reuse { cell: Box<Expression>, data: DataType, constructor: usize, arguments: Vec<Expression> },
    Foreign { foreign: &'static Foreign, arguments: Vec<Expression> },
    Apply { function: Box<Expression>, arguments: Vec<Expression> },
    Lambda { parameters: Vec<Local>, body: Box<Expression> },
    Closure { tag: usize, captures: Vec<Expression> },
    Coerce(Box<Expression>),
    Let { bindings: Vec<Binding>, body: Box<Expression> },
    If { condition: Box<Expression>, then: Box<Expression>, otherwise: Box<Expression> },
    Case { scrutinees: Vec<Expression>, alternatives: Vec<Alternative> },
    EffectPure(Box<Expression>),
    EffectBind { action: Box<Expression>, local: Local, body: Box<Expression> },
    EffectEach { array: Box<Expression>, element: Local, body: Box<Expression> },
    Fail(SmolStr),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RecordUpdate {
    Leaf { label: SmolStr, value: Expression },
    Branch { label: SmolStr, updates: Vec<RecordUpdate> },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Binding {
    pub local: Local,
    pub value: Expression,
}

#[derive(Debug, Clone)]
pub struct Alternative {
    pub patterns: Vec<Pattern>,
    pub body: Guarded,
    pub position: Option<SourcePosition>,
}

impl PartialEq for Alternative {
    fn eq(&self, other: &Alternative) -> bool {
        self.patterns == other.patterns && self.body == other.body
    }
}

impl Eq for Alternative {}

impl std::hash::Hash for Alternative {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.patterns.hash(state);
        self.body.hash(state);
    }
}

pub const PATTERN_MATCH_FAILURE: &str = "Failed pattern match";

impl Guard {
    /// The expression the guard evaluates.
    pub fn value(&self) -> &Expression {
        match self {
            Guard::Boolean(condition) => condition,
            Guard::Pattern { value, .. } => value,
        }
    }
}

impl Guard {
    pub fn value_mut(&mut self) -> &mut Expression {
        match self {
            Guard::Boolean(condition) => condition,
            Guard::Pattern { value, .. } => value,
        }
    }
}

impl Alternative {
    /// Every local the alternative's patterns and pattern guards bind.
    pub fn for_each_local<'a>(&'a self, visit: &mut impl FnMut(&'a Local)) {
        self.patterns.iter().for_each(|pattern| pattern.for_each_local(visit));
        if let Guarded::Guards(branches) = &self.body {
            for guard in branches.iter().flat_map(|branch| &branch.guards) {
                if let Guard::Pattern { pattern, .. } = guard {
                    pattern.for_each_local(visit);
                }
            }
        }
    }

    pub fn match_failure(scrutinees: &[Expression], result: MonotypeId) -> Alternative {
        let patterns = scrutinees
            .iter()
            .map(|scrutinee| Pattern { kind: PatternKind::Wildcard, monotype: scrutinee.monotype })
            .collect();
        let failure = ExpressionKind::Fail(SmolStr::new_static(PATTERN_MATCH_FAILURE));
        let body = Guarded::Unconditional(Expression::new(failure, result));
        Alternative { patterns, body, position: None }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Guarded {
    Unconditional(Expression),
    Guards(Vec<GuardedBranch>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GuardedBranch {
    pub guards: Vec<Guard>,
    pub body: Expression,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Guard {
    Boolean(Expression),
    Pattern { pattern: Pattern, value: Expression },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Pattern {
    pub kind: PatternKind,
    pub monotype: MonotypeId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PatternKind {
    Wildcard,
    Variable(Local),
    Named { local: Local, pattern: Box<Pattern> },
    Literal(Literal),
    Array(Vec<Pattern>),
    Record(Vec<(SmolStr, Pattern)>),
    Constructor { data: DataType, constructor: usize, arguments: Vec<Pattern> },
    Closure { tag: usize, captures: Vec<Pattern> },
}

impl Pattern {
    /// Every local the pattern binds, outer before inner.
    pub fn for_each_local<'p>(&'p self, visit: &mut impl FnMut(&'p Local)) {
        match &self.kind {
            PatternKind::Wildcard | PatternKind::Literal(_) => {}
            PatternKind::Variable(local) => visit(local),
            PatternKind::Named { local, pattern } => {
                visit(local);
                pattern.for_each_local(visit);
            }
            PatternKind::Array(patterns)
            | PatternKind::Constructor { arguments: patterns, .. }
            | PatternKind::Closure { captures: patterns, .. } => {
                patterns.iter().for_each(|pattern| pattern.for_each_local(visit))
            }
            PatternKind::Record(fields) => {
                fields.iter().for_each(|(_, pattern)| pattern.for_each_local(visit))
            }
        }
    }

    /// [`Self::for_each_local`], to rename or retype them.
    pub fn for_each_local_mut(&mut self, visit: &mut impl FnMut(&mut Local)) {
        match &mut self.kind {
            PatternKind::Wildcard | PatternKind::Literal(_) => {}
            PatternKind::Variable(local) => visit(local),
            PatternKind::Named { local, pattern } => {
                visit(local);
                pattern.for_each_local_mut(visit);
            }
            PatternKind::Array(patterns)
            | PatternKind::Constructor { arguments: patterns, .. }
            | PatternKind::Closure { captures: patterns, .. } => {
                patterns.iter_mut().for_each(|pattern| pattern.for_each_local_mut(visit))
            }
            PatternKind::Record(fields) => {
                fields.iter_mut().for_each(|(_, pattern)| pattern.for_each_local_mut(visit))
            }
        }
    }

    pub fn is_irrefutable(&self) -> bool {
        match &self.kind {
            PatternKind::Wildcard | PatternKind::Variable(_) => true,
            PatternKind::Named { pattern, .. } => pattern.is_irrefutable(),
            PatternKind::Record(fields) => {
                fields.iter().all(|(_, pattern)| pattern.is_irrefutable())
            }
            PatternKind::Literal(_)
            | PatternKind::Array(_)
            | PatternKind::Constructor { .. }
            | PatternKind::Closure { .. } => false,
        }
    }
}

impl Expression {
    pub fn new(kind: ExpressionKind, monotype: MonotypeId) -> Expression {
        Expression { kind, monotype, position: None }
    }

    /// The expression, written at `position` unless it already says where it is written.
    pub fn located(mut self, position: Option<SourcePosition>) -> Expression {
        self.position = self.position.or(position);
        self
    }

    /// The expression that replaces one written at `position`: written there too, wherever the
    /// code it is made of is written.
    pub fn replacing(mut self, position: Option<SourcePosition>) -> Expression {
        self.position = position.or(self.position);
        self
    }
}
