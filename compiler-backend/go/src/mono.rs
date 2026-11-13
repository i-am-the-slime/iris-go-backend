//! A closed, monomorphic tree: every node carries a concrete type, every reference
//! names one specialization, and no dictionaries remain.

use smol_str::SmolStr;

use crate::foreign::Foreign;
use crate::monotype::{DataType, MonotypeId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

#[derive(Debug)]
pub struct Program {
    pub functions: Vec<Function>,
    pub entry: FunctionId,
}

impl Program {
    pub fn function(&self, id: FunctionId) -> &Function {
        &self.functions[id.0 as usize]
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: SmolStr,
    pub parameters: Vec<Local>,
    pub result: MonotypeId,
    pub body: Expression,
}

#[derive(Debug, Clone)]
pub struct Local {
    pub id: LocalId,
    pub name: SmolStr,
    pub monotype: MonotypeId,
}

#[derive(Debug, Clone)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub monotype: MonotypeId,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    Number(SmolStr),
    String(String),
    Char(char),
    Boolean(bool),
}

#[derive(Debug, Clone)]
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
    Foreign { foreign: Foreign, arguments: Vec<Expression> },
    Apply { function: Box<Expression>, arguments: Vec<Expression> },
    Lambda { parameters: Vec<Local>, body: Box<Expression> },
    Coerce(Box<Expression>),
    Let { bindings: Vec<Binding>, body: Box<Expression> },
    If { condition: Box<Expression>, then: Box<Expression>, otherwise: Box<Expression> },
    Case { scrutinees: Vec<Expression>, alternatives: Vec<Alternative> },
    EffectPure(Box<Expression>),
    EffectBind { action: Box<Expression>, local: Local, body: Box<Expression> },
    EffectEach { array: Box<Expression>, element: Local, body: Box<Expression> },
    EffectWhen { condition: Box<Expression>, action: Box<Expression> },
    Fail(SmolStr),
}

#[derive(Debug, Clone)]
pub enum RecordUpdate {
    Leaf { label: SmolStr, value: Expression },
    Branch { label: SmolStr, updates: Vec<RecordUpdate> },
}

#[derive(Debug, Clone)]
pub struct Binding {
    pub local: Local,
    pub value: Expression,
}

#[derive(Debug, Clone)]
pub struct Alternative {
    pub patterns: Vec<Pattern>,
    pub body: Guarded,
}

pub const PATTERN_MATCH_FAILURE: &str = "Pattern match failure";

impl Alternative {
    pub fn match_failure(scrutinees: &[Expression], result: MonotypeId) -> Alternative {
        let patterns = scrutinees
            .iter()
            .map(|scrutinee| Pattern { kind: PatternKind::Wildcard, monotype: scrutinee.monotype })
            .collect();
        let failure = ExpressionKind::Fail(SmolStr::new_static(PATTERN_MATCH_FAILURE));
        let body = Guarded::Unconditional(Expression::new(failure, result));
        Alternative { patterns, body }
    }
}

#[derive(Debug, Clone)]
pub enum Guarded {
    Unconditional(Expression),
    Guards(Vec<GuardedBranch>),
}

#[derive(Debug, Clone)]
pub struct GuardedBranch {
    pub guards: Vec<Guard>,
    pub body: Expression,
}

#[derive(Debug, Clone)]
pub enum Guard {
    Boolean(Expression),
    Pattern { pattern: Pattern, value: Expression },
}

#[derive(Debug, Clone)]
pub struct Pattern {
    pub kind: PatternKind,
    pub monotype: MonotypeId,
}

#[derive(Debug, Clone)]
pub enum PatternKind {
    Wildcard,
    Variable(Local),
    Named { local: Local, pattern: Box<Pattern> },
    Literal(Literal),
    Array(Vec<Pattern>),
    Record(Vec<(SmolStr, Pattern)>),
    Constructor { data: DataType, constructor: usize, arguments: Vec<Pattern> },
}

impl Pattern {
    pub fn is_irrefutable(&self) -> bool {
        match &self.kind {
            PatternKind::Wildcard | PatternKind::Variable(_) => true,
            PatternKind::Named { pattern, .. } => pattern.is_irrefutable(),
            PatternKind::Record(fields) => {
                fields.iter().all(|(_, pattern)| pattern.is_irrefutable())
            }
            PatternKind::Literal(_) | PatternKind::Array(_) | PatternKind::Constructor { .. } => {
                false
            }
        }
    }
}

impl Expression {
    pub fn new(kind: ExpressionKind, monotype: MonotypeId) -> Expression {
        Expression { kind, monotype }
    }
}
