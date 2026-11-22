//! A small Go syntax tree with a printer that follows `gofmt` layout.

mod directives;
mod names;
mod printer;

pub use names::{DeclarationNames, Name, Reference, statements_names};
pub use printer::{GoFile, GoImport};

use std::sync::Arc;

#[derive(Debug, Clone, Eq)]
pub enum GoType {
    Named(String),
    Int,
    Float64,
    Bool,
    Rune,
    String,
    EmptyStruct,
    Any,
    /// `any` standing for a type erased for the given reason.
    Erased(crate::erasure::Erasure),
    Slice(Box<GoType>),
    Pointer(Box<GoType>),
    Function {
        parameters: Vec<GoType>,
        result: Option<Box<GoType>>,
    },
    Struct(Vec<StructField>),
    /// A generic type instantiated at type arguments, `name[arguments]`.
    Generic {
        name: String,
        arguments: Vec<GoType>,
    },
}

/// Types compare as Go sees them: every flavour of `any` is the same type.
impl PartialEq for GoType {
    fn eq(&self, other: &GoType) -> bool {
        use GoType::*;
        match (self, other) {
            (Any | Erased(_), Any | Erased(_)) => true,
            (Named(left), Named(right)) => left == right,
            (Int, Int) | (Float64, Float64) | (Bool, Bool) | (Rune, Rune) => true,
            (String, String) | (EmptyStruct, EmptyStruct) => true,
            (Slice(left), Slice(right)) | (Pointer(left), Pointer(right)) => left == right,
            (
                Function { parameters: left, result: left_result },
                Function { parameters: right, result: right_result },
            ) => left == right && left_result == right_result,
            (Struct(left), Struct(right)) => left == right,
            (
                Generic { name: left, arguments: left_arguments },
                Generic { name: right, arguments: right_arguments },
            ) => left == right && left_arguments == right_arguments,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructField {
    pub name: String,
    pub type_: GoType,
    pub label: Option<String>,
}

impl StructField {
    pub fn new(name: impl Into<String>, type_: GoType) -> StructField {
        StructField { name: name.into(), type_, label: None }
    }
}

#[derive(Debug, Clone)]
pub enum GoExpression {
    Identifier(String),
    Qualified {
        package: String,
        name: String,
    },
    Integer(i64),
    Float(String),
    String(String),
    /// A string holding a lone surrogate, as its UTF-16 code units: Go spells it in WTF-8, the
    /// representation go-support's prim package gives PureScript strings.
    Utf16(Arc<[u16]>),
    Rune(char),
    Boolean(bool),
    Call {
        function: Box<GoExpression>,
        arguments: Vec<GoExpression>,
    },
    Binary {
        operator: &'static str,
        left: Box<GoExpression>,
        right: Box<GoExpression>,
    },
    Unary {
        operator: &'static str,
        operand: Box<GoExpression>,
    },
    Field {
        value: Box<GoExpression>,
        name: String,
    },
    Index {
        value: Box<GoExpression>,
        index: Box<GoExpression>,
    },
    Composite {
        type_: GoType,
        fields: Vec<(Option<String>, GoExpression)>,
    },
    Address(Box<GoExpression>),
    Conversion {
        type_: GoType,
        value: Box<GoExpression>,
    },
    TypeAssertion {
        value: Box<GoExpression>,
        type_: GoType,
    },
    Type(GoType),
    Spread(Box<GoExpression>),
    Function {
        parameters: Vec<(String, GoType)>,
        result: Option<GoType>,
        body: Vec<GoStatement>,
    },
    /// A generic function instantiated at type arguments, `function[arguments]`.
    Instantiation {
        function: Box<GoExpression>,
        arguments: Vec<GoType>,
    },
    Attributed {
        line: SourceLine,
        value: Box<GoExpression>,
    },
}

#[derive(Debug, Clone)]
pub enum GoStatement {
    Define {
        names: Vec<String>,
        values: Vec<GoExpression>,
    },
    Variable {
        name: String,
        type_: GoType,
        value: Option<GoExpression>,
    },
    Assign {
        targets: Vec<GoExpression>,
        values: Vec<GoExpression>,
    },
    Expression(GoExpression),
    Defer(GoExpression),
    Return(Option<GoExpression>),
    If {
        condition: GoExpression,
        then: Vec<GoStatement>,
        otherwise: Vec<GoStatement>,
    },
    Switch {
        value: Option<GoExpression>,
        cases: Vec<GoCase>,
        default: Option<GoDefault>,
    },
    /// `if name, ok := value.(T); ok { then }`
    IfAssert {
        name: String,
        value: GoExpression,
        type_: GoType,
        then: Vec<GoStatement>,
    },
    Loop(Vec<GoStatement>),
    Range {
        index: Option<String>,
        element: String,
        iterable: GoExpression,
        body: Vec<GoStatement>,
    },
    Counting {
        variable: String,
        start: GoExpression,
        end: GoExpression,
        body: Vec<GoStatement>,
    },
    CountingDown {
        variable: String,
        start: GoExpression,
        body: Vec<GoStatement>,
    },
    Continue,
    Break,
    BreakTo(String),
    LabeledLoop {
        label: String,
        body: Vec<GoStatement>,
    },
    /// A `//line` directive: Go attributes the code after it, up to the next one, to the
    /// PureScript source.
    Line(SourceLine),
}

/// A line of a PureScript source file, as a `//line` directive names it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceLine {
    pub path: Arc<str>,
    pub line: u32,
    pub column: u32,
}

impl GoExpression {
    /// Whether evaluating the expression calls a function or indexes; a function literal's body
    /// does not run where it is written.
    fn does_work(&self) -> bool {
        match self {
            GoExpression::Call { .. }
            | GoExpression::Index { .. }
            | GoExpression::TypeAssertion { .. } => true,
            GoExpression::Function { .. } => false,
            GoExpression::Binary { left, right, .. } => left.does_work() || right.does_work(),
            GoExpression::Unary { operand: value, .. }
            | GoExpression::Field { value, .. }
            | GoExpression::Address(value)
            | GoExpression::Conversion { value, .. }
            | GoExpression::Spread(value)
            | GoExpression::Instantiation { function: value, .. }
            | GoExpression::Attributed { value, .. } => value.does_work(),
            GoExpression::Composite { fields, .. } => {
                fields.iter().any(|(_, field)| field.does_work())
            }
            GoExpression::Identifier(_)
            | GoExpression::Qualified { .. }
            | GoExpression::Integer(_)
            | GoExpression::Float(_)
            | GoExpression::String(_)
            | GoExpression::Utf16(_)
            | GoExpression::Rune(_)
            | GoExpression::Boolean(_)
            | GoExpression::Type(_) => false,
        }
    }

    pub fn unattributed(&self) -> &GoExpression {
        match self {
            GoExpression::Attributed { value, .. } => value.unattributed(),
            expression => expression,
        }
    }
}

impl GoStatement {
    /// Whether running the statement itself, apart from the blocks in it, calls a function or
    /// indexes, which can fail.
    fn does_work(&self) -> bool {
        match self {
            GoStatement::Define { values, .. } => values.iter().any(GoExpression::does_work),
            GoStatement::Assign { targets, values } => {
                targets.iter().chain(values).any(GoExpression::does_work)
            }
            GoStatement::Variable { value: Some(value), .. }
            | GoStatement::Return(Some(value))
            | GoStatement::Expression(value)
            | GoStatement::Defer(value)
            | GoStatement::If { condition: value, .. }
            | GoStatement::Switch { value: Some(value), .. }
            | GoStatement::IfAssert { value, .. }
            | GoStatement::Range { iterable: value, .. }
            | GoStatement::CountingDown { start: value, .. } => value.does_work(),
            GoStatement::Counting { start, end, .. } => start.does_work() || end.does_work(),
            GoStatement::Variable { value: None, .. }
            | GoStatement::Return(None)
            | GoStatement::Switch { value: None, .. }
            | GoStatement::Loop(_)
            | GoStatement::Continue
            | GoStatement::Break
            | GoStatement::BreakTo(_)
            | GoStatement::LabeledLoop { .. }
            | GoStatement::Line(_) => false,
        }
    }

    /// A call of Go's `panic`, which ends the block like a `return`.
    pub fn is_panic(&self) -> bool {
        matches!(
            self,
            GoStatement::Expression(GoExpression::Call { function, .. })
                if matches!(function.as_ref(), GoExpression::Identifier(name) if name == "panic")
        )
    }
}

#[derive(Debug, Clone)]
pub struct GoCase {
    pub values: Vec<GoExpression>,
    pub body: Vec<GoStatement>,
    pub line: Option<SourceLine>,
}

#[derive(Debug, Clone)]
pub struct GoDefault {
    pub covers: Vec<GoExpression>,
    pub body: Vec<GoStatement>,
    pub line: Option<SourceLine>,
}

impl GoDefault {
    pub fn covering(cases: &mut Vec<GoCase>) -> GoDefault {
        let GoCase { values, body, line } =
            cases.pop().expect("invariant violated: a total switch has a case");
        GoDefault { covers: values, body, line }
    }
}

#[derive(Debug, Clone)]
pub enum GoDeclaration {
    /// Fixed support code that generated programs share, declaring `name`
    /// where its template says `{name}`.
    Source {
        name: String,
        template: &'static str,
    },
    Type {
        name: String,
        type_: GoType,
        line: Option<SourceLine>,
        member_lines: Vec<(String, SourceLine)>,
    },
    /// `type name = type_`: another spelling of the same type, for a recursive
    /// newtype whose cycle already passes through a named type.
    Alias {
        name: String,
        type_: GoType,
        line: Option<SourceLine>,
    },
    /// `type name[parameter any] type_`.
    GenericType {
        name: String,
        parameter: String,
        type_: GoType,
    },
    Constants {
        type_name: Option<String>,
        names: Vec<String>,
        line: Option<SourceLine>,
        member_lines: Vec<(String, SourceLine)>,
    },
    Constant {
        name: String,
        type_: Option<GoType>,
        value: GoExpression,
    },
    Variable {
        name: String,
        type_: Option<GoType>,
        value: GoExpression,
        line: Option<SourceLine>,
    },
    Function {
        name: String,
        parameters: Vec<(String, GoType)>,
        result: Option<GoType>,
        body: Vec<GoStatement>,
    },
    /// A declaration of `name` written out in full, which no pass rewrites.
    Written {
        name: String,
        source: String,
        line: Option<SourceLine>,
    },
}
