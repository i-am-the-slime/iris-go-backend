use super::GoExpression;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GoBuiltin {
    Append,
    Cap,
    Clear,
    Close,
    Complex,
    Copy,
    Delete,
    Imag,
    Len,
    Make,
    Max,
    Min,
    New,
    Panic,
    Print,
    Println,
    Real,
    Recover,
}

const BUILTINS: [GoBuiltin; 18] = [
    GoBuiltin::Append,
    GoBuiltin::Cap,
    GoBuiltin::Clear,
    GoBuiltin::Close,
    GoBuiltin::Complex,
    GoBuiltin::Copy,
    GoBuiltin::Delete,
    GoBuiltin::Imag,
    GoBuiltin::Len,
    GoBuiltin::Make,
    GoBuiltin::Max,
    GoBuiltin::Min,
    GoBuiltin::New,
    GoBuiltin::Panic,
    GoBuiltin::Print,
    GoBuiltin::Println,
    GoBuiltin::Real,
    GoBuiltin::Recover,
];

impl GoBuiltin {
    pub fn name(self) -> &'static str {
        match self {
            GoBuiltin::Append => "append",
            GoBuiltin::Cap => "cap",
            GoBuiltin::Clear => "clear",
            GoBuiltin::Close => "close",
            GoBuiltin::Complex => "complex",
            GoBuiltin::Copy => "copy",
            GoBuiltin::Delete => "delete",
            GoBuiltin::Imag => "imag",
            GoBuiltin::Len => "len",
            GoBuiltin::Make => "make",
            GoBuiltin::Max => "max",
            GoBuiltin::Min => "min",
            GoBuiltin::New => "new",
            GoBuiltin::Panic => "panic",
            GoBuiltin::Print => "print",
            GoBuiltin::Println => "println",
            GoBuiltin::Real => "real",
            GoBuiltin::Recover => "recover",
        }
    }

    pub fn named(name: &str) -> Option<GoBuiltin> {
        BUILTINS.into_iter().find(|builtin| builtin.name() == name)
    }
}

impl GoExpression {
    pub fn builtin(builtin: GoBuiltin) -> GoExpression {
        GoExpression::Identifier(builtin.name().to_string())
    }

    pub fn nil() -> GoExpression {
        GoExpression::Identifier("nil".to_string())
    }

    pub fn as_builtin(&self) -> Option<GoBuiltin> {
        match self {
            GoExpression::Identifier(name) => GoBuiltin::named(name),
            _ => None,
        }
    }

    pub fn is_builtin(&self, builtin: GoBuiltin) -> bool {
        matches!(self, GoExpression::Identifier(name) if name == builtin.name())
    }

    pub fn is_one_of(&self, builtins: &[GoBuiltin]) -> bool {
        self.as_builtin().is_some_and(|builtin| builtins.contains(&builtin))
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, GoExpression::Identifier(name) if name == "nil")
    }
}
