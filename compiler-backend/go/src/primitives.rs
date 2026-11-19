#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Primitive {
    MakeExists,
    RunExists,
    Inject,
    On,
    Default,
    Case,
    Expand,
    Match,
    OnMatch,
    ReifyType,
}

pub fn known(module: &str, name: &str) -> Option<Primitive> {
    match (module, name) {
        ("Data.Exists", "mkExists") => Some(Primitive::MakeExists),
        ("Data.Exists", "runExists") => Some(Primitive::RunExists),
        ("Data.Variant", "inj") => Some(Primitive::Inject),
        ("Data.Variant", "on") => Some(Primitive::On),
        ("Data.Variant", "default") => Some(Primitive::Default),
        ("Data.Variant", "case_") => Some(Primitive::Case),
        ("Data.Variant", "expand") => Some(Primitive::Expand),
        ("Data.Variant", "match") => Some(Primitive::Match),
        ("Data.Variant", "onMatch") => Some(Primitive::OnMatch),
        ("Data.Reflectable", "reifyType") => Some(Primitive::ReifyType),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KnownType {
    Maybe,
    Variant,
    /// Control.Monad.Free's `Val`, the constructorless type that stands for the
    /// result of every step a `Free` hides behind `unsafeCoerce`.
    FreeValue,
}

pub fn known_type(module: &str, name: &str) -> Option<KnownType> {
    match (module, name) {
        ("Data.Maybe", "Maybe") => Some(KnownType::Maybe),
        ("Data.Variant", "Variant") => Some(KnownType::Variant),
        ("Control.Monad.Free", "Val") => Some(KnownType::FreeValue),
        _ => None,
    }
}
