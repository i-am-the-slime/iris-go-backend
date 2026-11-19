#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Primitive {
    MakeExists,
    RunExists,
}

pub fn known(module: &str, name: &str) -> Option<Primitive> {
    match (module, name) {
        ("Data.Exists", "mkExists") => Some(Primitive::MakeExists),
        ("Data.Exists", "runExists") => Some(Primitive::RunExists),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KnownType {
    Maybe,
}

pub fn known_type(module: &str, name: &str) -> Option<KnownType> {
    match (module, name) {
        ("Data.Maybe", "Maybe") => Some(KnownType::Maybe),
        _ => None,
    }
}
