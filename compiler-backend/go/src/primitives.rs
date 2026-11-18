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
