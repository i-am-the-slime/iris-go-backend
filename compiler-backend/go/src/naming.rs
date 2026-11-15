//! Names for the values the program leaves unnamed, such as a parameter that
//! every equation takes apart or a foreign's eta-expanded argument. Such a
//! value is called after its type, as a person would call it: a `Step a b` is
//! a `step`, a function is an `f`. A record is called after the Go name its
//! type ends up with, which only emission knows, so its name is a placeholder
//! until then.

use smol_str::SmolStr;

use crate::monotype::{Monotype, MonotypeId, Monotypes};

/// The name of a value whose type is a record, until emission names it after
/// the record's Go type. No PureScript identifier can spell it.
pub const RECORD_VALUE: &str = "\u{1}record";

/// The name of a value that nothing, not even its type, names.
pub const UNNAMED_VALUE: &str = "argument";

/// The name of a value whose binder says nothing about it.
pub const VALUE: &str = "value";

impl Monotypes {
    /// What a value of the type is called when nothing names it.
    pub fn value_name(&self, monotype: MonotypeId) -> SmolStr {
        let name = match self.get(monotype) {
            Monotype::Int => "int",
            Monotype::Number => "number",
            Monotype::Boolean => "boolean",
            Monotype::Char => "char",
            Monotype::String => "string",
            Monotype::Unit => "unit",
            Monotype::Array(_) | Monotype::MutableArray(_) => "array",
            Monotype::Record(_) => return SmolStr::new_static(RECORD_VALUE),
            Monotype::Function(..) => "f",
            Monotype::Effect(_) => "effect",
            Monotype::Reference(_) => "ref",
            Monotype::Object(_) => "object",
            Monotype::Nullable(_) => "nullable",
            Monotype::Regex => "regex",
            Monotype::Mutex => "mutex",
            Monotype::BigInt => "bigInt",
            Monotype::Lazy(_) => "lazy",
            Monotype::Data(data) | Monotype::ForeignData(data) | Monotype::Recursive(data) => {
                match self.type_names.get(&(data.file_id, data.item)) {
                    Some(name) => return go_safe(&lower_camel(name)),
                    None => UNNAMED_VALUE,
                }
            }
            Monotype::Error => "error",
            Monotype::Opaque | Monotype::Erased(_) => UNNAMED_VALUE,
        };
        go_safe(name)
    }
}

/// A name Go leaves free for a local: a keyword or predeclared identifier
/// shortens to its initial, as `string` does to `s`.
pub fn go_safe(name: &str) -> SmolStr {
    if GO_PREDECLARED.contains(&name) {
        return SmolStr::from(&name[..1]);
    }
    SmolStr::from(name)
}

/// Go's keywords and predeclared identifiers, which no local may shadow
/// without changing what the code means or how it reads.
pub const GO_PREDECLARED: &[&str] = &[
    "break", "case", "chan", "const", "continue", "default", "defer", "else", "fallthrough",
    "for", "func", "go", "goto", "if", "import", "interface", "map", "package", "range",
    "return", "select", "struct", "switch", "type", "var", "any", "append", "bool", "byte",
    "cap", "clear", "close", "comparable", "complex", "complex64", "complex128", "copy",
    "delete", "error", "false", "float32", "float64", "imag", "int", "int8", "int16", "int32",
    "int64", "iota", "len", "make", "max", "min", "new", "nil", "panic", "print", "println",
    "real", "recover", "rune", "string", "true", "uint", "uint8", "uint16", "uint32", "uint64",
    "uintptr",
];

/// `LayoutTree` is `layoutTree`, `HTMLNode` is `htmlNode`, `URL` is `url`.
pub fn lower_camel(name: &str) -> String {
    let characters: Vec<char> = name.chars().filter(|c| c.is_alphanumeric() || *c == '_').collect();
    let leading = characters.iter().take_while(|character| character.is_uppercase()).count();
    let lowered = match leading {
        0 | 1 => leading,
        _ if leading == characters.len() => leading,
        // The last capital of a run starts the next word.
        _ if characters[leading].is_lowercase() => leading - 1,
        _ => leading,
    };
    characters
        .iter()
        .enumerate()
        .flat_map(|(index, character)| {
            let lower = index < lowered;
            let mut out: Vec<char> = vec![];
            if lower {
                out.extend(character.to_lowercase());
            } else {
                out.push(*character);
            }
            out
        })
        .collect()
}

/// Names a global or a package-level identifier must not take: Go's keywords and
/// predeclared names, and the packages the generated code imports.
pub const RESERVED: &[&str] = &[
    "break",
    "case",
    "chan",
    "const",
    "continue",
    "default",
    "defer",
    "else",
    "fallthrough",
    "for",
    "func",
    "go",
    "goto",
    "if",
    "import",
    "interface",
    "map",
    "package",
    "range",
    "return",
    "select",
    "struct",
    "switch",
    "type",
    "var",
    "append",
    "bool",
    "byte",
    "cap",
    "clear",
    "close",
    "complex",
    "copy",
    "delete",
    "error",
    "false",
    "float64",
    "imag",
    "int",
    "int32",
    "iota",
    "len",
    "make",
    "max",
    "min",
    "new",
    "nil",
    "panic",
    "print",
    "println",
    "real",
    "recover",
    "rune",
    "string",
    "true",
    "any",
    "main",
    "init",
    "fmt",
    "prim",
    "array",
    "direct",
    "object",
    "nullable",
    "exception",
    "aff",
    "promise",
    "foreignvalue",
    "regex",
    "sync",
    "big",
    "math",
    "slices",
    "Ref",
];

/// A name as a Go identifier: other characters become `_`, a digit start gets a
/// `_` in front and a reserved word one behind.
pub fn identifier(name: &str) -> String {
    let mut sanitized: String = name
        .chars()
        .map(
            |character| {
                if character.is_alphanumeric() || character == '_' { character } else { '_' }
            },
        )
        .collect();
    if sanitized.is_empty() || sanitized.starts_with(|character: char| character.is_ascii_digit()) {
        sanitized.insert(0, '_');
    }
    if RESERVED.contains(&sanitized.as_str()) {
        sanitized.push('_');
    }
    sanitized
}


/// The name with its first letter in upper case.
pub fn capitalise(text: &str) -> String {
    let mut characters = text.chars();
    match characters.next() {
        Some(first) => first.to_uppercase().chain(characters).collect(),
        None => String::new(),
    }
}

/// The name with its first letter in lower case.
pub fn lower_first(name: &str) -> String {
    let mut characters = name.chars();
    match characters.next() {
        Some(first) => first.to_lowercase().chain(characters).collect(),
        None => String::new(),
    }
}

/// A Go-exported spelling of a name.
pub fn exported(name: &str) -> String {
    let capitalised = capitalise(name);
    if capitalised.starts_with(char::is_uppercase) {
        capitalised
    } else {
        format!("X{capitalised}")
    }
}

/// Parameter names that say nothing about what they hold.
const VAGUE_NAMES: &[&str] = &[
    "arg", "args", "argument", "acc", "accumulator", "dict", "input", "rec", "record", "result",
    "self", "this", "value", "values", "xs", "ys",
];

/// Whether an identifier is too vague to say what its value is.
pub fn is_vague(name: &str) -> bool {
    name.len() < 3
        || !name.starts_with(|character: char| character.is_ascii_alphabetic())
        || name.ends_with(|character: char| character.is_ascii_digit())
        || name.contains('_')
        || VAGUE_NAMES.contains(&name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_names_are_lower_camel_case() {
        assert_eq!(lower_camel("Step"), "step");
        assert_eq!(lower_camel("LayoutTree"), "layoutTree");
        assert_eq!(lower_camel("HTMLNode"), "htmlNode");
        assert_eq!(lower_camel("URL"), "url");
        assert_eq!(lower_camel("Vec3"), "vec3");
    }

    #[test]
    fn go_keywords_and_predeclared_names_shorten_to_their_initial() {
        assert_eq!(go_safe("string"), "s");
        assert_eq!(go_safe("int"), "i");
        assert_eq!(go_safe("map"), "m");
        assert_eq!(go_safe("type"), "t");
        assert_eq!(go_safe("step"), "step");
    }
}
