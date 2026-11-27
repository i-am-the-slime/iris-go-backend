//! Names for the values the program leaves unnamed, such as a parameter that
//! every equation takes apart or a foreign's eta-expanded argument. Such a
//! value is called after its type, as a person would call it: a `Step a b` is
//! a `step`, a function is an `f`. A record is called after the Go name its
//! type ends up with, which only emission knows, so its name is a placeholder
//! until then.

use std::collections::BTreeMap;

use rustc_hash::{FxHashMap, FxHashSet};
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
            Monotype::Int64 | Monotype::UInt64 => "long",
            Monotype::Lazy(_) => "lazy",
            Monotype::ConsList(_) => "list",
            Monotype::HashMap(..) => "table",
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
    "any",
    "append",
    "bool",
    "byte",
    "cap",
    "clear",
    "close",
    "comparable",
    "complex",
    "complex64",
    "complex128",
    "copy",
    "delete",
    "error",
    "false",
    "float32",
    "float64",
    "imag",
    "int",
    "int8",
    "int16",
    "int32",
    "int64",
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
    "uint",
    "uint8",
    "uint16",
    "uint32",
    "uint64",
    "uintptr",
];

/// `LayoutTree` is `layoutTree`, `HTMLNode` is `htmlNode`, `URL` is `url`.
pub fn lower_camel(name: &str) -> String {
    let characters: Vec<char> =
        name.chars().filter(|character| character.is_alphanumeric() || *character == '_').collect();
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
    "int64",
    "uint32",
    "uint64",
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
    "eventloop",
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
    let mut sanitized = identifier_characters(name);
    if sanitized.is_empty() || sanitized.starts_with(|character: char| character.is_ascii_digit()) {
        sanitized.insert(0, '_');
    }
    if RESERVED.contains(&sanitized.as_str()) {
        sanitized.push('_');
    }
    sanitized
}

/// A name with each character a Go identifier cannot hold, as the prime of `xs'`, made `_`.
pub fn identifier_characters(name: &str) -> String {
    name.chars()
        .map(
            |character| {
                if character.is_alphanumeric() || character == '_' { character } else { '_' }
            },
        )
        .collect()
}

/// A label's or constructor's Go name, exported so that code in any package can use it: the
/// characters a Go identifier cannot hold become `_`, the first letter is upper case, and a name
/// that still does not start with an upper-case letter gets an `X` in front. `respondNow` is
/// `RespondNow`, `_respondNow` is `X_respondNow`, `content-type` is `Content_type`, `1st` is `X1st`.
/// Two labels can share a name; [`go_fields`] tells them apart.
pub fn go_field(label: &str) -> String {
    let sanitized: String = label.chars().map(identifier_character).collect();
    exported(&sanitized)
}

/// A character as a Go identifier holds it: a letter or digit as it is, anything else as `_`.
fn identifier_character(character: char) -> char {
    if character.is_alphabetic() || character.is_ascii_digit() { character } else { '_' }
}

/// The Go names of a type's labels, in their order, all different: when labels share a
/// [`go_field`], a label starting in lower case keeps it, one starting in upper case takes a `_`
/// behind it, and the others take the lowest number no label has, as `a` and `"A"` are `A` and
/// `A_`, and `content_type` and `"content-type"` are `Content_type` and `Content_type2`.
pub fn go_fields(labels: &[&str]) -> Vec<String> {
    let bases: Vec<String> = labels.iter().map(|label| go_field(label)).collect();
    let mut claims: Vec<usize> = (0..labels.len()).collect();
    claims.sort_by_key(|&index| (claim_rank(labels[index], &bases[index]), labels[index]));
    let mut names: Vec<Option<String>> = vec![None; labels.len()];
    let mut taken: FxHashSet<String> = FxHashSet::default();
    for &index in &claims {
        if taken.insert(bases[index].clone()) {
            names[index] = Some(bases[index].clone());
        }
    }
    for &index in &claims {
        if names[index].is_some() {
            continue;
        }
        let base = &bases[index];
        let unavailable =
            |name: &str| taken.contains(name) || bases.iter().any(|other| other == name);
        let suffixed = format!("{base}_");
        let starts_upper = labels[index].starts_with(char::is_uppercase);
        let name = if starts_upper && !unavailable(&suffixed) {
            suffixed
        } else {
            numbered(base, unavailable)
        };
        taken.insert(name.clone());
        names[index] = Some(name);
    }
    names.into_iter().map(|name| name.expect("invariant violated: a label left unnamed")).collect()
}

fn claim_rank(label: &str, base: &str) -> u8 {
    let starts_lower = label.starts_with(char::is_lowercase);
    let spelled = capitalise(label) == base;
    match (starts_lower, spelled) {
        (true, true) => 0,
        (true, false) => 1,
        (false, true) => 2,
        (false, false) => 3,
    }
}

pub fn renamed_label(label: &str, name: &str) -> Option<String> {
    (capitalise(label) != name).then(|| label.to_string())
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
    let is_upper_letter = |character: char| character.is_uppercase() && character.is_alphabetic();
    if capitalised.starts_with(is_upper_letter) { capitalised } else { format!("X{capitalised}") }
}

/// Parameter names that say nothing about what they hold.
const VAGUE_NAMES: &[&str] = &[
    "arg",
    "args",
    "argument",
    "acc",
    "accumulator",
    "dict",
    "input",
    "rec",
    "record",
    "result",
    "self",
    "this",
    "value",
    "values",
    "xs",
    "ys",
];

/// Whether an identifier is too vague to say what its value is.
pub fn is_vague(name: &str) -> bool {
    is_vaguely_spelled(name) || VAGUE_NAMES.contains(&name)
}

pub fn is_vaguely_spelled(name: &str) -> bool {
    name.len() < 3
        || !name.starts_with(|character: char| character.is_ascii_alphabetic())
        || name.ends_with(|character: char| character.is_ascii_digit())
        || name.contains('_')
}

/// `base`, else `base2`, `base3` and so on, the first that is not `taken`.
pub fn numbered(base: &str, mut taken: impl FnMut(&str) -> bool) -> String {
    let mut name = base.to_string();
    let mut counter = 2;
    while taken(&name) {
        name = format!("{base}{counter}");
        counter += 1;
    }
    name
}

/// The first candidate of each ladder that no other ladder wants, and that
/// `taken` allows. A collision moves every name in it one step up its ladder,
/// except that a name alone on the lowest step of the collision keeps it: a
/// name that grew into another's does not displace it. Names still colliding
/// at the top of their ladders, or whose ladders climb alike, are told apart
/// by a count, in ladder order.
pub fn resolve(ladders: &[Vec<String>], taken: &dyn Fn(&str) -> bool) -> Vec<String> {
    let mut steps = vec![0; ladders.len()];
    loop {
        let mut wanting: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
        for (index, ladder) in ladders.iter().enumerate() {
            wanting.entry(ladder[steps[index]].as_str()).or_default().push(index);
        }
        let mut climbed = false;
        for (name, indices) in &wanting {
            let forbidden = taken(name);
            if indices.len() == 1 && !forbidden {
                continue;
            }
            // Names that would climb alike stay as they are and are counted.
            let remaining = |index: usize| &ladders[index][steps[index]..];
            if !forbidden && indices.iter().all(|&index| remaining(index) == remaining(indices[0]))
            {
                continue;
            }
            let lowest = indices.iter().map(|&index| steps[index]).min().unwrap_or(0);
            let on_lowest = indices.iter().filter(|&&index| steps[index] == lowest).count();
            for &index in indices {
                let keeps = !forbidden && on_lowest == 1 && steps[index] == lowest;
                if !keeps && steps[index] + 1 < ladders[index].len() {
                    steps[index] += 1;
                    climbed = true;
                }
            }
        }
        if !climbed {
            break;
        }
    }
    let wanted = |index: usize| ladders[index][steps[index]].as_str();
    let mut wanting: FxHashMap<&str, usize> = FxHashMap::default();
    for index in 0..ladders.len() {
        *wanting.entry(wanted(index)).or_default() += 1;
    }
    let mut chosen: FxHashSet<String> = FxHashSet::default();
    let mut names: Vec<Option<String>> = vec![None; ladders.len()];
    for (index, slot) in names.iter_mut().enumerate() {
        let name = wanted(index);
        if wanting[name] == 1 && !taken(name) {
            chosen.insert(name.to_string());
            *slot = Some(name.to_string());
        }
    }
    let mut counted: Vec<usize> =
        (0..ladders.len()).filter(|&index| names[index].is_none()).collect();
    counted.sort_by_key(|&index| (steps[index], index));
    for index in counted {
        let base = wanted(index);
        let name = numbered(base, |name| taken(name) || chosen.contains(name));
        chosen.insert(name.clone());
        names[index] = Some(name);
    }
    names.into_iter().map(|name| name.expect("invariant violated: a ladder left unnamed")).collect()
}

/// A ladder without repeated candidates.
pub fn ladder(candidates: impl IntoIterator<Item = String>) -> Vec<String> {
    let mut ladder: Vec<String> = vec![];
    for candidate in candidates {
        if !candidate.is_empty() && !ladder.contains(&candidate) {
            ladder.push(candidate);
        }
    }
    ladder
}

#[cfg(test)]
mod tests {

    #[test]
    fn every_label_has_an_exported_go_name() {
        assert_eq!(go_field("respondNow"), "RespondNow");
        assert_eq!(go_field("_respondNow"), "X_respondNow");
        assert_eq!(go_field("1st"), "X1st");
        assert_eq!(go_field("content-type"), "Content_type");
        assert_eq!(go_field("über"), "Über");
        assert_eq!(go_field("名前"), "X名前");
        assert_eq!(go_field(""), "X");
        assert_eq!(go_field("Just"), "Just");
    }

    #[test]
    fn labels_that_share_a_go_name_are_numbered() {
        assert_eq!(
            go_fields(&["content-type", "content_type", "Content_type2"]),
            ["Content_type3", "Content_type", "Content_type2"]
        );
    }

    #[test]
    fn a_lower_case_label_keeps_its_plain_name() {
        assert_eq!(go_fields(&["A", "a"]), ["A_", "A"]);
        assert_eq!(go_fields(&["a", "A"]), ["A", "A_"]);
        assert_eq!(go_fields(&["A", "A2", "a"]), ["A_", "A2", "A"]);
        assert_eq!(go_fields(&["A2"]), ["A2"]);
        assert_eq!(go_fields(&["A2", "a2"]), ["A2_", "A2"]);
    }

    #[test]
    fn an_upper_case_label_whose_suffixed_name_is_taken_is_numbered() {
        assert_eq!(go_fields(&["A", "a", "a_"]), ["A2", "A", "A_"]);
        assert_eq!(go_fields(&["A", "A_", "a"]), ["A2", "A_", "A"]);
    }

    #[test]
    fn go_names_do_not_depend_on_label_order() {
        let labels = ["content-type", "content_type", "Content_type", "a", "A", "a_"];
        let names = go_fields(&labels);
        let mut reversed = labels;
        reversed.reverse();
        let mut reversed_names = go_fields(&reversed);
        reversed_names.reverse();
        assert_eq!(names, reversed_names);
    }

    #[test]
    fn a_label_its_go_name_does_not_spell_is_kept() {
        assert_eq!(renamed_label("title", "Title"), None);
        assert_eq!(renamed_label("A2", "A2"), None);
        assert_eq!(renamed_label("A", "A_").as_deref(), Some("A"));
        assert_eq!(renamed_label("content-type", "Content_type").as_deref(), Some("content-type"));
        assert_eq!(renamed_label("_id", "X_id").as_deref(), Some("_id"));
        assert_eq!(renamed_label("1st", "X1st").as_deref(), Some("1st"));
    }

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

    fn ladders(ladders: &[&[&str]]) -> Vec<Vec<String>> {
        ladders.iter().map(|ladder| ladder.iter().map(|name| name.to_string()).collect()).collect()
    }

    #[test]
    fn names_that_collide_with_nothing_stay_short() {
        let ladders = ladders(&[&["Timing", "EasingTiming"], &["Layout", "SpecLayout"]]);
        assert_eq!(resolve(&ladders, &|_| false), ["Timing", "Layout"]);
    }

    #[test]
    fn colliding_names_climb_until_they_differ() {
        let ladders = ladders(&[
            &["Timing", "EasingTiming", "TimingWithEasing"],
            &["Timing", "MainTiming", "TimingWithProbe"],
            &["Layout"],
        ]);
        assert_eq!(resolve(&ladders, &|_| false), ["EasingTiming", "MainTiming", "Layout"]);
    }

    #[test]
    fn a_name_that_grows_into_another_does_not_displace_it() {
        let ladders = ladders(&[
            &["Timing", "MainTiming"],
            &["Timing", "EasingTiming"],
            &["MainTiming", "MainTimingWithProbe"],
        ]);
        assert_eq!(
            resolve(&ladders, &|_| false),
            ["MainTiming2", "EasingTiming", "MainTiming"].map(String::from)
        );
    }

    #[test]
    fn names_that_would_climb_alike_are_counted_where_they_are() {
        let ladders =
            ladders(&[&["MaybeArgs", "MaybeRecordInput"], &["MaybeArgs", "MaybeRecordInput"]]);
        assert_eq!(resolve(&ladders, &|_| false), ["MaybeArgs", "MaybeArgs2"]);
    }

    #[test]
    fn taken_names_are_never_chosen() {
        let ladders = ladders(&[&["timing", "scheduleTiming"]]);
        assert_eq!(resolve(&ladders, &|name| name == "timing"), ["scheduleTiming"]);
    }
}
