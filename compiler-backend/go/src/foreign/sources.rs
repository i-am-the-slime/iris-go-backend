//! Go files next to a PureScript source implement its module's foreign imports, as `.js` files
//! do for the JavaScript backend: `Foo.go`, and further `Foo.<part>.go` files, beside
//! `Foo.purs`.

use std::io;
use std::path::{Path, PathBuf};

use super::{ForeignPackages, GoPackage};

/// The Go files next to a source file, in order of name. Go test files are left out.
pub fn foreign_files(source: &Path) -> io::Result<Vec<PathBuf>> {
    let (Some(directory), Some(stem)) =
        (source.parent(), source.file_stem().and_then(|stem| stem.to_str()))
    else {
        return Ok(vec![]);
    };
    let Ok(entries) = std::fs::read_dir(directory) else {
        return Ok(vec![]);
    };
    let mut names = vec![];
    for entry in entries {
        let entry = entry?;
        if entry.file_type()?.is_file()
            && let Ok(name) = entry.file_name().into_string()
        {
            names.push(name);
        }
    }
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    Ok(owned_files(stem, &names).into_iter().map(|name| directory.join(name)).collect())
}

/// A foreign file's Go source, with its package clause naming the package the generated code
/// imports. Authors may write any package name, such as `package ffi`.
pub fn foreign_source(module_name: &str, source: &str) -> String {
    let package = ForeignPackages::package_name(module_name);
    let mut renamed = false;
    let lines = source.split_inclusive('\n').map(|line| {
        if !renamed && line.starts_with("package ") {
            renamed = true;
            let ending = &line[line.trim_end().len()..];
            format!("package {package}{ending}")
        } else {
            line.to_string()
        }
    });
    lines.collect()
}

/// The structs a foreign file declares at its top level: `type Output struct {`. A struct named
/// like a record synonym of the module, `type Output = { stdout :: String }`, is that record's
/// Go representation: the generated code builds, reads and passes it as the struct, field
/// `stdout` as `Stdout`, instead of a struct of its own. Synonyms are transparent, so the struct
/// represents every record of exactly the synonym's fields.
pub fn foreign_structs(source: &str) -> Vec<String> {
    let mut structs = vec![];
    for line in source.lines() {
        let Some(rest) = line.strip_prefix("type ") else { continue };
        let mut words = rest.split_whitespace();
        let (Some(name), Some(kind)) = (words.next(), words.next()) else { continue };
        if kind.starts_with("struct")
            && name.chars().all(|character| character.is_alphanumeric() || character == '_')
        {
            structs.push(name.to_string());
        }
    }
    structs
}

/// The top-level names a foreign file declares: its functions, variables and constants, which
/// implement foreign imports, and its types, which represent foreign data. It reads declarations
/// at the start of a line, and in `var (`, `const (` and `type (` groups, as `gofmt` lays them out,
/// so a line inside a raw string literal that looks like a declaration counts as one.
pub fn foreign_declarations(source: &str) -> (Vec<String>, Vec<String>) {
    let (mut values, mut types) = (vec![], vec![]);
    let mut group: Option<&str> = None;
    for line in source.lines() {
        if let Some(keyword) = group {
            if line.starts_with(')') {
                group = None;
            } else if let Some(name) = line.strip_prefix('\t').and_then(leading_identifier) {
                let names = if keyword == "type" { &mut types } else { &mut values };
                names.push(name.to_string());
            }
            continue;
        }
        let Some((keyword, rest)) = line.split_once(' ') else { continue };
        match keyword {
            "var" | "const" | "type" if rest.starts_with('(') => group = Some(keyword),
            "func" | "var" | "const" => {
                if let Some(name) = leading_identifier(rest) {
                    values.push(name.to_string());
                }
            }
            "type" => {
                if let Some(name) = leading_identifier(rest) {
                    types.push(name.to_string());
                }
            }
            _ => {}
        }
    }
    (values, types)
}

/// The identifier a declaration starts with; a method's receiver is not one.
fn leading_identifier(text: &str) -> Option<&str> {
    let end = text
        .find(|character: char| !(character.is_alphanumeric() || character == '_'))
        .unwrap_or(text.len());
    (end > 0).then(|| &text[..end])
}

/// Of a directory's files, those that belong to the source `<stem>.purs`, in order of name:
/// `<stem>.go`, and `<stem>.<part>.go` unless `<stem>.<part>.purs`, a module of its own, owns it.
/// Go test files belong to no source.
fn owned_files<'n>(stem: &str, names: &[&'n str]) -> Vec<&'n str> {
    let mut owned: Vec<&str> = names
        .iter()
        .copied()
        .filter(|name| {
            let Some(part) = name.strip_prefix(stem).and_then(|rest| rest.strip_suffix(".go"))
            else {
                return false;
            };
            let is_test = name.ends_with("_test.go");
            let is_own_part = part.len() > 1
                && part.starts_with('.')
                && !names.contains(&format!("{stem}{part}.purs").as_str());
            (part.is_empty() || is_own_part) && !is_test
        })
        .collect();
    owned.sort();
    owned
}

pub fn foreign_forwarders(source: &str) -> Vec<(String, String)> {
    let value_receivers = value_receiver_methods(source);
    source
        .lines()
        .filter_map(|line| forwarder(line.trim_end(), &value_receivers))
        .collect()
}

fn forwarder(line: &str, value_receivers: &[&str]) -> Option<(String, String)> {
    let rest = line.strip_prefix("func ")?;
    let name = leading_identifier(rest)?;
    let mut rest = &rest[name.len()..];
    let mut type_parameters = vec![];
    if rest.starts_with('[') {
        let end = matching(rest, '[', ']')?;
        type_parameters = rest[1..end]
            .split(',')
            .filter_map(|entry| leading_identifier(entry.trim_start()))
            .collect();
        rest = &rest[end + 1..];
    }
    if !rest.starts_with('(') {
        return None;
    }
    let end = matching(rest, '(', ')')?;
    let parameters = parameters(&rest[1..end])?;
    let rest = &rest[end + 1..];
    let open = rest.find('{')?;
    if rest[..open].contains(['}', '(']) {
        return None;
    }
    let body = rest[open + 1..].strip_suffix('}')?.trim();
    let call = body.strip_prefix("return ").unwrap_or(body);
    let ((receiver, receiver_type), others) = parameters.split_first()?;
    let call = call.strip_prefix(*receiver)?.strip_prefix('.')?;
    let method = leading_identifier(call)?;
    let arguments = call[method.len()..].strip_prefix('(')?.strip_suffix(')')?;
    let arguments: Vec<&str> =
        arguments.split(',').map(str::trim).filter(|argument| !argument.is_empty()).collect();
    let forwarded = others.iter().map(|(name, _)| *name).eq(arguments.iter().copied());
    let typed_by_receiver = type_parameters
        .iter()
        .all(|parameter| mentions_word(receiver_type, parameter));
    let addressable = receiver_type.starts_with('*') || value_receivers.contains(&method);
    (forwarded && typed_by_receiver && addressable)
        .then(|| (name.to_string(), method.to_string()))
}

fn parameters(list: &str) -> Option<Vec<(&str, &str)>> {
    let mut parameters = vec![];
    let mut pending = vec![];
    let mut depth = 0;
    let mut start = 0;
    let mut entries = vec![];
    for (at, character) in list.char_indices() {
        match character {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                entries.push(list[start..at].trim());
                start = at + 1;
            }
            _ => {}
        }
    }
    entries.push(list[start..].trim());
    for entry in entries.into_iter().filter(|entry| !entry.is_empty()) {
        match entry.split_once(' ') {
            Some((name, type_)) => {
                for pending in pending.drain(..) {
                    parameters.push((pending, type_.trim()));
                }
                parameters.push((name, type_.trim()));
            }
            None => pending.push(entry),
        }
    }
    pending.is_empty().then_some(parameters)
}

fn value_receiver_methods(source: &str) -> Vec<&str> {
    source
        .lines()
        .filter_map(|line| {
            let receiver = line.strip_prefix("func (")?;
            let (receiver, rest) = receiver.split_once(')')?;
            let (_, type_) = receiver.trim().split_once(' ')?;
            (!type_.trim_start().starts_with('*')).then_some(())?;
            leading_identifier(rest.trim_start())
        })
        .collect()
}

fn matching(text: &str, open: char, close: char) -> Option<usize> {
    let mut depth = 0;
    for (at, character) in text.char_indices() {
        if character == open {
            depth += 1;
        } else if character == close {
            depth -= 1;
            if depth == 0 {
                return Some(at);
            }
        }
    }
    None
}

fn mentions_word(text: &str, word: &str) -> bool {
    text.split(|character: char| !(character.is_alphanumeric() || character == '_'))
        .any(|part| part == word)
}

pub fn recovers(source: &str) -> bool {
    source.contains("recover()")
}

pub fn uses_event_loop(source: &str) -> bool {
    let event_loop = format!("\"{}\"", GoPackage::EventLoop.path());
    source.lines().any(|line| {
        let line = line.trim();
        let line = line.strip_prefix("import").unwrap_or(line).trim();
        line == event_loop || line.split_once(' ').is_some_and(|(_, path)| path == event_loop)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_file_that_imports_the_event_loop_uses_it() {
        let grouped = "package ffi\n\nimport (\n\t\"sync\"\n\n\t\"github.com/i-am-the-slime/iris-go/eventloop\"\n)\n";
        let single = "package ffi\n\nimport \"github.com/i-am-the-slime/iris-go/eventloop\"\n";
        let aliased =
            "package ffi\n\nimport loop \"github.com/i-am-the-slime/iris-go/eventloop\"\n";
        let other = "package ffi\n\nimport \"github.com/i-am-the-slime/iris-go/exception\"\n";
        assert!(uses_event_loop(grouped));
        assert!(uses_event_loop(single));
        assert!(uses_event_loop(aliased));
        assert!(!uses_event_loop(other));
    }

    #[test]
    fn a_source_owns_its_go_file_and_its_parts() {
        let names = [
            "Parser.purs",
            "Parser.go",
            "Parser.grammar.go",
            "Parser_test.go",
            "Parser.grammar_test.go",
            "ParserState.go",
            "Parser.js",
        ];
        assert_eq!(owned_files("Parser", &names), ["Parser.go", "Parser.grammar.go"]);
    }

    #[test]
    fn a_dotted_module_owns_its_own_go_file() {
        let names = ["OrderPricing.purs", "OrderPricing.Input.purs", "OrderPricing.Input.go"];
        assert!(owned_files("OrderPricing", &names).is_empty());
        assert_eq!(owned_files("OrderPricing.Input", &names), ["OrderPricing.Input.go"]);
    }

    #[test]
    fn a_file_declares_its_top_level_structs() {
        let source = "package ffi\n\ntype Output struct {\n\tStdout string\n}\n\ntype Empty struct{}\n\ntype Mode int\n\ntype Pair[A any] struct{ First A }\n\nfunc f() {\n\ttype local struct{}\n}\n";
        assert_eq!(foreign_structs(source), ["Output", "Empty"]);
    }

    #[test]
    fn a_file_declares_its_top_level_names() {
        let source = "package ffi\n\nfunc Start() Stopwatch { return Stopwatch{} }\n\nfunc Repeat[A any](n int32, x A) []A { return nil }\n\nfunc (s Stopwatch) method() {}\n\nvar Seed int32 = 41\n\nconst (\n\tLimit = 3\n\tother = 4\n)\n\ntype Stopwatch struct{}\n\ntype (\n\tGoError = error\n)\n";
        let (values, types) = foreign_declarations(source);
        assert_eq!(values, ["Start", "Repeat", "Seed", "Limit", "other"]);
        assert_eq!(types, ["Stopwatch", "GoError"]);
    }

    #[test]
    fn a_foreign_that_calls_a_method_of_its_first_parameter_forwards_to_it() {
        let source = "package ffi

func (ref *ioref[A]) Load() A { return *ref.value.Load() }

func (box Box) Size() int32 { return 1 }

func ReadIORefImpl[A any](ref *ioref[A]) A { return ref.Load() }

func WriteIORefImpl[A any](ref *ioref[A], value A) { ref.Store(value) }

func SizeImpl(box Box) int32 { return box.Size() }

func ByPointer(box Box) int32 { return box.Grow() }

func Swapped[A any](ref *ioref[A], a, b A) { ref.Swap(b, a) }

func Mapped[A, B any](ref *ioref[A], f func(A) B) B { return ref.Map(f) }

func Longer[A any](ref *ioref[A]) A {
	return ref.Load()
}
";
        assert_eq!(
            foreign_forwarders(source),
            [
                ("ReadIORefImpl".to_string(), "Load".to_string()),
                ("WriteIORefImpl".to_string(), "Store".to_string()),
                ("SizeImpl".to_string(), "Size".to_string()),
            ]
        );
    }

    #[test]
    fn the_package_clause_names_the_imported_package() {
        let source = "// Event's foreigns.\npackage ffi\r\n\nimport \"sort\"\n";
        assert_eq!(
            foreign_source("FRP.Event", source),
            "// Event's foreigns.\npackage FRP_Event_ffi\r\n\nimport \"sort\"\n"
        );
    }
}
