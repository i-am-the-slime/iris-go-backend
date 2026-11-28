//! Go files next to a PureScript source implement its module's foreign imports, as `.js` files
//! do for the JavaScript backend: `Foo.go`, and further `Foo.<part>.go` files, beside
//! `Foo.purs`.

use std::io;
use std::path::{Path, PathBuf};

use super::{ForeignPackages, GoPackage};
use crate::syntax::tokens::{Token, TokenKind, closing, split_top, tokens};

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
    let tokens = code_tokens(source).unwrap_or_default();
    match tokens.as_slice() {
        [clause, name, ..] if clause.is_word("package") && name.word().is_some() => {
            format!("{}{package}{}", &source[..name.offset], &source[name.end()..])
        }
        _ => source.to_string(),
    }
}

/// The structs a foreign file declares at its top level: `type Output struct {`. A struct named
/// like a record synonym of the module, `type Output = { stdout :: String }`, is that record's
/// Go representation: the generated code builds, reads and passes it as the struct, field
/// `stdout` as `Stdout`, instead of a struct of its own. Synonyms are transparent, so the struct
/// represents every record of exactly the synonym's fields.
pub fn foreign_structs(source: &str) -> Vec<String> {
    let tokens = code_tokens(source).unwrap_or_default();
    let structs = split_top(&tokens, ";").into_iter().filter_map(|declaration| match declaration {
        [keyword, name, kind, ..] if keyword.is_word("type") && kind.is_word("struct") => {
            name.word()
        }
        _ => None,
    });
    structs.map(str::to_string).collect()
}

/// The top-level names a foreign file declares: its functions, variables and constants, which
/// implement foreign imports, and its types, which represent foreign data. It reads declarations
/// at the start of a line, and in `var (`, `const (` and `type (` groups.
pub fn foreign_declarations(source: &str) -> (Vec<String>, Vec<String>) {
    let (mut values, mut types) = (vec![], vec![]);
    let tokens = code_tokens(source).unwrap_or_default();
    for declaration in split_top(&tokens, ";") {
        let Some((keyword, rest)) = declaration.split_first() else { continue };
        let names = match keyword.word() {
            Some("func" | "var" | "const") => &mut values,
            Some("type") => &mut types,
            _ => continue,
        };
        match rest {
            [open, ..] if open.is("(") && !keyword.is_word("func") => {
                names.extend(grouped_names(rest));
            }
            [name, ..] => names.extend(name.word().map(str::to_string)),
            [] => {}
        }
    }
    (values, types)
}

fn grouped_names(group: &[Token]) -> Vec<String> {
    let Some(close) = closing(group, 0) else { return vec![] };
    let specifications = split_top(&group[1..close], ";").into_iter();
    let names = specifications.filter_map(|specification| specification.first()?.word());
    names.map(str::to_string).collect()
}

fn code_tokens(source: &str) -> Option<Vec<Token<'_>>> {
    let tokens = tokens(source).ok()?;
    Some(tokens.into_iter().filter(|token| !token.is_comment()).collect())
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

/// What a foreign that only hands its parameters on is called as.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Forward {
    /// `p0.Method(p1, …)`: a method of its first parameter.
    Method(String),
    MethodOfCopy(String),
    /// `Function(p0, p1, …)`: another function of its package, of the same signature.
    Function(String),
}

/// The foreigns of a file that only forward to a method or a function, which the generated code
/// calls in their place: `func ReadIORefImpl[A any](ref *ioref[A]) A { return ref.Load() }`,
/// `func NewIORefImpl[A any](value A) *ioref[A] { return New(value) }`, and the method expression
/// `var ValueImpl = TextInput.Value` of a type the file declares.
pub fn foreign_forwarders(source: &str) -> Vec<(String, Forward)> {
    let (_, types) = foreign_declarations(source);
    let tokens = code_tokens(source).unwrap_or_default();
    let declarations = split_top(&tokens, ";");
    let value_receivers = declarations.iter().copied().filter_map(value_receiver_method);
    let value_receivers: Vec<&str> = value_receivers.collect();
    let headers = declarations.iter().filter_map(|declaration| header(source, declaration));
    let headers: Vec<Header> = headers.collect();
    let calls = headers.iter().filter_map(|function| {
        let forward = method_forwarder(function, &value_receivers)
            .or_else(|| function_forwarder(function, &headers))?;
        Some((function.name.to_string(), forward))
    });
    let method_expressions = declarations.iter().map(|tokens| method_expression(tokens, &types));
    calls.chain(method_expressions.flatten()).collect()
}

struct Header<'t, 's> {
    name: &'s str,
    type_parameters: &'t [Token<'s>],
    parameters: Vec<(&'s str, &'t [Token<'s>])>,
    results: &'t [Token<'s>],
    body: Option<&'t [Token<'s>]>,
}

fn header<'t, 's>(source: &str, declaration: &'t [Token<'s>]) -> Option<Header<'t, 's>> {
    let [keyword, name, ..] = declaration else { return None };
    let name = name.word().filter(|_| keyword.is_word("func"))?;
    let mut rest = &declaration[2..];
    let mut type_parameters: &[Token] = &[];
    if rest.first()?.is("[") {
        let end = closing(rest, 0)?;
        type_parameters = &rest[1..end];
        rest = &rest[end + 1..];
    }
    if !rest.first()?.is("(") {
        return None;
    }
    let end = closing(rest, 0)?;
    let parameters = parameters(&rest[1..end])?;
    let rest = &rest[end + 1..];
    let open = rest.iter().position(|token| token.is("{"))?;
    let results = &rest[..open];
    if results.iter().any(|token| token.is("}") || token.is("(")) {
        return None;
    }
    let last = declaration.last()?;
    let on_one_line = !source[keyword.offset..last.end()].contains('\n');
    let body = closing(rest, open)
        .filter(|&close| on_one_line && close == rest.len() - 1)
        .map(|close| &rest[open + 1..close]);
    Some(Header { name, type_parameters, parameters, results, body })
}

fn method_forwarder(function: &Header, value_receivers: &[&str]) -> Option<Forward> {
    let ((receiver, receiver_type), others) = function.parameters.split_first()?;
    let [object, dot, method, arguments @ ..] = forwarded_call(function)? else { return None };
    if !(object.is_word(receiver) && dot.is(".")) {
        return None;
    }
    let method = method.word()?;
    let forwarded = forwards_parameters(arguments, others);
    let typed_by_receiver = type_parameter_names(function.type_parameters)
        .all(|parameter| receiver_type.iter().any(|token| token.is_word(parameter)));
    if !(forwarded && typed_by_receiver) {
        return None;
    }
    let by_pointer = receiver_type.first().is_some_and(|token| token.is("*"));
    match by_pointer || value_receivers.contains(&method) {
        true => Some(Forward::Method(method.to_string())),
        false => Some(Forward::MethodOfCopy(method.to_string())),
    }
}

fn function_forwarder(function: &Header, headers: &[Header]) -> Option<Forward> {
    let (callee, arguments) = forwarded_call(function)?.split_first()?;
    let callee = callee.word()?;
    let exported = callee.starts_with(|character: char| character.is_uppercase());
    let arguments = strip_own_type_arguments(arguments, function.type_parameters);
    let forwarded = forwards_parameters(arguments, &function.parameters);
    let same_signature = |other: &Header| {
        other.name == callee
            && spelling(other.type_parameters) == spelling(function.type_parameters)
            && spelling(other.results) == spelling(function.results)
            && parameter_types(other) == parameter_types(function)
    };
    let declared = headers.iter().any(same_signature);
    (exported && callee != function.name && forwarded && declared)
        .then(|| Forward::Function(callee.to_string()))
}

/// `[A, B](…)` to `(…)` when the type arguments are the function's own type parameters, in order,
/// as a call that can't infer them spells them.
fn strip_own_type_arguments<'t, 's>(
    call: &'t [Token<'s>],
    type_parameters: &[Token<'s>],
) -> &'t [Token<'s>] {
    if !call.first().is_some_and(|open| open.is("[")) {
        return call;
    }
    let Some(end) = closing(call, 0) else { return call };
    let arguments = split_top(&call[1..end], ",").into_iter().map(single_word);
    let own = arguments.eq(type_parameter_names(type_parameters).map(Some));
    if own { &call[end + 1..] } else { call }
}

fn forwarded_call<'t, 's>(function: &Header<'t, 's>) -> Option<&'t [Token<'s>]> {
    match function.body? {
        [keyword, call @ ..] if keyword.is_word("return") => Some(call),
        body => Some(body),
    }
}

fn forwards_parameters(arguments: &[Token], parameters: &[(&str, &[Token])]) -> bool {
    let parenthesized = arguments.first().is_some_and(|open| open.is("("))
        && closing(arguments, 0).is_some_and(|close| close + 1 == arguments.len());
    if !parenthesized {
        return false;
    }
    let arguments = split_top(&arguments[1..arguments.len() - 1], ",").into_iter().map(single_word);
    parameters.iter().map(|(name, _)| Some(*name)).eq(arguments)
}

/// `var ValueImpl = TextInput.Value`: a method expression of a type the file declares takes its
/// receiver first, and Go only allows it for a method that a value of the type has, so the
/// generated code can call the method on any value of the type.
fn method_expression(declaration: &[Token], types: &[String]) -> Option<(String, Forward)> {
    let [keyword, name, assign, type_, dot, method] = declaration else { return None };
    if !(keyword.is_word("var") && assign.is("=") && dot.is(".")) {
        return None;
    }
    let (name, type_, method) = (name.word()?, type_.word()?, method.word()?);
    types
        .iter()
        .any(|declared| declared == type_)
        .then(|| (name.to_string(), Forward::Method(method.to_string())))
}

fn parameters<'t, 's>(list: &'t [Token<'s>]) -> Option<Vec<(&'s str, &'t [Token<'s>])>> {
    let mut parameters = vec![];
    let mut pending = vec![];
    for entry in split_top(list, ",") {
        match entry {
            [name, type_start, ..] if name.word().is_some() && type_start.offset > name.end() => {
                let type_ = &entry[1..];
                parameters.extend(pending.drain(..).map(|pending| (pending, type_)));
                parameters.push((name.text, type_));
            }
            [name] => pending.push(name.word()?),
            _ => return None,
        }
    }
    pending.is_empty().then_some(parameters)
}

fn value_receiver_method<'s>(declaration: &[Token<'s>]) -> Option<&'s str> {
    let [keyword, open, ..] = declaration else { return None };
    if !(keyword.is_word("func") && open.is("(")) {
        return None;
    }
    let close = closing(declaration, 1)?;
    let [receiver, receiver_type, ..] = &declaration[2..close] else { return None };
    if receiver.word().is_none() || receiver_type.is("*") {
        return None;
    }
    declaration.get(close + 1)?.word()
}

fn type_parameter_names<'t, 's>(
    type_parameters: &'t [Token<'s>],
) -> impl Iterator<Item = &'s str> + 't {
    let entries = split_top(type_parameters, ",").into_iter();
    entries.filter_map(|entry| entry.first()?.word())
}

fn parameter_types<'s>(header: &Header<'_, 's>) -> Vec<Vec<&'s str>> {
    header.parameters.iter().map(|(_, type_)| spelling(type_)).collect()
}

fn single_word<'s>(tokens: &[Token<'s>]) -> Option<&'s str> {
    match tokens {
        [token] => token.word(),
        _ => None,
    }
}

fn spelling<'s>(tokens: &[Token<'s>]) -> Vec<&'s str> {
    tokens.iter().map(|token| token.text).collect()
}

pub fn recovers(source: &str) -> bool {
    let Some(tokens) = code_tokens(source) else { return true };
    tokens.iter().enumerate().any(|(index, token)| {
        let called = tokens.get(index + 1).is_some_and(|next| next.is("("));
        let selected = index > 0 && tokens[index - 1].is(".");
        token.is_word("recover") && called && !selected
    })
}

pub fn uses_event_loop(source: &str) -> bool {
    let event_loop = format!("\"{}\"", GoPackage::EventLoop.path());
    let tokens = code_tokens(source).unwrap_or_default();
    let imports = split_top(&tokens, ";")
        .into_iter()
        .filter(|declaration| declaration.first().is_some_and(|keyword| keyword.is_word("import")));
    let mut paths = imports.flatten().filter(|token| token.kind == TokenKind::Literal);
    paths.any(|path| path.text == event_loop)
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
    fn declarations_inside_comments_and_strings_are_not_declared() {
        let source = "package ffi\n\n// type Commented struct{}\n\n/*\nfunc Hidden() {}\n*/\n\nvar Usage = `\ntype Quoted struct{}\nfunc Quoted() {}\n`\n\ntype Real struct{}\n";
        assert_eq!(foreign_structs(source), ["Real"]);
        let (values, types) = foreign_declarations(source);
        assert_eq!(values, ["Usage"]);
        assert_eq!(types, ["Real"]);
    }

    #[test]
    fn a_file_recovers_only_where_it_calls_recover() {
        let mentions = "package ffi\n\n// recover() is never called here.\nvar message = \"recover()\"\n\nfunc Run(state Machine) { state.recover() }\n";
        let calls = "package ffi\n\nfunc Safely(run func()) {\n\tdefer func() { recover () }()\n\trun()\n}\n";
        assert!(!recovers(mentions));
        assert!(recovers(calls));
    }

    #[test]
    fn a_forwarder_may_end_with_a_comment() {
        let source = "package ffi\n\nfunc New[A any](value A) *ioref[A] { return &ioref[A]{} }\n\nfunc NewImpl[A any](value A) *ioref[A] { return New(value) } // keeps New's type\n";
        assert_eq!(
            foreign_forwarders(source),
            [("NewImpl".to_string(), Forward::Function("New".to_string()))]
        );
    }

    #[test]
    fn the_event_loop_is_used_only_where_it_is_imported() {
        let mentioned = "package ffi\n\n// import \"github.com/i-am-the-slime/iris-go/eventloop\"\nvar path = `\n\"github.com/i-am-the-slime/iris-go/eventloop\"\n`\n";
        assert!(!uses_event_loop(mentioned));
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
                ("ReadIORefImpl".to_string(), Forward::Method("Load".to_string())),
                ("WriteIORefImpl".to_string(), Forward::Method("Store".to_string())),
                ("SizeImpl".to_string(), Forward::Method("Size".to_string())),
                ("ByPointer".to_string(), Forward::MethodOfCopy("Grow".to_string())),
            ]
        );
    }

    #[test]
    fn a_foreign_that_calls_a_function_of_the_same_signature_forwards_to_it() {
        let source = "package ffi

func New[A any](value A) *ioref[A] {
	ref := &ioref[A]{}
	ref.value.Store(&value)
	return ref
}

func NewIORefImpl[A any](value A) *ioref[A] { return New(value) }

func Wider[A any](value A) IORef[A] { return New(value) }

func Hidden[A any](value A) *ioref[A] { return newIORef(value) }

func newIORef[A any](value A) *ioref[A] { return &ioref[A]{} }

func Imported(text string) string { return Upper(text) }

func Fresh[A, B any]() *pair[A, B] { return &pair[A, B]{} }

func FreshImpl[A, B any]() *pair[A, B] { return Fresh[A, B]() }

func SwappedImpl[A, B any]() *pair[A, B] { return Fresh[B, A]() }
";
        assert_eq!(
            foreign_forwarders(source),
            [
                ("NewIORefImpl".to_string(), Forward::Function("New".to_string())),
                ("FreshImpl".to_string(), Forward::Function("Fresh".to_string())),
            ]
        );
    }

    #[test]
    fn a_method_expression_of_a_declared_type_forwards_to_the_method() {
        let source = "package ffi

type TextInput = textinput.Model

var ValueImpl = TextInput.Value

var BlinkImpl tea.Cmd = textinput.Blink

var ViewImpl = textinput.Model.View

var Upper = strings.ToUpper
";
        assert_eq!(
            foreign_forwarders(source),
            [("ValueImpl".to_string(), Forward::Method("Value".to_string()))]
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
