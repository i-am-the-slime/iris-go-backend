use std::fmt;
use std::ops::Range;

use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Debug, Clone, Default)]
pub struct Opacity {
    pub functions: Vec<OpaqueDeclaration>,
    pub types: Vec<OpaqueDeclaration>,
    pub unreadable: Option<String>,
    pub called_in_place: FxHashMap<String, Vec<usize>>,
    /// The shapes of each function's value parameters and of its one result.
    pub signatures: FxHashMap<String, ForeignSignature>,
}

/// What a foreign function's signature says about its values, in terms of its type parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForeignSignature {
    pub parameters: Vec<ForeignShape>,
    pub result: ForeignShape,
}

/// The shape of a type in a foreign signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForeignShape {
    /// A type parameter itself, `A`.
    Parameter(String),
    /// A type that holds values of one type parameter and nothing else of the caller's:
    /// `*ioref[A]`, `[]A`, `chan A`.
    Holder(String),
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpaqueDeclaration {
    pub name: String,
    pub parameters: Vec<String>,
    pub escapes: Vec<Escape>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Escape {
    pub parameter: Option<String>,
    pub reason: String,
}

impl fmt::Display for Escape {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.parameter {
            Some(parameter) => write!(formatter, "type parameter {parameter} {}", self.reason),
            None => write!(formatter, "it {}", self.reason),
        }
    }
}

impl Opacity {
    pub fn function(&self, name: &str) -> Option<&OpaqueDeclaration> {
        self.functions.iter().find(|function| function.name == name)
    }

    pub fn data_type(&self, name: &str) -> Option<&OpaqueDeclaration> {
        self.types.iter().find(|declaration| declaration.name == name)
    }
}

pub fn foreign_opacity(sources: &[&str]) -> Opacity {
    let mut package = Package::default();
    for source in sources {
        match tokens(source) {
            Ok(tokens) => package.read(&tokens),
            Err(reason) => return Opacity { unreadable: Some(reason), ..Opacity::default() },
        }
    }
    package.opacity()
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Word(String),
    Literal,
    Symbol(&'static str),
}

impl Token {
    fn is(&self, symbol: &str) -> bool {
        matches!(self, Token::Symbol(own) if *own == symbol)
    }

    fn word(&self) -> Option<&str> {
        match self {
            Token::Word(word) => Some(word),
            _ => None,
        }
    }

    fn is_word(&self, word: &str) -> bool {
        self.word() == Some(word)
    }

    fn is_keyword(&self) -> bool {
        self.word().is_some_and(|word| KEYWORDS.contains(&word))
    }

    fn is_opening(&self) -> bool {
        self.is("(") || self.is("[") || self.is("{")
    }

    fn is_closing(&self) -> bool {
        self.is(")") || self.is("]") || self.is("}")
    }
}

const KEYWORDS: &[&str] = &[
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
];

const STATEMENT_ENDING_KEYWORDS: &[&str] = &["break", "continue", "fallthrough", "return"];

const SYMBOLS: &[&str] = &[
    "<<=", ">>=", "&^=", "...", "&&", "||", "<-", "++", "--", "==", "!=", "<=", ">=", ":=", "+=",
    "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "&^", "+", "-", "*", "/", "%", "&", "|",
    "^", "<", ">", "=", "!", "(", ")", "[", "]", "{", "}", ",", ";", ".", ":", "~",
];

const ASSIGNMENTS: &[&str] =
    &["=", ":=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "&^="];

const ESCAPING_WORDS: &[&str] = &["any", "interface", "reflect", "unsafe"];

const OPAQUE_GENERIC_PACKAGES: &[&str] = &["atomic", "iter", "unique", "weak"];

const BUILTINS: &[&str] =
    &["append", "cap", "clear", "close", "copy", "delete", "len", "make", "max", "min", "new"];

const COUNTING_BUILTINS: &[&str] = &["len", "cap"];

const GENERIC_PACKAGES: &[&str] = &["slices", "maps"];

const HEADER_KEYWORDS: &[&str] = &["if", "for", "switch", "select", "else"];

const TYPE_KEYWORDS: &[&str] = &["map", "chan", "struct", "func"];

fn tokens(source: &str) -> Result<Vec<Token>, String> {
    let characters: Vec<char> = source.chars().collect();
    let mut tokens = vec![];
    let mut position = 0;
    while let Some(&character) = characters.get(position) {
        let next = characters.get(position + 1).copied();
        if character == '\n' {
            end_line(&mut tokens);
            position += 1;
        } else if character.is_whitespace() {
            position += 1;
        } else if character == '/' && next == Some('/') {
            while characters.get(position).is_some_and(|&character| character != '\n') {
                position += 1;
            }
        } else if character == '/' && next == Some('*') {
            let end = comment_end(&characters, position + 2)
                .ok_or_else(|| "an unterminated comment".to_string())?;
            if characters[position..end].contains(&'\n') {
                end_line(&mut tokens);
            }
            position = end;
        } else if matches!(character, '"' | '\'' | '`') {
            position = literal_end(&characters, position)?;
            tokens.push(Token::Literal);
        } else if character.is_alphabetic() || character == '_' {
            let start = position;
            while characters
                .get(position)
                .is_some_and(|&character| character.is_alphanumeric() || character == '_')
            {
                position += 1;
            }
            tokens.push(Token::Word(characters[start..position].iter().collect()));
        } else if character.is_ascii_digit()
            || (character == '.' && next.is_some_and(|next| next.is_ascii_digit()))
        {
            position = number_end(&characters, position);
            tokens.push(Token::Literal);
        } else {
            let symbol = SYMBOLS.iter().find(|symbol| {
                symbol
                    .chars()
                    .enumerate()
                    .all(|(offset, expected)| characters.get(position + offset) == Some(&expected))
            });
            let symbol = symbol.ok_or_else(|| format!("an unexpected `{character}`"))?;
            position += symbol.len();
            tokens.push(Token::Symbol(symbol));
        }
    }
    end_line(&mut tokens);
    Ok(tokens)
}

fn end_line(tokens: &mut Vec<Token>) {
    let ends_statement = match tokens.last() {
        Some(Token::Word(word)) => {
            !KEYWORDS.contains(&word.as_str()) || STATEMENT_ENDING_KEYWORDS.contains(&word.as_str())
        }
        Some(Token::Literal) => true,
        Some(Token::Symbol(symbol)) => [")", "]", "}", "++", "--"].contains(symbol),
        None => false,
    };
    if ends_statement {
        tokens.push(Token::Symbol(";"));
    }
}

fn comment_end(characters: &[char], start: usize) -> Option<usize> {
    let mut position = start;
    while position + 1 < characters.len() {
        if characters[position] == '*' && characters[position + 1] == '/' {
            return Some(position + 2);
        }
        position += 1;
    }
    None
}

fn literal_end(characters: &[char], start: usize) -> Result<usize, String> {
    let quote = characters[start];
    let mut position = start + 1;
    while let Some(&character) = characters.get(position) {
        if character == quote {
            return Ok(position + 1);
        }
        if quote != '`' && character == '\n' {
            break;
        }
        position += if quote != '`' && character == '\\' { 2 } else { 1 };
    }
    Err("an unterminated literal".to_string())
}

fn number_end(characters: &[char], start: usize) -> usize {
    let mut position = start;
    while let Some(&character) = characters.get(position) {
        let exponent_sign = matches!(character, '+' | '-')
            && position > start
            && matches!(characters[position - 1], 'e' | 'E' | 'p' | 'P');
        if character.is_alphanumeric() || matches!(character, '_' | '.') || exponent_sign {
            position += 1;
        } else {
            break;
        }
    }
    position
}

fn closing(tokens: &[Token], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate().skip(open) {
        if token.is_opening() {
            depth += 1;
        } else if token.is_closing() {
            depth = depth.checked_sub(1)?;
            if depth == 0 {
                return Some(index);
            }
        }
    }
    None
}

fn opening(tokens: &[Token], close: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate().take(close + 1).rev() {
        if token.is_closing() {
            depth += 1;
        } else if token.is_opening() {
            depth = depth.checked_sub(1)?;
            if depth == 0 {
                return Some(index);
            }
        }
    }
    None
}

fn split_top<'t>(tokens: &'t [Token], separator: &str) -> Vec<&'t [Token]> {
    let mut parts = vec![];
    let mut depth = 0usize;
    let mut start = 0;
    for (index, token) in tokens.iter().enumerate() {
        if token.is_opening() {
            depth += 1;
        } else if token.is_closing() {
            depth = depth.saturating_sub(1);
        } else if depth == 0 && token.is(separator) {
            parts.push(&tokens[start..index]);
            start = index + 1;
        }
    }
    parts.push(&tokens[start..]);
    parts.into_iter().filter(|part| !part.is_empty()).collect()
}

fn mentions(tokens: &[Token], word: &str) -> bool {
    tokens.iter().any(|token| token.is_word(word))
}

fn mentioned<'t>(tokens: &'t [Token], words: &FxHashSet<String>) -> Option<&'t str> {
    tokens.iter().filter_map(Token::word).find(|word| words.contains(*word))
}

/// The first type of another package the tokens name, other than one that only holds its type
/// parameter or nothing of the caller's at all.
fn qualified(tokens: &[Token]) -> Option<String> {
    tokens.windows(3).find_map(|window| match window {
        [Token::Word(package), dot, Token::Word(name)] if dot.is(".") => {
            let spelled = format!("{package}.{name}");
            (!PARAMETRIC_TYPES.contains(&spelled.as_str())).then_some(spelled)
        }
        _ => None,
    })
}

/// Standard library types that never look at a value of their type parameter, if they have one:
/// `atomic.Pointer[A]` only swaps a `*A`, and a mutex guards whatever is next to it. A foreign
/// type built from them keeps its values' Go types, `IORef[[]Book]` rather than `IORef[any]`.
const PARAMETRIC_TYPES: &[&str] = &[
    "atomic.Pointer",
    "atomic.Bool",
    "atomic.Int32",
    "atomic.Int64",
    "atomic.Uint32",
    "atomic.Uint64",
    "sync.Mutex",
    "sync.RWMutex",
    "sync.Once",
    "sync.WaitGroup",
];

/// What a value of the `PARAMETRIC_TYPES` is asked to do with a value of its type parameter:
/// keep it and hand it back, never look into it.
const PARAMETRIC_METHODS: &[&str] = &["Load", "Store", "Swap", "CompareAndSwap"];

fn qualified_instantiation(tokens: &[Token]) -> Option<String> {
    tokens.windows(4).find_map(|window| match window {
        [Token::Word(package), dot, Token::Word(name), open]
            if dot.is(".")
                && open.is("[")
                && !OPAQUE_GENERIC_PACKAGES.contains(&package.as_str()) =>
        {
            Some(format!("{package}.{name}"))
        }
        _ => None,
    })
}

fn spelled(tokens: &[Token]) -> String {
    let mut text = String::new();
    for token in tokens {
        match token {
            Token::Word(word) => {
                if text.ends_with(|character: char| character.is_alphanumeric()) {
                    text.push(' ');
                }
                text.push_str(word);
            }
            Token::Literal => text.push('…'),
            Token::Symbol(symbol) => text.push_str(symbol),
        }
    }
    text
}

struct TypeParameter {
    name: String,
    constraint: Vec<Token>,
}

impl TypeParameter {
    fn is_unconstrained(&self) -> bool {
        match self.constraint.as_slice() {
            [word] => word.is_word("any"),
            [interface, open, close] => {
                interface.is_word("interface") && open.is("{") && close.is("}")
            }
            _ => false,
        }
    }
}

struct Function {
    name: String,
    type_parameters: Vec<TypeParameter>,
    parameters: Vec<Token>,
    results: Vec<Token>,
    body: Option<Vec<Token>>,
}

struct TypeDeclaration {
    name: String,
    type_parameters: Vec<TypeParameter>,
    definition: Vec<Token>,
}

#[derive(Default)]
struct Package {
    functions: Vec<Function>,
    types: Vec<TypeDeclaration>,
    methods: FxHashSet<String>,
    method_functions: Vec<Function>,
}

impl Package {
    fn read(&mut self, tokens: &[Token]) {
        for declaration in split_top(tokens, ";") {
            match declaration.first().and_then(Token::word) {
                Some("func") => self.read_function(&declaration[1..]),
                Some("type") if declaration.get(1).is_some_and(|token| token.is("(")) => {
                    let Some(end) = closing(declaration, 1) else { continue };
                    for specification in split_top(&declaration[2..end], ";") {
                        self.read_type(specification);
                    }
                }
                Some("type") => self.read_type(&declaration[1..]),
                _ => {}
            }
        }
    }

    fn read_function(&mut self, declaration: &[Token]) {
        if declaration.first().is_some_and(|token| token.is("(")) {
            self.read_method(declaration);
            return;
        }
        let Some(name) = declaration.first().and_then(Token::word) else { return };
        let mut position = 1;
        let mut type_parameters = vec![];
        if declaration.get(1).is_some_and(|token| token.is("[")) {
            let Some(end) = closing(declaration, 1) else { return };
            type_parameters = read_type_parameters(&declaration[2..end]);
            position = end + 1;
        }
        if let Some(function) =
            read_signature(name, type_parameters, vec![], &declaration[position..])
        {
            self.functions.push(function);
        }
    }

    fn read_method(&mut self, declaration: &[Token]) {
        let Some(receiver_end) = closing(declaration, 0) else { return };
        let Some(name) = declaration.get(receiver_end + 1).and_then(Token::word) else { return };
        self.methods.insert(name.to_string());
        let receiver = &declaration[1..receiver_end];
        let type_parameters = match receiver.iter().position(|token| token.is("[")) {
            Some(open) => {
                let Some(close) = closing(receiver, open) else { return };
                let names = receiver[open + 1..close].iter().filter_map(Token::word);
                let unconstrained = |name: &str| TypeParameter {
                    name: name.to_string(),
                    constraint: vec![Token::Word("any".to_string())],
                };
                names.map(unconstrained).collect()
            }
            None => vec![],
        };
        let rest = &declaration[receiver_end + 2..];
        if let Some(method) = read_signature(name, type_parameters, receiver.to_vec(), rest) {
            self.method_functions.push(method);
        }
    }

    fn read_type(&mut self, specification: &[Token]) {
        let Some(name) = specification.first().and_then(Token::word) else { return };
        let generic = specification.get(1).is_some_and(|token| token.is("["))
            && specification.get(2).is_some_and(|token| token.word().is_some())
            && specification.get(3).is_some_and(|token| !token.is("]"));
        let (type_parameters, definition) = if generic {
            let Some(end) = closing(specification, 1) else { return };
            (read_type_parameters(&specification[2..end]), specification[end + 1..].to_vec())
        } else {
            (vec![], specification[1..].to_vec())
        };
        self.types.push(TypeDeclaration { name: name.to_string(), type_parameters, definition });
    }

    fn opacity(&self) -> Opacity {
        let escaping = self.escaping_words();
        let signature_escaping: FxHashSet<String> = self
            .functions
            .iter()
            .filter(|function| signature_escape(function, &escaping).is_some())
            .map(|function| function.name.clone())
            .collect();
        let mut opaque: FxHashSet<String> =
            self.functions.iter().map(|function| function.name.clone()).collect();
        let mut opaque_methods: FxHashSet<String> = self.methods.clone();
        loop {
            let surroundings =
                self.surroundings(&escaping, &signature_escaping, &opaque, &opaque_methods);
            let next: FxHashSet<String> = self
                .functions
                .iter()
                .filter(|function| surroundings.escapes(function).is_empty())
                .map(|function| function.name.clone())
                .collect();
            let next_methods: FxHashSet<String> = self
                .methods
                .iter()
                .filter(|name| {
                    let mut definitions =
                        self.method_functions.iter().filter(|method| &method.name == *name);
                    definitions.all(|method| surroundings.escapes(method).is_empty())
                        && self.method_functions.iter().any(|method| &method.name == *name)
                })
                .cloned()
                .collect();
            if next == opaque && next_methods == opaque_methods {
                break;
            }
            opaque = next;
            opaque_methods = next_methods;
        }
        let surroundings =
            self.surroundings(&escaping, &signature_escaping, &opaque, &opaque_methods);
        let functions = self.functions.iter().map(|function| OpaqueDeclaration {
            name: function.name.clone(),
            parameters: parameter_names(&function.type_parameters),
            escapes: surroundings.escapes(function),
        });
        let types = self.types.iter().map(|declaration| OpaqueDeclaration {
            name: declaration.name.clone(),
            parameters: parameter_names(&declaration.type_parameters),
            escapes: type_escapes(declaration, &escaping),
        });
        Opacity {
            functions: functions.collect(),
            types: types.collect(),
            unreadable: None,
            called_in_place: self.called_in_place(),
            signatures: self
                .functions
                .iter()
                .map(|function| (function.name.clone(), signature_shapes(function)))
                .collect(),
        }
    }

    fn called_in_place(&self) -> FxHashMap<String, Vec<usize>> {
        let mut in_place: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        loop {
            let mut grown = false;
            for function in &self.functions {
                let Some(body) = &function.body else { continue };
                if mentions(body, "go") {
                    continue;
                }
                for (position, parameter) in
                    value_parameter_names(&function.parameters).iter().enumerate()
                {
                    let known = in_place
                        .get(&function.name)
                        .is_some_and(|positions| positions.contains(&position));
                    if known || !self.only_called_in_place(body, parameter, &in_place) {
                        continue;
                    }
                    in_place.entry(function.name.clone()).or_default().push(position);
                    grown = true;
                }
            }
            if !grown {
                return in_place;
            }
        }
    }

    fn only_called_in_place(
        &self,
        body: &[Token],
        parameter: &str,
        in_place: &FxHashMap<String, Vec<usize>>,
    ) -> bool {
        let literals = function_literal_bodies(body);
        body.iter().enumerate().all(|(index, token)| {
            if !token.is_word(parameter)
                || index.checked_sub(1).is_some_and(|before| body[before].is("."))
            {
                return true;
            }
            if literals.iter().any(|literal| literal.contains(&index)) {
                return false;
            }
            if body.get(index + 1).is_some_and(|next| next.is("(")) {
                return true;
            }
            self.forwarded_in_place(body, index, in_place)
        })
    }

    fn forwarded_in_place(
        &self,
        body: &[Token],
        index: usize,
        in_place: &FxHashMap<String, Vec<usize>>,
    ) -> bool {
        let whole_argument =
            index.checked_sub(1).is_some_and(|before| body[before].is("(") || body[before].is(","))
                && body.get(index + 1).is_some_and(|next| next.is(")") || next.is(","));
        if !whole_argument {
            return false;
        }
        let Some(open) = enclosing_parenthesis(body, index) else { return false };
        let Some(callee) = called_name(body, open) else { return false };
        if !self.functions.iter().any(|function| function.name == callee) {
            return false;
        }
        let position = split_top(&body[open + 1..index], ",").len();
        in_place.get(callee).is_some_and(|positions| positions.contains(&position))
    }

    fn surroundings<'p>(
        &'p self,
        escaping: &'p FxHashSet<String>,
        signature_escaping: &'p FxHashSet<String>,
        opaque: &'p FxHashSet<String>,
        opaque_methods: &'p FxHashSet<String>,
    ) -> Surroundings<'p> {
        Surroundings {
            escaping,
            signature_escaping,
            functions: &self.functions,
            types: &self.types,
            methods: &self.methods,
            opaque,
            opaque_methods,
            parametric_fields: self.parametric_fields(),
        }
    }

    /// The struct fields whose type is one of the `PARAMETRIC_TYPES`, such as `value` in
    /// `struct { value atomic.Pointer[A] }`.
    fn parametric_fields(&self) -> FxHashSet<String> {
        let mut fields = FxHashSet::default();
        for declaration in &self.types {
            let definition = declaration.definition.as_slice();
            let [keyword, open, ..] = definition else { continue };
            if !keyword.is_word("struct") || !open.is("{") {
                continue;
            }
            let Some(end) = closing(definition, 1) else { continue };
            // `a, b atomic.Pointer[A]`: the names, then the package, a dot and the type.
            for field in split_top(&definition[2..end], ";") {
                let Some(dot) = field.iter().position(|token| token.is(".")) else { continue };
                let package = dot.checked_sub(1).and_then(|before| field[before].word());
                let name = field.get(dot + 1).and_then(Token::word);
                let (Some(package), Some(name)) = (package, name) else { continue };
                if !PARAMETRIC_TYPES.contains(&format!("{package}.{name}").as_str()) {
                    continue;
                }
                fields.extend(field[..dot - 1].iter().filter_map(Token::word).map(str::to_string));
            }
        }
        fields
    }

    fn escaping_words(&self) -> FxHashSet<String> {
        let mut escaping: FxHashSet<String> =
            ESCAPING_WORDS.iter().map(|word| word.to_string()).collect();
        loop {
            let before = escaping.len();
            for declaration in &self.types {
                let definition = &declaration.definition;
                if mentioned(definition, &escaping).is_some()
                    || qualified_instantiation(definition).is_some()
                {
                    escaping.insert(declaration.name.clone());
                }
            }
            if escaping.len() == before {
                return escaping;
            }
        }
    }
}

fn read_signature(
    name: &str,
    type_parameters: Vec<TypeParameter>,
    receiver: Vec<Token>,
    declaration: &[Token],
) -> Option<Function> {
    let last = declaration.len().checked_sub(1)?;
    let body_start = match declaration.last() {
        Some(token) if token.is("}") => opening(declaration, last),
        _ => None,
    };
    let signature = &declaration[..body_start.unwrap_or(declaration.len())];
    let end = signature.first().filter(|token| token.is("(")).and(closing(signature, 0))?;
    let mut parameters = receiver;
    if !parameters.is_empty() && end > 1 {
        parameters.push(Token::Symbol(","));
    }
    parameters.extend_from_slice(&signature[1..end]);
    Some(Function {
        name: name.to_string(),
        type_parameters,
        parameters,
        results: signature[end + 1..].to_vec(),
        body: body_start.map(|start| declaration[start + 1..last].to_vec()),
    })
}

fn read_type_parameters(tokens: &[Token]) -> Vec<TypeParameter> {
    let mut parameters = vec![];
    let mut pending = vec![];
    for entry in split_top(tokens, ",") {
        let Some(name) = entry.first().and_then(Token::word) else { continue };
        pending.push(name.to_string());
        if entry.len() > 1 {
            for name in pending.drain(..) {
                parameters.push(TypeParameter { name, constraint: entry[1..].to_vec() });
            }
        }
    }
    let unconstrained = pending.into_iter().map(|name| TypeParameter { name, constraint: vec![] });
    parameters.extend(unconstrained);
    parameters
}

fn signature_shapes(function: &Function) -> ForeignSignature {
    let type_parameters: FxHashSet<String> =
        function.type_parameters.iter().map(|parameter| parameter.name.clone()).collect();
    let entries = split_top(&function.parameters, ",");
    let mut parameters = Vec::with_capacity(entries.len());
    for (position, entry) in entries.iter().enumerate() {
        let typed = entries[position..].iter().find(|entry| entry.len() > 1);
        let shape = match typed {
            Some(typed) => shape_of(&typed[1..], &type_parameters),
            None => ForeignShape::Other,
        };
        parameters.push(match entry.len() {
            1 if typed.is_none() => ForeignShape::Other,
            _ => shape,
        });
    }
    ForeignSignature { parameters, result: shape_of(&function.results, &type_parameters) }
}

fn shape_of(tokens: &[Token], type_parameters: &FxHashSet<String>) -> ForeignShape {
    if let [Token::Word(word)] = tokens
        && type_parameters.contains(word)
    {
        return ForeignShape::Parameter(word.clone());
    }
    if tokens.iter().any(|token| token.is_word("func") || token.is("(")) {
        return ForeignShape::Other;
    }
    let mut held =
        tokens.iter().filter_map(Token::word).filter(|word| type_parameters.contains(*word));
    match (held.next(), held.next()) {
        (Some(word), None)
            if tokens.last().is_some_and(|last| last.is_word(word) || last.is("]")) =>
        {
            ForeignShape::Holder(word.to_string())
        }
        _ => ForeignShape::Other,
    }
}

fn parameter_names(parameters: &[TypeParameter]) -> Vec<String> {
    parameters.iter().map(|parameter| parameter.name.clone()).collect()
}

fn value_parameter_names(parameters: &[Token]) -> Vec<&str> {
    split_top(parameters, ",")
        .into_iter()
        .map(|parameter| parameter.first().and_then(Token::word).unwrap_or_default())
        .collect()
}

fn function_literal_bodies(body: &[Token]) -> Vec<Range<usize>> {
    let mut literals = vec![];
    for (index, token) in body.iter().enumerate() {
        if !token.is_word("func") {
            continue;
        }
        let open = index + 1 + literal_signature(body, index + 1).len();
        if let Some(close) = body.get(open).filter(|token| token.is("{")).and(closing(body, open)) {
            literals.push(open..close);
        }
    }
    literals
}

fn enclosing_parenthesis(tokens: &[Token], index: usize) -> Option<usize> {
    let mut depth = 0usize;
    for position in (0..index).rev() {
        let token = &tokens[position];
        if token.is_closing() {
            depth += 1;
        } else if token.is_opening() {
            if depth == 0 {
                return token.is("(").then_some(position);
            }
            depth -= 1;
        }
    }
    None
}

fn called_name(tokens: &[Token], open: usize) -> Option<&str> {
    let mut end = open.checked_sub(1)?;
    if tokens[end].is("]") {
        end = opening(tokens, end)?.checked_sub(1)?;
    }
    let qualified = end.checked_sub(1).is_some_and(|before| tokens[before].is("."));
    if qualified {
        return None;
    }
    tokens[end].word().filter(|_| !tokens[end].is_keyword())
}

fn constraint_escapes(parameters: &[TypeParameter]) -> Vec<Escape> {
    let constrained = parameters.iter().filter(|parameter| !parameter.is_unconstrained());
    let escapes = constrained.map(|parameter| Escape {
        parameter: Some(parameter.name.clone()),
        reason: format!("is constrained by `{}`", spelled(&parameter.constraint)),
    });
    escapes.collect()
}

fn whole(reason: String) -> Escape {
    Escape { parameter: None, reason }
}

fn type_escapes(declaration: &TypeDeclaration, escaping: &FxHashSet<String>) -> Vec<Escape> {
    let mut escapes = constraint_escapes(&declaration.type_parameters);
    if let Some(word) = mentioned(&declaration.definition, escaping) {
        escapes.push(whole(format!("mentions `{word}`")));
    } else if let Some(name) = qualified_instantiation(&declaration.definition) {
        escapes.push(whole(format!("names `{name}`")));
    }
    escapes
}

fn signature_escape(function: &Function, escaping: &FxHashSet<String>) -> Option<String> {
    let signature = [function.parameters.as_slice(), function.results.as_slice()].concat();
    if let Some(word) = mentioned(&signature, escaping) {
        return Some(format!("mentions `{word}` in its signature"));
    }
    qualified_instantiation(&signature).map(|name| format!("names `{name}` in its signature"))
}

fn literal_signature(tokens: &[Token], start: usize) -> &[Token] {
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate().skip(start) {
        if token.is_opening() {
            let type_literal = index > 0
                && ["struct", "interface"].iter().any(|word| tokens[index - 1].is_word(word));
            if depth == 0 && token.is("{") && !type_literal {
                return &tokens[start..index];
            }
            depth += 1;
        } else if token.is_closing() {
            let Some(inner) = depth.checked_sub(1) else { return &tokens[start..index] };
            depth = inner;
        } else if depth == 0 && [",", ";", "="].iter().any(|separator| token.is(separator)) {
            return &tokens[start..index];
        }
    }
    &tokens[start..]
}

struct Surroundings<'p> {
    escaping: &'p FxHashSet<String>,
    signature_escaping: &'p FxHashSet<String>,
    functions: &'p [Function],
    types: &'p [TypeDeclaration],
    methods: &'p FxHashSet<String>,
    opaque: &'p FxHashSet<String>,
    opaque_methods: &'p FxHashSet<String>,
    parametric_fields: FxHashSet<String>,
}

impl Surroundings<'_> {
    /// The type of the field of a struct the package declares, through pointers and aliases.
    fn field_type(&self, holder: &[Token], field: &str) -> Option<Vec<Token>> {
        let definition = self.struct_definition(holder)?;
        let body = &definition[2..closing(&definition, 1)?];
        split_top(body, ";").into_iter().find_map(|entry| {
            let names = split_top(entry, ",");
            let (last, others) = names.split_last()?;
            let named = last.len() > 1 && others.iter().all(|other| other.len() == 1);
            let declares = others.iter().chain([last]).any(|name| name[0].is_word(field));
            (named && declares).then(|| last[1..].to_vec())
        })
    }

    fn struct_definition(&self, holder: &[Token]) -> Option<Vec<Token>> {
        let mut current = holder.to_vec();
        for _ in 0..self.types.len() + 1 {
            let unpointed = current.iter().position(|token| !token.is("*"))?;
            current.drain(..unpointed);
            if current.first()?.is_word("struct") && current.get(1)?.is("{") {
                return Some(current);
            }
            let name = current.first()?.word()?;
            if current.get(1).is_some_and(|token| token.is(".")) {
                return None;
            }
            let declaration = self.types.iter().find(|declaration| declaration.name == name)?;
            let definition = &declaration.definition;
            let aliased = definition.first().is_some_and(|token| token.is("="));
            current = definition[usize::from(aliased)..].to_vec();
        }
        None
    }

    fn escapes(&self, function: &Function) -> Vec<Escape> {
        let mut escapes = constraint_escapes(&function.type_parameters);
        let Some(body) = &function.body else {
            escapes.push(whole("has no body".to_string()));
            return escapes;
        };
        if let Some(reason) = self.whole_escape(function, body) {
            escapes.push(whole(reason));
            return escapes;
        }
        for parameter in &function.type_parameters {
            if escapes.iter().any(|escape| escape.parameter.as_ref() == Some(&parameter.name)) {
                continue;
            }
            let flow = Flow::new(self, function, body, &parameter.name);
            if let Some(reason) = flow.escape() {
                escapes.push(Escape { parameter: Some(parameter.name.clone()), reason });
            }
        }
        escapes
    }

    fn whole_escape(&self, function: &Function, body: &[Token]) -> Option<String> {
        if let Some(reason) = signature_escape(function, self.escaping) {
            return Some(reason);
        }
        if let Some(word) = mentioned(body, self.escaping) {
            return Some(format!("mentions `{word}`"));
        }
        if body.windows(2).any(|pair| pair[0].is(".") && pair[1].is("(")) {
            return Some("asserts a type".to_string());
        }
        if mentions(body, "type") {
            return Some("declares a type".to_string());
        }
        let literals = body.iter().enumerate().filter(|(_, token)| token.is_word("func"));
        for (index, _) in literals {
            if let Some(name) = qualified(literal_signature(body, index + 1)) {
                return Some(format!("names `{name}` in a function literal"));
            }
        }
        let called = body.windows(2).find_map(|pair| match pair {
            [Token::Word(name), open] if open.is("(") => self.signature_escaping.get(name.as_str()),
            _ => None,
        });
        called.map(|name| format!("calls `{name}`"))
    }
}

struct Assignment {
    left: Range<usize>,
    right: Range<usize>,
    defines: bool,
    declared_type: Option<Range<usize>>,
}

struct Flow<'f> {
    surroundings: &'f Surroundings<'f>,
    tokens: &'f [Token],
    parameter: &'f str,
    locals: FxHashSet<&'f str>,
    tainted: FxHashSet<&'f str>,
    declared: FxHashMap<&'f str, &'f [Token]>,
    assignments: Vec<Assignment>,
    blocks: FxHashSet<usize>,
    /// The function's parameters of a function type: PureScript functions, which take what Go
    /// lets them be called with and look into nothing else.
    callbacks: FxHashSet<&'f str>,
}

impl<'f> Flow<'f> {
    fn new(
        surroundings: &'f Surroundings<'f>,
        function: &'f Function,
        body: &'f [Token],
        parameter: &'f str,
    ) -> Flow<'f> {
        let mut flow = Flow {
            surroundings,
            tokens: body,
            parameter,
            locals: FxHashSet::default(),
            tainted: [parameter].into_iter().collect(),
            declared: FxHashMap::default(),
            assignments: vec![],
            blocks: FxHashSet::default(),
            callbacks: FxHashSet::default(),
        };
        flow.declare_parameters(&function.parameters);
        flow.callbacks = flow.callbacks_among(&function.parameters);
        flow.declare_parameters(result_list(&function.results));
        for (index, token) in body.iter().enumerate() {
            if token.is_word("func") && body.get(index + 1).is_some_and(|token| token.is("(")) {
                flow.declare_literal(index);
            }
            if token.word().is_some_and(|word| HEADER_KEYWORDS.contains(&word)) {
                flow.mark_header_block(index);
            }
        }
        flow.assignments = flow.find_assignments();
        flow.propagate();
        flow
    }

    fn declare_parameters(&mut self, list: &'f [Token]) {
        let entries = split_top(list, ",");
        if !entries.iter().any(|entry| is_named_entry(entry)) {
            return;
        }
        let mut pending = vec![];
        for entry in entries {
            let Some(name) = entry.first().and_then(Token::word) else { continue };
            pending.push(name);
            if entry.len() > 1 {
                let typed = mentions(&entry[1..], self.parameter);
                for name in pending.drain(..) {
                    self.locals.insert(name);
                    self.declared.insert(name, &entry[1..]);
                    if typed {
                        self.tainted.insert(name);
                    }
                }
            }
        }
    }

    fn callbacks_among(&self, list: &'f [Token]) -> FxHashSet<&'f str> {
        let mut callbacks = FxHashSet::default();
        let mut pending = vec![];
        for entry in split_top(list, ",") {
            let Some(name) = entry.first().and_then(Token::word) else { continue };
            pending.push(name);
            if entry.len() > 1 {
                let function = entry[1].is_word("func");
                callbacks.extend(pending.drain(..).filter(|_| function));
            }
        }
        callbacks
    }

    fn declare_literal(&mut self, keyword: usize) {
        let tokens = self.tokens;
        let Some(end) = closing(tokens, keyword + 1) else { return };
        self.declare_parameters(&tokens[keyword + 2..end]);
        let mut results = end + 1;
        if tokens.get(results).is_some_and(|token| token.is("("))
            && let Some(results_end) = closing(tokens, results)
        {
            self.declare_parameters(&tokens[results + 1..results_end]);
            results = results_end + 1;
        }
        let signature = literal_signature(tokens, results);
        let after = results + signature.len();
        if tokens.get(after).is_some_and(|token| token.is("{")) {
            self.blocks.insert(after);
        }
    }

    fn mark_header_block(&mut self, keyword: usize) {
        let mut depth = 0usize;
        for (index, token) in self.tokens.iter().enumerate().skip(keyword + 1) {
            if token.is_opening() {
                if depth == 0 && token.is("{") {
                    self.blocks.insert(index);
                    return;
                }
                depth += 1;
            } else if token.is_closing() {
                let Some(inner) = depth.checked_sub(1) else { return };
                depth = inner;
            }
        }
    }

    fn find_assignments(&mut self) -> Vec<Assignment> {
        let tokens = self.tokens;
        let mut assignments = vec![];
        let mut declared_equals = FxHashSet::default();
        for (index, token) in tokens.iter().enumerate() {
            if token.is_word("var") {
                let end = self.right_end(index, false);
                assignments.extend(self.variable_assignment(index + 1..end, &mut declared_equals));
            }
        }
        for (index, token) in tokens.iter().enumerate() {
            let Token::Symbol(symbol) = token else { continue };
            if !ASSIGNMENTS.contains(symbol) || declared_equals.contains(&index) {
                continue;
            }
            let start = self.left_start(index);
            let header = start
                .checked_sub(1)
                .and_then(|before| tokens[before].word())
                .is_some_and(|word| HEADER_KEYWORDS.contains(&word))
                || tokens.get(index + 1).is_some_and(|token| token.is_word("range"));
            let defines = *symbol == ":=";
            if defines {
                for name in self.names(start..index) {
                    self.locals.insert(name);
                }
            }
            let right = index + 1..self.right_end(index, header);
            if let ([name], Some(constructed)) =
                (self.names(start..index).as_slice(), self.constructed_type(right.clone()))
                && defines
            {
                self.declared.insert(name, constructed);
            }
            assignments.push(Assignment {
                left: start..index,
                right,
                defines,
                declared_type: None,
            });
        }
        assignments
    }

    fn variable_assignment(
        &mut self,
        specification: Range<usize>,
        declared_equals: &mut FxHashSet<usize>,
    ) -> Option<Assignment> {
        let tokens = self.tokens;
        let mut position = specification.start;
        loop {
            tokens.get(position).and_then(Token::word)?;
            position += 1;
            if !tokens.get(position).is_some_and(|token| token.is(",")) {
                break;
            }
            position += 1;
        }
        let left = specification.start..position;
        for name in self.names(left.clone()) {
            self.locals.insert(name);
        }
        let equals = (position..specification.end).find(|&index| tokens[index].is("="));
        let declared_type = position..equals.unwrap_or(specification.end);
        let declared_type = (!declared_type.is_empty()).then_some(declared_type);
        if let Some(declared_type) = declared_type.clone() {
            for name in self.names(left.clone()) {
                self.declared.insert(name, &tokens[declared_type.clone()]);
            }
        }
        let right = match equals {
            Some(equals) => {
                declared_equals.insert(equals);
                equals + 1..specification.end
            }
            None => specification.end..specification.end,
        };
        Some(Assignment { left, right, defines: true, declared_type })
    }

    /// The type an expression spells out as it builds a value: `&T{…}`, `T{…}`, `new(T)` or
    /// `make(T, …)`.
    fn constructed_type(&self, expression: Range<usize>) -> Option<&'f [Token]> {
        let tokens = self.tokens;
        let expression = &tokens[expression];
        let unreferenced = expression.strip_prefix(&[Token::Symbol("&")][..]).unwrap_or(expression);
        match unreferenced {
            [Token::Word(builtin), open, ..] if builtin == "new" || builtin == "make" => {
                let arguments = &unreferenced[2..closing(unreferenced, 1)?];
                (open.is("(") && closing(unreferenced, 1)? + 1 == unreferenced.len())
                    .then(|| split_top(arguments, ",").into_iter().next())
                    .flatten()
            }
            [.., last] if last.is("}") => {
                let open = opening(unreferenced, unreferenced.len() - 1)?;
                let built = &unreferenced[..open];
                let simple = built.iter().all(|token| {
                    token.word().is_some_and(|word| !word.eq("func"))
                        || [".", "[", "]", ","].iter().any(|symbol| token.is(symbol))
                });
                (simple && !built.is_empty()).then_some(built)
            }
            _ => None,
        }
    }

    fn names(&self, range: Range<usize>) -> Vec<&'f str> {
        let tokens = self.tokens;
        let elements = split_top(&tokens[range], ",");
        elements.into_iter().filter_map(|element| element.first().and_then(Token::word)).collect()
    }

    fn left_start(&self, operator: usize) -> usize {
        let mut depth = 0usize;
        let mut index = operator;
        while index > 0 {
            let token = &self.tokens[index - 1];
            if token.is_closing() {
                depth += 1;
            } else if token.is_opening() {
                if depth == 0 {
                    return index;
                }
                depth -= 1;
            } else if depth == 0 && (token.is(";") || token.is(":") || token.is_keyword()) {
                return index;
            }
            index -= 1;
        }
        0
    }

    fn right_end(&self, operator: usize, header: bool) -> usize {
        let mut depth = 0usize;
        for (index, token) in self.tokens.iter().enumerate().skip(operator + 1) {
            if token.is_opening() {
                if depth == 0 && header && token.is("{") {
                    return index;
                }
                depth += 1;
            } else if token.is_closing() {
                if depth == 0 {
                    return index;
                }
                depth -= 1;
            } else if depth == 0 && (token.is(";") || token.is(":")) {
                return index;
            }
        }
        self.tokens.len()
    }

    fn propagate(&mut self) {
        loop {
            let before = self.tainted.len();
            for assignment in &self.assignments {
                let typed = assignment
                    .declared_type
                    .clone()
                    .is_some_and(|range| mentions(&self.tokens[range], self.parameter));
                if assignment.defines && (typed || self.is_tainted(assignment.right.clone())) {
                    for name in self.names(assignment.left.clone()) {
                        self.tainted.insert(name);
                    }
                }
            }
            if self.tainted.len() == before {
                return;
            }
        }
    }

    fn is_tainted(&self, range: Range<usize>) -> bool {
        let tokens = self.tokens;
        let mut index = range.start;
        while index < range.end {
            if let Some((body_open, body_close)) = self.function_literal(index) {
                if self.is_tainted(index + 1..body_open) {
                    return true;
                }
                index = body_close + 1;
                continue;
            }
            if let Some(word) = tokens[index].word() {
                let selected = index > 0 && tokens[index - 1].is(".");
                let counted = !selected
                    && COUNTING_BUILTINS.contains(&word)
                    && tokens.get(index + 1).is_some_and(|token| token.is("("));
                if counted && let Some(end) = closing(tokens, index + 1) {
                    index = end + 1;
                    continue;
                }
                if self.tainted.contains(word) {
                    return true;
                }
            }
            index += 1;
        }
        false
    }

    /// The braces around the body of the function literal starting at the `func` keyword. A
    /// literal hands on values only through what its signature names: whatever its body does with
    /// the values it captures is part of the surrounding body, and looked at there.
    fn function_literal(&self, keyword: usize) -> Option<(usize, usize)> {
        let tokens = self.tokens;
        if !tokens[keyword].is_word("func") || !tokens.get(keyword + 1)?.is("(") {
            return None;
        }
        let mut results = closing(tokens, keyword + 1)? + 1;
        if tokens.get(results)?.is("(") {
            results = closing(tokens, results)? + 1;
        }
        let body_open = results + literal_signature(tokens, results).len();
        if !tokens.get(body_open)?.is("{") {
            return None;
        }
        Some((body_open, closing(tokens, body_open)?))
    }

    /// Whether the call at `callee` goes through fields of a local to a function the package
    /// typed, or to a method of a type that only stores the value, such as `atomic.Pointer[A]`'s
    /// `Store`. A value of type `A` only shows what it is once converted to an interface, and the
    /// parameters of a function type the package spells out are no interfaces: those would
    /// mention `any` or `interface`.
    fn calls_through_held_value(&self, callee: usize) -> bool {
        let tokens = self.tokens;
        let mut selectors = vec![];
        let mut index = callee;
        while index >= 2 && tokens[index - 1].is(".") {
            let Some(word) = tokens[index - 2].word() else { return false };
            selectors.push(word);
            index -= 2;
        }
        let Some(root) = selectors.pop() else { return false };
        let Some(callee) = tokens[callee].word() else { return false };
        if !self.locals.contains(root) || self.surroundings.methods.contains(callee) {
            return false;
        }
        let Some(declared) = self.declared.get(root) else { return false };
        let mut receiver = declared.to_vec();
        for field in selectors.into_iter().rev() {
            let Some(field_type) = self.surroundings.field_type(&receiver, field) else {
                return false;
            };
            receiver = field_type;
        }
        if let Some(field_type) = self.surroundings.field_type(&receiver, callee) {
            return field_type.first().is_some_and(|token| token.is_word("func"));
        }
        let unpointed: Vec<&Token> = receiver.iter().skip_while(|token| token.is("*")).collect();
        match unpointed.as_slice() {
            [Token::Word(package), dot, Token::Word(_), open, ..] => {
                dot.is(".") && open.is("[") && OPAQUE_GENERIC_PACKAGES.contains(&package.as_str())
            }
            _ => false,
        }
    }

    fn holds_values(&self, name: &str) -> bool {
        self.locals.contains(name) && self.tainted.contains(name)
    }

    /// A local whose type the function spells out, as a parameter, a `var`, or by building it.
    fn is_typed_local(&self, name: &str) -> bool {
        self.locals.contains(name) && self.declared.contains_key(name)
    }

    /// A local of a function type the function spells out, such as a callback parameter.
    fn is_typed_function(&self, name: &str) -> bool {
        let declared = self.declared.get(name).filter(|_| self.locals.contains(name));
        declared.and_then(|declared| declared.first()).is_some_and(|token| token.is_word("func"))
    }

    fn escape(&self) -> Option<String> {
        for assignment in &self.assignments {
            if let Some(reason) = self.assignment_escape(assignment) {
                return Some(reason);
            }
        }
        for (index, token) in self.tokens.iter().enumerate() {
            let reason = match token {
                _ if token.is("(") => self.call_escape(index),
                _ if token.is("{") => self.composite_escape(index),
                _ if token.is(".") => self.method_escape(index),
                _ if token.is("<-") => self.send_escape(index),
                _ => None,
            };
            if reason.is_some() {
                return reason;
            }
        }
        None
    }

    fn assignment_escape(&self, assignment: &Assignment) -> Option<String> {
        if !self.is_tainted(assignment.right.clone()) {
            return None;
        }
        let tokens = self.tokens;
        if assignment.defines {
            let declared_type = &tokens[assignment.declared_type.clone()?];
            return (!mentions(declared_type, self.parameter))
                .then(|| format!("stores a value in a `{}`", spelled(declared_type)));
        }
        for element in split_top(&tokens[assignment.left.clone()], ",") {
            let Some(root) = element.iter().find_map(Token::word) else { continue };
            if root == "_" {
                continue;
            }
            if !self.locals.contains(root) {
                return Some(format!("stores a value in `{root}`"));
            }
            if !self.tainted.contains(root) {
                return Some(format!("assigns a value to `{root}`"));
            }
        }
        None
    }

    fn call_escape(&self, open: usize) -> Option<String> {
        let tokens = self.tokens;
        let end = closing(tokens, open)?;
        let previous = &tokens[open.checked_sub(1)?];
        if !self.is_tainted(open + 1..end) {
            return None;
        }
        if previous.is("]") {
            let bracket = opening(tokens, open - 1)?;
            let root = bracket.checked_sub(1).and_then(|before| tokens[before].word());
            return match root {
                Some(root)
                    if self.surroundings.opaque.contains(root) || self.holds_values(root) =>
                {
                    None
                }
                Some(root) if self.is_function(root) => Some(format!("passes a value to `{root}`")),
                _ if mentions(&tokens[bracket..open], self.parameter) => None,
                _ => Some("passes a value to an indexed function".to_string()),
            };
        }
        if previous.is(")") {
            let parenthesis = opening(tokens, open - 1)?;
            let after_func =
                parenthesis.checked_sub(1).is_some_and(|before| tokens[before].is_word("func"));
            let converts = mentions(&tokens[parenthesis..open], self.parameter);
            let curried = parenthesis.checked_sub(1).and_then(|before| tokens[before].word());
            let curried = curried
                .is_some_and(|callee| self.holds_values(callee) || self.is_typed_function(callee));
            return (!after_func && !converts && !curried)
                .then(|| "passes a value to the result of an expression".to_string());
        }
        let callee = previous.word()?;
        let qualifier = open
            .checked_sub(2)
            .filter(|&dot| tokens[dot].is("."))
            .and_then(|dot| dot.checked_sub(1))
            .and_then(|root| tokens[root].word());
        let field_access = open.checked_sub(4).is_some_and(|dot| tokens[dot].is("."));
        match qualifier {
            Some(root) if GENERIC_PACKAGES.contains(&root) && !self.locals.contains(root) => None,
            Some(root)
                if field_access
                    && self.surroundings.parametric_fields.contains(root)
                    && PARAMETRIC_METHODS.contains(&callee) =>
            {
                None
            }
            Some(_) if self.calls_through_held_value(open - 1) => None,
            Some(root)
                if self.locals.contains(root)
                    && self.surroundings.opaque_methods.contains(callee) =>
            {
                None
            }
            Some(root) => Some(format!("passes a value to `{root}.{callee}`")),
            None if previous.is_keyword() => None,
            None if BUILTINS.contains(&callee) => self.builtin_escape(callee, open, end),
            None if callee == self.parameter
                || self.surroundings.opaque.contains(callee)
                || self.holds_values(callee)
                || self.callbacks.contains(callee)
                || self.is_typed_function(callee) =>
            {
                None
            }
            None => Some(format!("passes a value to `{callee}`")),
        }
    }

    fn is_function(&self, name: &str) -> bool {
        self.surroundings.functions.iter().any(|function| function.name == name)
    }

    fn builtin_escape(&self, builtin: &str, open: usize, end: usize) -> Option<String> {
        if builtin != "append" {
            return None;
        }
        let first_end = self.first_argument_end(open, end);
        (!self.is_tainted(open + 1..first_end))
            .then(|| "appends a value to a slice of another type".to_string())
    }

    fn first_argument_end(&self, open: usize, end: usize) -> usize {
        let mut depth = 0usize;
        for (index, token) in self.tokens.iter().enumerate().take(end).skip(open + 1) {
            if token.is_opening() {
                depth += 1;
            } else if token.is_closing() {
                depth = depth.saturating_sub(1);
            } else if depth == 0 && token.is(",") {
                return index;
            }
        }
        end
    }

    fn composite_escape(&self, open: usize) -> Option<String> {
        let tokens = self.tokens;
        let type_literal = open.checked_sub(1).is_some_and(|before| {
            ["struct", "interface"].iter().any(|word| tokens[before].is_word(word))
        });
        if self.blocks.contains(&open) || type_literal {
            return None;
        }
        let start = self.type_start(open);
        if start == open {
            return None;
        }
        let end = closing(tokens, open)?;
        if !self.is_tainted(open + 1..end) {
            return None;
        }
        let composite_type = &tokens[start..open];
        (!mentions(composite_type, self.parameter))
            .then(|| format!("builds a `{}` from a value", spelled(composite_type)))
    }

    fn type_start(&self, open: usize) -> usize {
        let tokens = self.tokens;
        let mut start = open;
        while let Some(previous) = start.checked_sub(1) {
            let token = &tokens[previous];
            if token.is("]") || token.is("}") {
                let Some(bracket) = opening(tokens, previous) else { break };
                start = bracket;
            } else if token.is(".") || token.is("*") {
                start = previous;
            } else if let Some(word) = token.word()
                && (!token.is_keyword() || TYPE_KEYWORDS.contains(&word))
            {
                start = previous;
            } else {
                break;
            }
        }
        start
    }

    fn method_escape(&self, dot: usize) -> Option<String> {
        let tokens = self.tokens;
        let name = tokens.get(dot + 1)?.word()?;
        if !self.surroundings.methods.contains(name)
            || self.surroundings.opaque_methods.contains(name)
        {
            return None;
        }
        let root = self.chain_root(dot)?;
        self.tainted.contains(root).then(|| format!("uses the method `{name}`"))
    }

    fn chain_root(&self, end: usize) -> Option<&'f str> {
        let tokens = self.tokens;
        let mut root = None;
        let mut index = end;
        while let Some(previous) = index.checked_sub(1) {
            let token = &tokens[previous];
            if token.is_keyword() {
                break;
            } else if let Some(word) = token.word() {
                root = Some(word);
                index = previous;
            } else if token.is(".") {
                index = previous;
            } else if token.is("]") || token.is(")") {
                index = opening(tokens, previous)?;
            } else {
                break;
            }
        }
        root
    }

    fn send_escape(&self, arrow: usize) -> Option<String> {
        let tokens = self.tokens;
        let previous = &tokens[arrow.checked_sub(1)?];
        let sends = previous.word().is_some_and(|_| !previous.is_keyword())
            || previous.is(")")
            || previous.is("]");
        if !sends || !self.is_tainted(arrow + 1..self.right_end(arrow, false)) {
            return None;
        }
        let root = self.chain_root(arrow)?;
        let local_channel = self.holds_values(root) || self.is_typed_local(root);
        (!local_channel).then(|| format!("sends a value on `{root}`"))
    }
}

fn result_list(results: &[Token]) -> &[Token] {
    match results.first() {
        Some(token) if token.is("(") => match closing(results, 0) {
            Some(end) => &results[1..end],
            None => &[],
        },
        _ => &[],
    }
}

fn is_named_entry(entry: &[Token]) -> bool {
    match entry {
        [first, ..] if first.is_keyword() => false,
        [Token::Word(_), second, ..] if second.is(".") => false,
        [Token::Word(_), second, ..] if second.is("[") => {
            closing(entry, 1).is_some_and(|end| end + 1 < entry.len())
        }
        [Token::Word(_), _, ..] => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn escapes(source: &str, name: &str) -> Vec<String> {
        let opacity = foreign_opacity(&[source]);
        let function = opacity.function(name).or_else(|| opacity.data_type(name));
        let function = function.unwrap_or_else(|| panic!("{name} is declared"));
        function.escapes.iter().map(Escape::to_string).collect()
    }

    fn called_in_place(source: &str, name: &str) -> Vec<usize> {
        let opacity = foreign_opacity(&[source]);
        let mut positions = opacity.called_in_place.get(name).cloned().unwrap_or_default();
        positions.sort();
        positions
    }

    const RUNNERS: &str = "package ffi

func CatchImpl[A any](handler func(error) A, action func() A) A {
	result, failure, failed := attempt(action)
	if failed {
		return handler(failure)
	}
	return result
}

func attempt[A any](action func() A) (result A, failure error, failed bool) {
	defer recoverInto(&failure, &failed)
	return action(), nil, false
}

func ForkImpl(action func()) {
	go action()
}

func LaterImpl(action func()) func() {
	return action
}

func DeferredImpl(action func()) {
	run(func() { action() })
}

func run(action func()) {
	action()
}

func StoredImpl(actions []func(), action func()) {
	actions[0] = action
}
";

    #[test]
    fn a_function_argument_called_before_returning_is_called_in_place() {
        assert_eq!(called_in_place(RUNNERS, "CatchImpl"), vec![0, 1]);
        assert_eq!(called_in_place(RUNNERS, "attempt"), vec![0]);
        assert_eq!(called_in_place(RUNNERS, "run"), vec![0]);
    }

    #[test]
    fn a_function_argument_started_returned_wrapped_or_stored_is_not_called_in_place() {
        for name in ["ForkImpl", "LaterImpl", "DeferredImpl", "StoredImpl"] {
            assert_eq!(called_in_place(RUNNERS, name), Vec::<usize>::new(), "{name}");
        }
    }

    const REPEATED: &str = "package ffi

type Repeated[A any] []A

func Empty[A any]() Repeated[A] { return nil }

func SnocImpl[A any](items Repeated[A], item A) Repeated[A] { return append(items, item) }

func Freeze[A any](items Repeated[A]) []A { return items }

func Length[A any](items Repeated[A]) int32 { return int32(len(items)) }

func IndexOr[A any](fallback A, index int32, items Repeated[A]) A {
	if index < 0 || int(index) >= len(items) {
		return fallback
	}
	return items[index]
}

func Each[A any](items Repeated[A], visit func(A)) {
	for _, item := range items {
		visit(item)
	}
}

func Pairs[A any, B any](items Repeated[A], other []B) []struct{ first A; second B } {
	pairs := make([]struct{ first A; second B }, 0, len(items))
	for index, item := range items {
		pairs = append(pairs, struct{ first A; second B }{item, other[index]})
	}
	return pairs
}
";

    #[test]
    fn a_container_that_only_stores_its_values_is_opaque() {
        for name in
            ["Repeated", "Empty", "SnocImpl", "Freeze", "Length", "IndexOr", "Each", "Pairs"]
        {
            assert_eq!(escapes(REPEATED, name), Vec::<String>::new(), "{name}");
        }
    }

    #[test]
    fn a_cell_behind_an_atomic_pointer_only_keeps_its_values() {
        let source = "package ffi

import \"sync/atomic\"

type IORef[A any] = *ioref[A]

type ioref[A any] struct {
	value atomic.Pointer[A]
}

func NewIORefImpl[A any](value A) *ioref[A] {
	ref := &ioref[A]{}
	ref.value.Store(&value)
	return ref
}

func ReadIORefImpl[A any](ref *ioref[A]) A { return *ref.value.Load() }

func AtomicModifyIORefImpl[A, B, T any](first func(T) A, second func(T) B, f func(A) T, ref *ioref[A]) B {
	for {
		old := ref.value.Load()
		result := f(*old)
		updated := first(result)
		if ref.value.CompareAndSwap(old, &updated) {
			return second(result)
		}
	}
}
";
        for name in ["IORef", "ioref", "NewIORefImpl", "ReadIORefImpl", "AtomicModifyIORefImpl"] {
            assert_eq!(escapes(source, name), Vec::<String>::new(), "{name}");
        }
    }

    #[test]
    fn a_conversion_to_an_interface_looks_into_the_value() {
        let source = "package ffi

import \"fmt\"

func Describe[A any](value A) string {
	switch any(value).(type) {
	case int32:
		return \"an int\"
	}
	return \"something else\"
}

func Show[A any](value A) string { return fmt.Sprint(value) }

func Count[A any](values []A) string { return fmt.Sprint(len(values)) }

func Equal[A comparable](left A, right A) bool { return left == right }
";
        assert_eq!(escapes(source, "Describe"), ["it mentions `any`"]);
        assert_eq!(escapes(source, "Show"), ["type parameter A passes a value to `fmt.Sprint`"]);
        assert_eq!(escapes(source, "Count"), Vec::<String>::new());
        assert_eq!(escapes(source, "Equal"), ["type parameter A is constrained by `comparable`"]);
    }

    #[test]
    fn storing_a_value_beyond_the_function_looks_into_it() {
        let source = "package ffi

var kept int32

type Holder struct{ value any }

type Box[A any] struct{ holder Holder; value A }

func Keep[A any](value A) { kept = value }

func Hold[A any](value A) Box[A] { return Box[A]{value: value} }

func Forward[A any](value A) { Keep(value) }

func Pass[A any](value A) { keepAll(value) }

func keepAll(values ...any) {}

func (box Box[A]) Peek() {}

func Peek[A any](box Box[A]) { box.Peek() }
";
        assert_eq!(escapes(source, "Keep"), ["type parameter A stores a value in `kept`"]);
        assert_eq!(escapes(source, "Box"), ["it mentions `Holder`"]);
        assert_eq!(escapes(source, "Hold"), ["it mentions `Box` in its signature"]);
        assert_eq!(escapes(source, "Forward"), ["type parameter A passes a value to `Keep`"]);
        assert_eq!(escapes(source, "Pass"), ["it calls `keepAll`"]);
    }

    #[test]
    fn a_method_of_the_package_may_look_into_the_value() {
        let source = "package ffi

type Cell[A any] struct{ value A }

func (cell Cell[A]) Reset() { show(cell.value) }

func show(value any) {}

func Reset[A any](cell Cell[A]) { cell.Reset() }

func Wrap[A any](value A) Cell[A] { return Cell[A]{value: value} }
";
        assert_eq!(escapes(source, "Reset"), ["type parameter A uses the method `Reset`"]);
        assert_eq!(escapes(source, "Wrap"), Vec::<String>::new());
    }

    #[test]
    fn a_method_of_the_package_that_only_holds_the_value_keeps_it_opaque() {
        let source = "package ffi

import \"sync/atomic\"

type IORef[A any] = *ioref[A]

type ioref[A any] struct {
	value atomic.Pointer[A]
}

func (ref *ioref[A]) Load() A { return *ref.value.Load() }

func (ref *ioref[A]) Store(value A) { ref.value.Store(&value) }

func ReadIORefImpl[A any](ref *ioref[A]) A { return ref.Load() }

func WriteIORefImpl[A any](ref *ioref[A], value A) { ref.Store(value) }
";
        assert_eq!(escapes(source, "ReadIORefImpl"), Vec::<String>::new());
        assert_eq!(escapes(source, "WriteIORefImpl"), Vec::<String>::new());
    }

    #[test]
    fn a_type_of_another_package_holds_the_value_only_when_instantiated_with_it() {
        let source = "package ffi

import (
	\"context\"
	\"sync\"
	\"sync/atomic\"

	\"example.com/other\"
)

type cell[A any] struct {
	lock  sync.Mutex
	value atomic.Pointer[A]
}

type Cell[A any] = *cell[A]

func Read[A any](cell *cell[A]) A { return *cell.value.Load() }

func Offer[A any](ctx context.Context, channel chan A, value A) bool {
	select {
	case channel <- value:
		return true
	case <-ctx.Done():
		return false
	}
}

func Wrap[A any](value A) other.Box[A] { return other.Box[A]{} }
";
        assert_eq!(escapes(source, "cell"), Vec::<String>::new());
        assert_eq!(escapes(source, "Read"), Vec::<String>::new());
        assert_eq!(escapes(source, "Offer"), Vec::<String>::new());
        assert_eq!(escapes(source, "Wrap"), ["it names `other.Box` in its signature"]);
    }

    #[test]
    fn a_helper_that_is_opaque_keeps_its_caller_opaque() {
        let source = "package ffi

func Outer[A any](value A) []A { return wrap(value) }

func wrap[A any](value A) []A { return []A{value} }

func Leaky[A any](value A) []any { return leak(value) }

func leak[A any](value A) []any { return []any{value} }
";
        assert_eq!(escapes(source, "Outer"), Vec::<String>::new());
        assert_eq!(escapes(source, "Leaky"), ["it mentions `any` in its signature"]);
    }

    #[test]
    fn a_call_through_a_field_of_a_held_value_keeps_the_value_opaque() {
        let source = "package ffi

import (
	\"container/list\"
	\"sync/atomic\"
)

type Case[A, R any] struct {
	receiving <-chan A
	received  func(A, bool) R
	sending   chan<- A
	value     A
}

func Select[A, R any](first Case[A, R], fallback R) R {
	select {
	case value, open := <-first.receiving:
		return first.received(value, open)
	case first.sending <- first.value:
		return fallback
	}
}

type ioref[A any] struct{ value atomic.Pointer[A] }

func Write[A any](ref *ioref[A], value A) { ref.value.Store(&value) }

type queue[A any] struct{ items list.List }

func Push[A any](queue *queue[A], value A) { queue.items.PushBack(value) }

func Close[A any](channel chan A) { close(channel) }
";
        assert_eq!(escapes(source, "Select"), Vec::<String>::new());
        assert_eq!(escapes(source, "Write"), Vec::<String>::new());
        assert_eq!(
            escapes(source, "Push"),
            ["type parameter A passes a value to `items.PushBack`"]
        );
        assert_eq!(escapes(source, "Close"), Vec::<String>::new());
    }

    #[test]
    fn a_function_literal_hands_on_only_what_its_signature_names() {
        let source = "package ffi

import (
	\"fmt\"

	\"example.com/loop\"
)

func Turn[A any](effect func() A) A {
	var value A
	loop.Turn(func() { value = effect() })
	return value
}

func Later[A any](value A) { loop.Run(func() A { return value }) }

func Print[A any](value A) { loop.Turn(func() { fmt.Println(value) }) }

func Results[A, B any](f func(A) B, element A) []B {
	results := make([]B, 1)
	result := run(func() B { return f(element) })
	results[0] = result
	return results
}

func run[B any](action func() B) B { return action() }
";
        assert_eq!(escapes(source, "Turn"), Vec::<String>::new());
        assert_eq!(escapes(source, "Later"), ["type parameter A passes a value to `loop.Run`"]);
        assert_eq!(escapes(source, "Print"), ["type parameter A passes a value to `fmt.Println`"]);
        assert_eq!(escapes(source, "Results"), Vec::<String>::new());
    }

    #[test]
    fn a_name_reused_for_another_type_keeps_the_value_opaque() {
        let source = "package ffi

import \"example.com/failure\"

type Case[A, R any] struct {
	receiving <-chan A
	received  func(A, bool) R
}

func Select2[A, B, R any](first Case[A, R], second Case[B, R]) R {
	select {
	case value, open := <-first.receiving:
		return first.received(value, open)
	case value, open := <-second.receiving:
		return second.received(value, open)
	}
}

func Both[A, B, C any](combine func(A) func(B) C, left A, right B) C {
	return combine(left)(right)
}

func Launch[A any](action func() A, succeeded func(A), failed func(failure.Error)) {
	value, problem, didFail := attempt(action)
	failures := make(chan *failure.Error, 1)
	failures <- &problem
	if didFail {
		failed(problem)
	} else {
		succeeded(value)
	}
}

func Each[A any](elements []A, f func(A)) {
	for _, element := range elements {
		run(func() struct{} {
			f(element)
			return struct{}{}
		})
	}
}

func attempt[A any](action func() A) (A, failure.Error, bool) { return action(), failure.Error{}, false }

func run[B any](action func() B) B { return action() }
";
        assert_eq!(escapes(source, "Select2"), Vec::<String>::new());
        assert_eq!(escapes(source, "Both"), Vec::<String>::new());
        assert_eq!(escapes(source, "Launch"), Vec::<String>::new());
        assert_eq!(escapes(source, "Each"), Vec::<String>::new());
    }

    #[test]
    fn an_unreadable_file_makes_nothing_opaque() {
        let opacity = foreign_opacity(&[
            "package ffi\n\nfunc F[A any](value A) A { return value }\n\"unterminated\n",
        ]);
        assert!(opacity.unreadable.is_some());
        assert!(opacity.function("F").is_none());
    }
}
