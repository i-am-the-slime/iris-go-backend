use std::fmt;
use std::ops::Range;

use rustc_hash::FxHashSet;

#[derive(Debug, Clone, Default)]
pub struct Opacity {
    pub functions: Vec<OpaqueDeclaration>,
    pub types: Vec<OpaqueDeclaration>,
    pub unreadable: Option<String>,
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
    &["append", "cap", "clear", "copy", "delete", "len", "make", "max", "min", "new"];

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

fn qualified(tokens: &[Token]) -> Option<String> {
    tokens.windows(3).find_map(|window| match window {
        [Token::Word(package), dot, Token::Word(name)] if dot.is(".") => {
            Some(format!("{package}.{name}"))
        }
        _ => None,
    })
}

fn qualified_instantiation(tokens: &[Token]) -> Option<String> {
    tokens.windows(4).find_map(|window| match window {
        [Token::Word(package), dot, Token::Word(name), open]
            if dot.is(".") && open.is("[") && !OPAQUE_GENERIC_PACKAGES.contains(&package.as_str()) =>
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
            let name = closing(declaration, 0).and_then(|end| declaration.get(end + 1));
            if let Some(name) = name.and_then(Token::word) {
                self.methods.insert(name.to_string());
            }
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
        let last = declaration.len() - 1;
        let body_start = match declaration.last() {
            Some(token) if token.is("}") => opening(declaration, last),
            _ => None,
        };
        let signature = &declaration[position..body_start.unwrap_or(declaration.len())];
        let Some(end) = signature.first().filter(|token| token.is("(")).and(closing(signature, 0))
        else {
            return;
        };
        self.functions.push(Function {
            name: name.to_string(),
            type_parameters,
            parameters: signature[1..end].to_vec(),
            results: signature[end + 1..].to_vec(),
            body: body_start.map(|start| declaration[start + 1..last].to_vec()),
        });
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
        loop {
            let surroundings = self.surroundings(&escaping, &signature_escaping, &opaque);
            let next: FxHashSet<String> = self
                .functions
                .iter()
                .filter(|function| surroundings.escapes(function).is_empty())
                .map(|function| function.name.clone())
                .collect();
            if next == opaque {
                break;
            }
            opaque = next;
        }
        let surroundings = self.surroundings(&escaping, &signature_escaping, &opaque);
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
        Opacity { functions: functions.collect(), types: types.collect(), unreadable: None }
    }

    fn surroundings<'p>(
        &'p self,
        escaping: &'p FxHashSet<String>,
        signature_escaping: &'p FxHashSet<String>,
        opaque: &'p FxHashSet<String>,
    ) -> Surroundings<'p> {
        Surroundings {
            escaping,
            signature_escaping,
            functions: &self.functions,
            methods: &self.methods,
            opaque,
        }
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

fn parameter_names(parameters: &[TypeParameter]) -> Vec<String> {
    parameters.iter().map(|parameter| parameter.name.clone()).collect()
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
            if depth == 0 && token.is("{") {
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
    methods: &'p FxHashSet<String>,
    opaque: &'p FxHashSet<String>,
}

impl Surroundings<'_> {
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
    assignments: Vec<Assignment>,
    blocks: FxHashSet<usize>,
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
            assignments: vec![],
            blocks: FxHashSet::default(),
        };
        flow.declare_parameters(&function.parameters);
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
                    if typed {
                        self.tainted.insert(name);
                    }
                }
            }
        }
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
        let right = match equals {
            Some(equals) => {
                declared_equals.insert(equals);
                equals + 1..specification.end
            }
            None => specification.end..specification.end,
        };
        Some(Assignment { left, right, defines: true, declared_type })
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

    fn holds_values(&self, name: &str) -> bool {
        self.locals.contains(name) && self.tainted.contains(name)
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
            return (!after_func && !converts)
                .then(|| "passes a value to the result of an expression".to_string());
        }
        let callee = previous.word()?;
        let qualifier = open
            .checked_sub(2)
            .filter(|&dot| tokens[dot].is("."))
            .and_then(|dot| dot.checked_sub(1))
            .and_then(|root| tokens[root].word());
        match qualifier {
            Some(root) if GENERIC_PACKAGES.contains(&root) && !self.locals.contains(root) => None,
            Some(root) => Some(format!("passes a value to `{root}.{callee}`")),
            None if previous.is_keyword() => None,
            None if BUILTINS.contains(&callee) => self.builtin_escape(callee, open, end),
            None if callee == self.parameter
                || self.surroundings.opaque.contains(callee)
                || self.holds_values(callee) =>
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
        if !self.surroundings.methods.contains(name) {
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
        (!self.holds_values(root)).then(|| format!("sends a value on `{root}`"))
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

func (cell Cell[A]) Reset() {}

func Reset[A any](cell Cell[A]) { cell.Reset() }

func Wrap[A any](value A) Cell[A] { return Cell[A]{value: value} }
";
        assert_eq!(escapes(source, "Reset"), ["type parameter A uses the method `Reset`"]);
        assert_eq!(escapes(source, "Wrap"), Vec::<String>::new());
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
    fn an_unreadable_file_makes_nothing_opaque() {
        let opacity = foreign_opacity(&[
            "package ffi\n\nfunc F[A any](value A) A { return value }\n\"unterminated\n",
        ]);
        assert!(opacity.unreadable.is_some());
        assert!(opacity.function("F").is_none());
    }
}
