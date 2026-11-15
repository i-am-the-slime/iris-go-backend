//! Settles the names of a declaration's locals once its Go scopes are known.
//!
//! Emission names a local before it knows where in the Go code the local will
//! end up, so it marks every name it had to number, and names a record value
//! by a token for the record whose Go name packaging chooses. This pass gives
//! each marked local the plainest name that clashes with nothing in its Go
//! scope: locals in separate function literals or branches may share a name,
//! and only a local that would shadow or be shadowed by another of the same
//! name, or hide something its scope refers to, is numbered.

use rustc_hash::FxHashMap;

use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};
use crate::naming::{GO_PREDECLARED, VALUE, capitalise, go_safe};

use crate::walk::{self, Walk as _};

/// Follows a name that emission numbered, before the number.
pub(super) const NUMBERED: char = 'ǂ';
/// Encloses the index of a record whose Go name names a value.
pub(super) const RECORD: char = 'ǀ';

/// The token for the record at `index` in the emitter's typed records.
pub(super) fn record_token(index: usize) -> String {
    format!("{RECORD}{index}{RECORD}")
}

/// Whether the pass is to settle the name.
pub(super) fn is_marked(name: &str) -> bool {
    name.contains([NUMBERED, RECORD])
}

/// Gives the marked locals and labels of a declaration their names, the
/// records among them named as `records` says, by token index.
pub(super) fn settle(declaration: &mut GoDeclaration, records: &[String]) {
    let mut walk = Walk::default();
    match declaration {
        GoDeclaration::Function { parameters, result, body, .. } => {
            walk.function(parameters, result.as_mut(), body);
        }
        GoDeclaration::Variable { value, type_, .. } => {
            let root = walk.enter();
            if let Some(type_) = type_ {
                walk.type_(type_);
            }
            walk.expression(value);
            walk.exit(root);
        }
        _ => return,
    }
    if walk.entities.iter().all(|entity| !entity.marked) && walk.labels.is_empty() {
        return;
    }
    let names = walk.choose(records);
    let labels = settled_labels(&walk.labels, records);
    let mut apply = Apply { names: &names, labels: &labels };
    match declaration {
        GoDeclaration::Function { parameters, body, .. } => {
            for (parameter, _) in parameters.iter_mut() {
                apply.name(parameter);
            }
            apply.block(body);
        }
        GoDeclaration::Variable { value, .. } => apply.expression(value),
        _ => {}
    }
}

/// The name a marked name stands for: numbers dropped, record tokens spelled
/// by the record's name.
fn wanted(marked: &str, records: &[String]) -> String {
    let mut out = String::new();
    let mut characters = marked.chars().peekable();
    while let Some(character) = characters.next() {
        match character {
            NUMBERED => while characters.next_if(char::is_ascii_digit).is_some() {},
            RECORD => {
                let mut index = 0usize;
                while let Some(digit) = characters.next_if(char::is_ascii_digit) {
                    index = index * 10 + digit.to_digit(10).unwrap_or(0) as usize;
                }
                characters.next_if_eq(&RECORD);
                let name = records.get(index).map_or("record", String::as_str);
                if out.is_empty() {
                    out.push_str(name);
                } else {
                    out.push_str(&capitalise(name));
                }
            }
            character => out.push(character),
        }
    }
    if out.is_empty() {
        return VALUE.into();
    }
    go_safe(&out).to_string()
}

/// Labels live apart from other names, one per loop in a function, and are
/// rare: they are numbered in order where they collide.
fn settled_labels(labels: &[String], records: &[String]) -> FxHashMap<String, String> {
    let mut settled = FxHashMap::default();
    let fixed: Vec<&String> = labels.iter().filter(|label| !is_marked(label)).collect();
    let mut taken: Vec<String> = fixed.iter().map(|label| label.to_string()).collect();
    for label in labels.iter().filter(|label| is_marked(label)) {
        if settled.contains_key(label) {
            continue;
        }
        let base = wanted(label, records);
        let mut name = base.clone();
        let mut counter = 2;
        while taken.contains(&name) {
            name = format!("{base}{counter}");
            counter += 1;
        }
        taken.push(name.clone());
        settled.insert(label.clone(), name);
    }
    settled
}

/// A Go scope, by the interval its preorder numbering spans.
#[derive(Debug, Clone, Copy)]
struct Scope {
    enter: usize,
    exit: usize,
}

#[derive(Debug)]
struct Entity {
    original: String,
    scope: usize,
    marked: bool,
}

/// A placeholder for a marked entity's name between the two walks.
fn placeholder(entity: usize) -> String {
    format!("\u{0}{entity}")
}

#[derive(Default)]
struct Walk {
    scopes: Vec<Scope>,
    counter: usize,
    /// The open scopes, innermost last, with the names they bind.
    open: Vec<(usize, FxHashMap<String, usize>)>,
    entities: Vec<Entity>,
    /// Names that refer to no local, with the scope they occur in.
    free: FxHashMap<String, Vec<usize>>,
    labels: Vec<String>,
}

impl Walk {
    fn enter(&mut self) -> usize {
        let id = self.scopes.len();
        self.scopes.push(Scope { enter: self.counter, exit: usize::MAX });
        self.counter += 1;
        self.open.push((id, FxHashMap::default()));
        id
    }

    fn exit(&mut self, id: usize) {
        self.scopes[id].exit = self.counter;
        self.counter += 1;
        self.open.pop();
    }

    fn current(&self) -> Option<usize> {
        self.open.last().map(|(id, _)| *id)
    }

    fn bind(&mut self, name: &mut String) {
        if name == "_" {
            return;
        }
        let scope = self.current().expect("invariant violated: a binder outside every scope");
        let (_, bound) = self.open.last_mut().expect("invariant violated: no open scope");
        if let Some(&entity) = bound.get(name.as_str()) {
            // `a, b := …` redeclares nothing that its scope already binds.
            if self.entities[entity].marked {
                *name = placeholder(entity);
            }
            return;
        }
        let entity = self.entities.len();
        let marked = is_marked(name);
        self.entities.push(Entity { original: name.clone(), scope, marked });
        bound.insert(name.clone(), entity);
        if marked {
            *name = placeholder(entity);
        }
    }

    /// A binder Go introduces itself, as `ok` in `if v, ok := x.(T); ok`.
    fn implicit(&mut self, name: &str) {
        let mut name = name.to_string();
        self.bind(&mut name);
    }

    fn reference(&mut self, name: &mut String) {
        let found = self.open.iter().rev().find_map(|(_, bound)| bound.get(name.as_str()).copied());
        match found {
            Some(entity) if self.entities[entity].marked => *name = placeholder(entity),
            Some(_) => {}
            None => self.free_name(name.clone()),
        }
    }

    fn free_name(&mut self, name: String) {
        // Outside every scope, such as in a declaration's signature, a name
        // hides nothing a local could.
        let Some(scope) = self.current() else { return };
        self.free.entry(name).or_default().push(scope);
    }

    fn function(
        &mut self,
        parameters: &mut [(String, GoType)],
        result: Option<&mut GoType>,
        body: &mut Vec<GoStatement>,
    ) {
        // A function's signature is in the scope around it; its parameters
        // are in scope in its body alone.
        for (_, type_) in parameters.iter_mut() {
            self.type_(type_);
        }
        if let Some(result) = result {
            self.type_(result);
        }
        let scope = self.enter();
        for (parameter, _) in parameters.iter_mut() {
            self.bind(parameter);
        }
        self.statements(body);
        self.exit(scope);
    }

    fn statements(&mut self, statements: &mut [GoStatement]) {
        for statement in statements {
            self.statement(statement);
        }
    }
}

impl walk::Walk for Walk {
    fn block(&mut self, statements: &mut Vec<GoStatement>) {
        let scope = self.enter();
        self.statements(statements);
        self.exit(scope);
    }

    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values } => {
                values.iter_mut().for_each(|value| self.expression(value));
                names.iter_mut().for_each(|name| self.bind(name));
            }
            GoStatement::Variable { name, type_, value } => {
                self.type_(type_);
                if let Some(value) = value {
                    self.expression(value);
                }
                self.bind(name);
                self.bind(name);
            }
            GoStatement::IfAssert { name, value, type_, then } => {
                self.expression(value);
                self.type_(type_);
                let scope = self.enter();
                self.bind(name);
                self.implicit("ok");
                self.statements(then);
                self.exit(scope);
            }
            GoStatement::Range { index, element, iterable, body } => {
                self.expression(iterable);
                let scope = self.enter();
                if let Some(index) = index {
                    self.bind(index);
                }
                self.bind(element);
                self.statements(body);
                self.exit(scope);
            }
            GoStatement::Counting { variable, start, end, body } => {
                self.expression(start);
                let scope = self.enter();
                self.bind(variable);
                self.expression(end);
                self.statements(body);
                self.exit(scope);
            }
            GoStatement::CountingDown { variable, start, body } => {
                self.expression(start);
                let scope = self.enter();
                self.bind(variable);
                self.statements(body);
                self.exit(scope);
            }
            GoStatement::LabeledLoop { label, .. } | GoStatement::BreakTo(label) => {
                self.labels.push(label.clone());
                walk::statement(self, statement);
            }
            statement => walk::statement(self, statement),
        }
    }

    fn expression(&mut self, expression: &mut GoExpression) {
        match expression {
            GoExpression::Identifier(name) => self.reference(name),
            GoExpression::Qualified { package, .. } => self.free_name(package.clone()),
            GoExpression::Type(type_) => self.type_(type_),
            GoExpression::Function { parameters, result, body } => {
                self.function(parameters, result.as_mut(), body);
            }
            GoExpression::Composite { type_, .. }
            | GoExpression::Conversion { type_, .. }
            | GoExpression::TypeAssertion { type_, .. } => {
                self.type_(type_);
                walk::expression(self, expression);
            }
            GoExpression::Instantiation { function, arguments } => {
                self.expression(function);
                arguments.iter_mut().for_each(|argument| self.type_(argument));
            }
            expression => walk::expression(self, expression),
        }
    }
}

impl Walk {
    fn type_(&mut self, type_: &mut GoType) {
        match type_ {
            GoType::Named(name) => self.type_name(name.clone()),
            GoType::Generic { name, arguments } => {
                self.type_name(name.clone());
                arguments.iter_mut().for_each(|argument| self.type_(argument));
            }
            GoType::Int => self.free_name("int".into()),
            GoType::Float64 => self.free_name("float64".into()),
            GoType::Bool => self.free_name("bool".into()),
            GoType::Rune => self.free_name("rune".into()),
            GoType::String => self.free_name("string".into()),
            GoType::Any | GoType::Erased(_) => self.free_name("any".into()),
            GoType::EmptyStruct => {}
            GoType::Slice(element) | GoType::Pointer(element) => self.type_(element),
            GoType::Function { parameters, result } => {
                parameters.iter_mut().for_each(|parameter| self.type_(parameter));
                if let Some(result) = result {
                    self.type_(result);
                }
            }
            GoType::Struct(fields) => fields.iter_mut().for_each(|(_, field)| self.type_(field)),
        }
    }

    /// `pkg.Name` names `pkg`, `Name` names itself, and a generic spelled
    /// whole, `Name[pkg.T]`, names each.
    fn type_name(&mut self, spelled: String) {
        let mut start = 0;
        let mut qualified = false;
        let bytes: Vec<(usize, char)> = spelled.char_indices().collect();
        for (position, &(at, character)) in bytes.iter().enumerate() {
            let ends = bytes.get(position + 1).is_none_or(|&(_, next)| {
                !(next.is_alphanumeric() || next == '_')
            });
            if !(character.is_alphanumeric() || character == '_') {
                qualified = character == '.';
                start = at + character.len_utf8();
                continue;
            }
            if ends {
                let word = &spelled[start..at + character.len_utf8()];
                let is_qualifier =
                    bytes.get(position + 1).is_some_and(|&(_, next)| next == '.');
                if is_qualifier || !qualified {
                    self.free_name(word.to_string());
                }
            }
        }
    }

    /// Each marked entity's name, in the order they bind: the plainest that
    /// no local it shadows or that shadows it, and no name its scope refers
    /// to, already has.
    fn choose(&self, records: &[String]) -> Vec<String> {
        let mut names: Vec<Option<String>> = self
            .entities
            .iter()
            .map(|entity| (!entity.marked).then(|| entity.original.clone()))
            .collect();
        let mut by_name: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        for (entity, name) in names.iter().enumerate() {
            if let Some(name) = name {
                by_name.entry(name.clone()).or_default().push(self.entities[entity].scope);
            }
        }
        for entity in 0..self.entities.len() {
            if names[entity].is_some() {
                continue;
            }
            let scope = self.scopes[self.entities[entity].scope];
            let base = wanted(&self.entities[entity].original, records);
            let clashes = |candidate: &str| {
                GO_PREDECLARED.contains(&candidate)
                    || self.free.get(candidate).is_some_and(|scopes| {
                        scopes.iter().any(|&other| self.within(self.scopes[other], scope))
                    })
                    || by_name.get(candidate).is_some_and(|scopes| {
                        scopes.iter().any(|&other| {
                            let other = self.scopes[other];
                            self.within(other, scope) || self.within(scope, other)
                        })
                    })
            };
            let mut name = base.clone();
            let mut counter = 2;
            while clashes(&name) {
                name = format!("{base}{counter}");
                counter += 1;
            }
            by_name.entry(name.clone()).or_default().push(self.entities[entity].scope);
            names[entity] = Some(name);
        }
        names.into_iter().map(|name| name.unwrap_or_default()).collect()
    }

    /// Whether `inner` lies within `outer` or is it.
    fn within(&self, inner: Scope, outer: Scope) -> bool {
        outer.enter <= inner.enter && inner.exit <= outer.exit
    }
}

struct Apply<'a> {
    names: &'a [String],
    labels: &'a FxHashMap<String, String>,
}

impl Apply<'_> {
    fn name(&mut self, name: &mut String) {
        if let Some(entity) = name.strip_prefix('\u{0}') {
            let entity: usize = entity.parse().expect("invariant violated: a placeholder's index");
            *name = self.names[entity].clone();
        }
    }

    fn label(&mut self, label: &mut String) {
        if let Some(settled) = self.labels.get(label.as_str()) {
            *label = settled.clone();
        }
    }
}

impl walk::Walk for Apply<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, .. } => names.iter_mut().for_each(|name| self.name(name)),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                self.name(name)
            }
            GoStatement::Range { index, element, .. } => {
                index.iter_mut().for_each(|index| self.name(index));
                self.name(element);
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.name(variable)
            }
            GoStatement::LabeledLoop { label, .. } | GoStatement::BreakTo(label) => {
                self.label(label)
            }
            _ => {}
        }
        walk::statement(self, statement);
    }

    fn expression(&mut self, expression: &mut GoExpression) {
        match expression {
            GoExpression::Identifier(name) => self.name(name),
            GoExpression::Function { parameters, .. } => {
                parameters.iter_mut().for_each(|(parameter, _)| self.name(parameter))
            }
            _ => {}
        }
        walk::expression(self, expression);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn literal(parameter: &str) -> GoExpression {
        GoExpression::Function {
            parameters: vec![(parameter.into(), GoType::Int)],
            result: Some(GoType::Int),
            body: vec![GoStatement::Return(Some(GoExpression::Identifier(parameter.into())))],
        }
    }

    fn settled(declaration: &mut GoDeclaration) -> String {
        settle(declaration, &["layoutTree".into()]);
        declaration.render()
    }

    #[test]
    fn locals_in_separate_function_literals_share_a_name() {
        let mut declaration = GoDeclaration::Variable {
            name: "both".into(),
            type_: None,
            value: GoExpression::Call {
                function: Box::new(GoExpression::Identifier("pair".into())),
                arguments: vec![literal("done"), literal(&format!("done{NUMBERED}2"))],
            },
        };
        let rendered = settled(&mut declaration);
        assert!(!rendered.contains("done2"), "{rendered}");
        assert_eq!(rendered.matches("func(done int)").count(), 2, "{rendered}");
    }

    #[test]
    fn a_local_that_would_shadow_another_is_numbered() {
        let inner = GoExpression::Function {
            parameters: vec![(format!("x{NUMBERED}2"), GoType::Int)],
            result: Some(GoType::Int),
            body: vec![GoStatement::Return(Some(GoExpression::Binary {
                operator: "+",
                left: Box::new(GoExpression::Identifier("x".into())),
                right: Box::new(GoExpression::Identifier(format!("x{NUMBERED}2"))),
            }))],
        };
        let mut declaration = GoDeclaration::Function {
            name: "f".into(),
            parameters: vec![("x".into(), GoType::Int)],
            result: None,
            body: vec![GoStatement::Expression(inner)],
        };
        let rendered = settled(&mut declaration);
        assert!(rendered.contains("func(x2 int) int"), "{rendered}");
        assert!(rendered.contains("return x + x2"), "{rendered}");
    }

    #[test]
    fn a_local_never_hides_a_name_its_scope_refers_to() {
        let mut declaration = GoDeclaration::Function {
            name: "f".into(),
            parameters: vec![(format!("array{NUMBERED}2"), GoType::Int)],
            result: None,
            body: vec![GoStatement::Expression(GoExpression::Call {
                function: Box::new(GoExpression::Qualified {
                    package: "array".into(),
                    name: "Length".into(),
                }),
                arguments: vec![GoExpression::Identifier(format!("array{NUMBERED}2"))],
            })],
        };
        let rendered = settled(&mut declaration);
        assert!(rendered.contains("array.Length(array2)"), "{rendered}");
    }

    #[test]
    fn a_record_value_is_called_after_its_record() {
        let token = record_token(0);
        let mut declaration = GoDeclaration::Function {
            name: "f".into(),
            parameters: vec![(token.clone(), GoType::Named("LayoutTree".into()))],
            result: None,
            body: vec![GoStatement::Define {
                names: vec![format!("{token}Captured")],
                values: vec![GoExpression::Identifier(token)],
            }],
        };
        let rendered = settled(&mut declaration);
        assert!(rendered.contains("f(layoutTree LayoutTree)"), "{rendered}");
        assert!(rendered.contains("layoutTreeCaptured := layoutTree"), "{rendered}");
    }
}
