//! Cells that a loop links into a growing structure, allocated in chunks.
//!
//! A loop that builds a list or a tree one cell at a time calls Go's allocator
//! once per cell, and that call costs several times what the rest of the
//! iteration does. Such cells are taken from an `alloc.Cells` chunk instead,
//! which serves many cells with one allocation.
//!
//! A chunk lives as long as any of its cells, so only cells whose neighbours
//! stay alive anyway are chunked: a new cell stored in a variable declared
//! outside the loop that holds that variable's previous value, as in
//! `acc = &Cons{x, acc}`. Every earlier cell is then reachable from the latest
//! one. A loop that replaces its variable instead, keeping the best value so
//! far, allocates one cell at a time, since chunking would let the surviving
//! cell keep its dead neighbours alive.
//!
//! One chunk serves every such cell of one type in the outermost loop of a
//! function body, and is declared just before that loop. It belongs to one
//! invocation of the function, so goroutines never share it. A function
//! literal inside a loop is a function body of its own: a chunk of the
//! enclosing function would be shared by every call of the literal. A labelled
//! `for` that a case expression breaks out of runs once, so it is a block
//! rather than a loop.
//!
//! Chunked cells are ordinary pointers, so reuse may overwrite them in place
//! exactly as it overwrites cells allocated one by one.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType, Name};

use super::walk::{self, Walk};

/// Rewrites the linked cells of every loop, and tells whether it rewrote any.
/// `taken` tells which names a new local must not shadow.
pub fn allocate_linked_cells_in_chunks(
    declarations: &mut [GoDeclaration],
    taken: &dyn Fn(&str) -> bool,
) -> bool {
    let mut chunked = false;
    for declaration in declarations {
        let mut names = FxHashSet::default();
        declaration.for_each_name_mut(&mut |name| {
            let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
            names.insert(name.clone());
        });
        let mut function = Function { names, taken, chunked: false };
        walk::declaration(&mut function, declaration);
        chunked |= function.chunked;
    }
    chunked
}

struct Function<'a> {
    /// Every name the declaration uses, so that a chunk shadows none of them.
    names: FxHashSet<String>,
    taken: &'a dyn Fn(&str) -> bool,
    chunked: bool,
}

/// The chunks of one outermost loop: a cell type and the local holding its chunk.
type Chunks = Vec<(GoType, String)>;

/// The names declared within the innermost loop. An alias is one of them that
/// copies a variable declared outside the loop, or a part of one.
#[derive(Default)]
struct Scope {
    inside: FxHashSet<String>,
    aliases: FxHashMap<String, String>,
}

impl Scope {
    fn declare(&mut self, name: &str, value: Option<&GoExpression>) {
        let outer = value.and_then(|value| self.outer_variable(value)).map(str::to_string);
        self.inside.insert(name.to_string());
        match outer {
            Some(outer) => self.aliases.insert(name.to_string(), outer),
            None => self.aliases.remove(name),
        };
    }

    /// The variable declared outside the loop that `value` reads, directly,
    /// through an alias or through a field.
    fn outer_variable<'a>(&'a self, value: &'a GoExpression) -> Option<&'a str> {
        match value {
            GoExpression::Identifier(name) if !self.inside.contains(name) => Some(name),
            GoExpression::Identifier(name) => self.aliases.get(name).map(String::as_str),
            GoExpression::Field { value, .. } => self.outer_variable(value),
            _ => None,
        }
    }

    /// Whether `value`, or a value stored in it, holds the previous value of
    /// `variable`.
    fn links(&self, value: &GoExpression, variable: &str) -> bool {
        let fields = match value {
            GoExpression::Address(composite) => match composite.as_ref() {
                GoExpression::Composite { fields, .. } => fields,
                _ => return false,
            },
            GoExpression::Composite { fields, .. } => fields,
            _ => return false,
        };
        fields.iter().any(|(_, field)| {
            self.outer_variable(field) == Some(variable) || self.links(field, variable)
        })
    }
}

impl Walk for Function<'_> {
    /// A function body: each outermost loop gets the chunks its cells need.
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        let mut rewritten = Vec::with_capacity(body.len());
        for mut statement in std::mem::take(body) {
            let mut chunks = Chunks::new();
            match &mut statement {
                GoStatement::Loop(_)
                | GoStatement::Range { .. }
                | GoStatement::Counting { .. }
                | GoStatement::CountingDown { .. } => self.loop_(&mut statement, &mut chunks),
                statement => self.statement(statement),
            }
            for (type_, name) in chunks {
                let type_ = GoType::Generic { name: "alloc.Cells".into(), arguments: vec![type_] };
                rewritten.push(GoStatement::Variable { name, type_, value: None });
            }
            rewritten.push(statement);
        }
        *body = rewritten;
    }
}

impl Function<'_> {
    /// A loop, whose body starts a scope of its own.
    fn loop_(&mut self, statement: &mut GoStatement, chunks: &mut Chunks) {
        let mut scope = Scope::default();
        match statement {
            GoStatement::Loop(body) => self.loop_body(body, &mut scope, chunks),
            GoStatement::Range { index, element, iterable, body } => {
                self.expression(iterable);
                if let Some(index) = index {
                    scope.declare(index, None);
                }
                scope.declare(element, None);
                self.loop_body(body, &mut scope, chunks);
            }
            GoStatement::Counting { variable, start, end, body } => {
                self.expression(start);
                self.expression(end);
                scope.declare(variable, None);
                self.loop_body(body, &mut scope, chunks);
            }
            GoStatement::CountingDown { variable, start, body } => {
                self.expression(start);
                scope.declare(variable, None);
                self.loop_body(body, &mut scope, chunks);
            }
            _ => unreachable!("invariant violated: only loops have loop bodies"),
        }
    }

    fn loop_body(&mut self, body: &mut [GoStatement], scope: &mut Scope, chunks: &mut Chunks) {
        for statement in body {
            match statement {
                GoStatement::Define { names, values } => {
                    values.iter_mut().for_each(|value| self.expression(value));
                    for (index, name) in names.iter().enumerate() {
                        let value = (names.len() == values.len()).then(|| &values[index]);
                        scope.declare(name, value);
                    }
                }
                GoStatement::Variable { name, value, .. } => {
                    if let Some(value) = value {
                        self.expression(value);
                    }
                    scope.declare(name, value.as_ref());
                }
                GoStatement::Assign { targets, values } if targets.len() == values.len() => {
                    for (target, value) in targets.iter_mut().zip(values.iter_mut()) {
                        match target {
                            GoExpression::Identifier(variable)
                                if !scope.inside.contains(variable) =>
                            {
                                self.carried(value, variable, scope, chunks)
                            }
                            target => {
                                self.expression(target);
                                self.expression(value);
                            }
                        }
                    }
                }
                GoStatement::If { condition, then, otherwise } => {
                    self.expression(condition);
                    self.loop_body(then, scope, chunks);
                    self.loop_body(otherwise, scope, chunks);
                }
                GoStatement::Switch { value, cases, default } => {
                    if let Some(value) = value {
                        self.expression(value);
                    }
                    for case in cases {
                        case.values.iter_mut().for_each(|value| self.expression(value));
                        self.loop_body(&mut case.body, scope, chunks);
                    }
                    if let Some(default) = default {
                        self.loop_body(&mut default.body, scope, chunks);
                    }
                }
                GoStatement::IfAssert { name, value, then, .. } => {
                    self.expression(value);
                    scope.declare(name, None);
                    self.loop_body(then, scope, chunks);
                }
                GoStatement::LabeledLoop { body: inner, .. } | GoStatement::Block(inner) => {
                    self.loop_body(inner, scope, chunks)
                }
                GoStatement::Loop(_)
                | GoStatement::Range { .. }
                | GoStatement::Counting { .. }
                | GoStatement::CountingDown { .. } => self.loop_(statement, chunks),
                statement => self.statement(statement),
            }
        }
    }

    /// A value stored in `variable`, declared outside the loop. Each cell in it
    /// that no other cell holds is chunked, along with the cells it holds,
    /// when it holds the variable's previous value.
    fn carried(
        &mut self,
        value: &mut GoExpression,
        variable: &str,
        scope: &Scope,
        chunks: &mut Chunks,
    ) {
        match value {
            GoExpression::Address(_) if scope.links(value, variable) => {
                self.chunked_cells(value, chunks)
            }
            GoExpression::Composite { fields, .. } => fields
                .iter_mut()
                .for_each(|(_, field)| self.carried(field, variable, scope, chunks)),
            value => self.expression(value),
        }
    }

    /// Takes every cell in `value`, and every cell stored in one, from chunks.
    fn chunked_cells(&mut self, value: &mut GoExpression, chunks: &mut Chunks) {
        match value {
            GoExpression::Address(composite) => {
                let GoExpression::Composite { type_, fields } = composite.as_mut() else {
                    return self.expression(value);
                };
                if !matches!(type_, GoType::Named(_) | GoType::Generic { .. }) {
                    return self.expression(value);
                }
                fields.iter_mut().for_each(|(_, field)| self.chunked_cells(field, chunks));
                let chunk = self.chunk(type_, chunks);
                let composite = std::mem::replace(composite.as_mut(), GoExpression::Integer(0));
                let new = GoExpression::Field {
                    value: Box::new(GoExpression::Identifier(chunk)),
                    name: "New".into(),
                };
                *value = GoExpression::Call { function: Box::new(new), arguments: vec![composite] };
                self.chunked = true;
            }
            GoExpression::Composite { fields, .. } => {
                fields.iter_mut().for_each(|(_, field)| self.chunked_cells(field, chunks))
            }
            value => self.expression(value),
        }
    }

    /// The local holding the chunk for cells of `type_`, declared once per loop.
    fn chunk(&mut self, type_: &GoType, chunks: &mut Chunks) -> String {
        if let Some((_, name)) = chunks.iter().find(|(chunked, _)| chunked == type_) {
            return name.clone();
        }
        let base = format!("{}Cells", lower_first(type_name(type_)));
        let mut name = base.clone();
        let mut counter = 2;
        while self.names.contains(&name) || (self.taken)(&name) {
            name = format!("{base}{counter}");
            counter += 1;
        }
        self.names.insert(name.clone());
        chunks.push((type_.clone(), name.clone()));
        name
    }
}

fn type_name(type_: &GoType) -> &str {
    match type_ {
        GoType::Named(name) | GoType::Generic { name, .. } => name,
        _ => unreachable!("invariant violated: only named types are chunked"),
    }
}

pub(super) fn lower_first(name: &str) -> String {
    let mut characters = name.chars();
    match characters.next() {
        Some(first) => first.to_lowercase().chain(characters).collect(),
        None => String::new(),
    }
}
