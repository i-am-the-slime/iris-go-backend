//! Cells that a recursive function builds into its result, allocated in chunks.
//!
//! A function such as `sumTree` in
//!
//! ```go
//! func sumTree(depth int32, number int32) *Expr {
//!     if depth == 0 {
//!         return &Expr{Tag: ExprVal, FieldB0: number}
//!     }
//!     return &Expr{Tag: ExprAdd, FieldA0: sumTree(depth-1, number+1), FieldA1: sumTree(depth-1, number)}
//! }
//! ```
//!
//! calls Go's allocator once per cell of the tree it returns. It becomes a
//! wrapper that declares an `alloc.Cells` chunk and a worker that takes every
//! cell it returns from that chunk, passing the chunk on to the calls of
//! itself whose results it returns:
//!
//! ```go
//! func sumTree(depth int32, number int32) *Expr {
//!     var cells alloc.Cells[Expr]
//!     return sumTreeChunked(depth, number, &cells)
//! }
//! ```
//!
//! Only cells that a `return` builds, and calls whose results such a cell
//! holds or a `return` returns, use the chunk. Every cell taken from it is
//! then reachable from the result when the outermost call returns, as every
//! cell of a block of `blocks.rs` is from its root, so a chunk outlives its
//! cells only once code drops the root and keeps a part of the tree. A call
//! whose result the function might drop calls the wrapper, with a chunk of its
//! own.
//!
//! The chunk belongs to one call of the wrapper, so goroutines never share
//! it. Chunked cells are ordinary pointers, so reuse may overwrite them in
//! place exactly as it overwrites cells allocated one by one.

use rustc_hash::FxHashSet;

use crate::go_traversal::{self, Walk};
use crate::naming::numbered;
use crate::syntax::{DeclarationNames, GoDeclaration, GoExpression, GoStatement, GoType};

/// A worker added for a builder: its name and the builder it works for.
pub struct Worker {
    pub name: String,
    pub builder: String,
}

/// Splits every recursive function that builds its result out of cells of
/// its result type into a wrapper and a chunked worker, and returns the
/// workers. `taken` tells which names a new declaration must not take.
pub fn allocate_built_cells_in_chunks(
    declarations: &mut Vec<GoDeclaration>,
    names: &mut Vec<DeclarationNames>,
    taken: &dyn Fn(&str) -> bool,
) -> Vec<Worker> {
    let mut workers = vec![];
    let mut added = FxHashSet::default();
    let mut index = 0;
    while index < declarations.len() {
        let Some(builder) = Builder::of(&declarations[index]) else {
            index += 1;
            continue;
        };
        let worker_name = numbered(&format!("{}Chunked", builder.name), |name| {
            taken(name) || added.contains(name)
        });
        let chunk = numbered("cells", |name| names[index].names.contains(name));
        let GoDeclaration::Function { name, parameters, result, body } = &mut declarations[index]
        else {
            unreachable!("invariant violated: builders are functions")
        };
        let mut chunked = Chunked { builder: &builder, worker: &worker_name, chunk: &chunk };
        let mut worker_body = std::mem::take(body);
        chunked.block(&mut worker_body);
        *body = wrapper_body(&builder, parameters, &worker_name, &chunk);
        let mut worker_parameters = parameters.clone();
        worker_parameters.push((chunk.clone(), GoType::Pointer(Box::new(builder.chunk_type()))));
        let mut worker = GoDeclaration::Function {
            name: worker_name.clone(),
            parameters: worker_parameters,
            result: result.clone(),
            body: worker_body,
        };
        workers.push(Worker { name: worker_name.clone(), builder: name.clone() });
        added.insert(worker_name);
        let worker_names = worker.declared_names();
        names[index].names.insert(chunk.clone());
        declarations.insert(index + 1, worker);
        names.insert(index + 1, worker_names);
        index += 2;
    }
    workers
}

/// A function that returns a pointer to a named struct and builds some of
/// what it returns out of such cells and calls of itself.
struct Builder {
    name: String,
    cell: String,
}

impl Builder {
    fn of(declaration: &GoDeclaration) -> Option<Builder> {
        let GoDeclaration::Function { name, parameters, result: Some(GoType::Pointer(cell)), body } =
            declaration
        else {
            return None;
        };
        let GoType::Named(cell) = cell.as_ref() else { return None };
        if parameters.iter().any(|(_, type_)| might_hold_cells(type_)) {
            return None;
        }
        let builder = Builder { name: name.clone(), cell: cell.clone() };
        let mut found = Found::default();
        builder.returns(body, &mut found);
        (found.cells && found.calls).then_some(builder)
    }

    fn chunk_type(&self) -> GoType {
        GoType::Generic {
            name: "alloc.Cells".into(),
            arguments: vec![GoType::Named(self.cell.clone())],
        }
    }

    /// What the `return`s of a block build, outside function literals.
    fn returns(&self, body: &[GoStatement], found: &mut Found) {
        for statement in body {
            match statement {
                GoStatement::Return(Some(value)) => self.built(value, found),
                GoStatement::If { then, otherwise, .. } => {
                    self.returns(then, found);
                    self.returns(otherwise, found);
                }
                GoStatement::Switch { cases, default, .. } => {
                    cases.iter().for_each(|case| self.returns(&case.body, found));
                    if let Some(default) = default {
                        self.returns(&default.body, found);
                    }
                }
                GoStatement::IfAssert { then: body, .. }
                | GoStatement::Range { body, .. }
                | GoStatement::Counting { body, .. }
                | GoStatement::CountingDown { body, .. }
                | GoStatement::Loop(body)
                | GoStatement::LabeledLoop { body, .. } => self.returns(body, found),
                _ => {}
            }
        }
    }

    fn built(&self, value: &GoExpression, found: &mut Found) {
        match value {
            GoExpression::Attributed { value, .. } => self.built(value, found),
            GoExpression::Call { function, .. } if self.calls_itself(function) => {
                found.calls = true
            }
            GoExpression::Address(composite) => {
                if let Some(fields) = self.cell_fields(composite) {
                    found.cells = true;
                    fields.iter().for_each(|(_, field)| self.built(field, found));
                }
            }
            _ => {}
        }
    }

    fn calls_itself(&self, function: &GoExpression) -> bool {
        matches!(function, GoExpression::Identifier(name) if *name == self.name)
    }

    fn cell_fields<'a>(
        &self,
        composite: &'a GoExpression,
    ) -> Option<&'a Vec<(Option<String>, GoExpression)>> {
        match composite {
            GoExpression::Composite { type_: GoType::Named(type_), fields }
                if *type_ == self.cell =>
            {
                Some(fields)
            }
            _ => None,
        }
    }
}

/// Whether a value of `type_` might hold a cell. Any named type might, since
/// its declaration is not at hand. A builder that takes a cell would rebuild part of it and share the rest, as an insert
/// copies the path to a tree's new leaf. The copies of one call then die at
/// different times, a chunk keeps the dead ones alive with the live, and the
/// dead hold on to the versions they copied: chunks would keep every version
/// of the tree alive.
/// The predeclared types that hold no pointer.
const SCALARS: &[&str] = &[
    "bool", "byte", "float32", "float64", "int", "int8", "int16", "int32", "int64", "rune",
    "string", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr",
];

fn might_hold_cells(type_: &GoType) -> bool {
    match type_ {
        GoType::Named(name) => !SCALARS.contains(&name.as_str()),
        GoType::Slice(element) | GoType::Pointer(element) => might_hold_cells(element),
        GoType::Function { parameters, result } => {
            parameters.iter().any(might_hold_cells)
                || result.as_deref().is_some_and(might_hold_cells)
        }
        GoType::Struct(_) | GoType::Any | GoType::Erased(_) => true,
        GoType::Generic { arguments, .. } | GoType::Results(arguments) => {
            arguments.iter().any(might_hold_cells)
        }
        GoType::Int
        | GoType::Float64
        | GoType::Bool
        | GoType::Rune
        | GoType::String
        | GoType::EmptyStruct => false,
    }
}

#[derive(Default)]
struct Found {
    cells: bool,
    calls: bool,
}

/// `var cells alloc.Cells[T]; return worker(parameters..., &cells)`.
fn wrapper_body(
    builder: &Builder,
    parameters: &[(String, GoType)],
    worker: &str,
    chunk: &str,
) -> Vec<GoStatement> {
    let mut arguments: Vec<GoExpression> =
        parameters.iter().map(|(name, _)| GoExpression::Identifier(name.clone())).collect();
    arguments.push(GoExpression::Address(Box::new(GoExpression::Identifier(chunk.into()))));
    vec![
        GoStatement::Variable { name: chunk.into(), type_: builder.chunk_type(), value: None },
        GoStatement::Return(Some(GoExpression::Call {
            function: Box::new(GoExpression::Identifier(worker.into())),
            arguments,
        })),
    ]
}

/// Rewrites a builder's body into its worker's.
struct Chunked<'a> {
    builder: &'a Builder,
    worker: &'a str,
    chunk: &'a str,
}

impl Walk for Chunked<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Return(Some(value)) => self.built(value),
            statement => go_traversal::statement(self, statement),
        }
    }

    /// A function literal's `return`s are its own.
    fn expression(&mut self, value: &mut GoExpression) {
        if !matches!(value, GoExpression::Function { .. }) {
            go_traversal::expression(self, value)
        }
    }
}

impl Chunked<'_> {
    /// A value the worker returns: its cells come from the chunk, and the calls
    /// of the builder in it pass the chunk on.
    fn built(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Attributed { value, .. } => self.built(value),
            GoExpression::Call { function, arguments } if self.builder.calls_itself(function) => {
                arguments.iter_mut().for_each(|argument| self.expression(argument));
                **function = GoExpression::Identifier(self.worker.into());
                arguments.push(GoExpression::Identifier(self.chunk.into()));
            }
            GoExpression::Address(composite) if self.builder.cell_fields(composite).is_some() => {
                let GoExpression::Composite { fields, .. } = composite.as_mut() else {
                    unreachable!("invariant violated: a cell is a composite")
                };
                fields.iter_mut().for_each(|(_, field)| self.built(field));
                let cell = std::mem::replace(composite.as_mut(), GoExpression::Integer(0));
                let new = GoExpression::Field {
                    value: Box::new(GoExpression::Identifier(self.chunk.into())),
                    name: "New".into(),
                };
                *value = GoExpression::Call { function: Box::new(new), arguments: vec![cell] };
            }
            value => self.expression(value),
        }
    }
}
