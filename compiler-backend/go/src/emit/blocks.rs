//! Cells of one type that a single expression nests, allocated together.
//!
//! A constructor expression such as `Add (Mul (Val n) x) (Sub y (Val 1))`
//! becomes `&Expr{Add, &Expr{Mul, &Expr{Val, n}, x}, &Expr{Sub, y, &Expr{Val, 1}}}`,
//! one allocation per cell. When at least three cells of one type nest like
//! this they are taken from one slice instead, filled by index:
//!
//! ```go
//! exprs := make([]Expr, 5)
//! exprs[0] = Expr{Tag: ExprAdd, Field0: &exprs[1], Field1: &exprs[3]}
//! exprs[1] = Expr{Tag: ExprMul, Field0: &exprs[2], Field1: x}
//! ...
//! return &exprs[0]
//! ```
//!
//! A slice lives as long as any of its cells. Every cell of a block is
//! reachable from the root when the block is built, so a block outlives its
//! cells only once code drops the root and keeps a descendant, and then by
//! at most the size of one expression.
//!
//! The block is built just before the statement holding the expression, so
//! only expressions that statement always evaluates are rewritten: not the
//! right operand of `&&` or `||`, and not the body of a function literal,
//! which is a block of its own. The cells' fields are pure values, which may
//! be evaluated before the rest of the statement, as the emitter evaluates a
//! case expression it hoists out of an argument list.
//!
//! Cells from a block are ordinary pointers, so reuse may overwrite them in
//! place. Cells that a loop links together have already been taken from
//! `alloc.Cells` chunks, which are cheaper still, and are left alone.

use rustc_hash::FxHashSet;

use crate::go_traversal::{self, Walk};
use crate::naming::{lower_first, numbered};
use crate::syntax::{
    DeclarationNames, GoBinaryOperator, GoBuiltin, GoDeclaration, GoExpression, GoStatement, GoType,
};

/// The fewest cells of one type in one expression that are allocated together.
const MINIMUM_CELLS: usize = 3;

/// Rewrites every expression that nests enough cells of one type. `taken`
/// tells which names a new local must not shadow.
pub fn allocate_nested_cells_together(
    declarations: &mut [GoDeclaration],
    names: &mut [DeclarationNames],
    taken: &dyn Fn(&str) -> bool,
) {
    for (declaration, names) in declarations.iter_mut().zip(names) {
        let names = &mut names.names;
        let mut function = Function { names, taken, always: false, pending: vec![] };
        go_traversal::declaration(&mut function, declaration);
    }
}

struct Function<'a> {
    /// Every name the declaration uses, so that a block shadows none of them.
    names: &'a mut FxHashSet<String>,
    taken: &'a dyn Fn(&str) -> bool,
    /// Whether the statement always evaluates the expression visited, so that
    /// the blocks its cells need may go before the statement.
    always: bool,
    /// The blocks the statement visited needs, to go before it.
    pending: Vec<GoStatement>,
}

impl Walk for Function<'_> {
    /// A list of statements, each preceded by the blocks its expressions need.
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        let always = self.always;
        let outer = std::mem::take(&mut self.pending);
        let mut rewritten = Vec::with_capacity(body.len());
        for mut statement in std::mem::take(body) {
            self.statement(&mut statement);
            rewritten.append(&mut self.pending);
            rewritten.push(statement);
        }
        *body = rewritten;
        self.always = always;
        self.pending = outer;
    }

    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Assign { targets, values } = statement {
            self.always = false;
            targets.iter_mut().for_each(|target| self.expression(target));
            self.always = true;
            return values.iter_mut().for_each(|value| self.expression(value));
        }
        self.always = matches!(
            statement,
            GoStatement::Define { .. }
                | GoStatement::Variable { .. }
                | GoStatement::Expression(_)
                | GoStatement::Return(_)
        );
        go_traversal::statement(self, statement);
    }

    /// An expression. When its statement always evaluates it, the blocks its
    /// cells need go before that statement; otherwise only the function
    /// literals inside it are rewritten.
    fn expression(&mut self, value: &mut GoExpression) {
        if self.always
            && let Some(type_) = cell_type(value)
            && nested_cells(value, &type_) >= MINIMUM_CELLS
        {
            return self.allocate_together(value, type_);
        }
        match value {
            GoExpression::Binary {
                operator: GoBinaryOperator::LogicalAnd | GoBinaryOperator::LogicalOr,
                left,
                right,
            } => {
                self.expression(left);
                let always = std::mem::replace(&mut self.always, false);
                self.expression(right);
                self.always = always;
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

impl Function<'_> {
    /// Replaces the cell `value` and the cells of `type_` nested in it with
    /// cells of one slice, built in `pending`.
    fn allocate_together(&mut self, value: &mut GoExpression, type_: GoType) {
        let slice = self.fresh_name(&type_);
        let mut cells = vec![];
        let root = std::mem::replace(value, GoExpression::Integer(0));
        let GoExpression::Address(root) = root else {
            unreachable!("invariant violated: a cell is the address of a composite")
        };
        self.number(*root, &type_, &slice, &mut cells);
        let allocation = GoExpression::Call {
            function: Box::new(GoExpression::builtin(GoBuiltin::Make)),
            arguments: vec![
                GoExpression::Type(GoType::Slice(Box::new(type_))),
                GoExpression::Integer(cells.len() as i64),
            ],
        };
        self.pending
            .push(GoStatement::Define { names: vec![slice.clone()], values: vec![allocation] });
        for (index, cell) in cells.into_iter().enumerate() {
            self.pending.push(GoStatement::Assign {
                targets: vec![element(&slice, index)],
                values: vec![cell],
            });
        }
        *value = GoExpression::Address(Box::new(element(&slice, 0)));
    }

    /// Gives `composite` the next index of the slice, in pre-order, and its
    /// nested cells the indices after it. Fields that are no such cell may
    /// hold expressions that need blocks of their own.
    fn number(
        &mut self,
        mut composite: GoExpression,
        type_: &GoType,
        slice: &str,
        cells: &mut Vec<GoExpression>,
    ) {
        let index = cells.len();
        cells.push(GoExpression::Integer(0));
        self.number_fields(&mut composite, type_, slice, cells);
        cells[index] = composite;
    }

    fn number_fields(
        &mut self,
        composite: &mut GoExpression,
        type_: &GoType,
        slice: &str,
        cells: &mut Vec<GoExpression>,
    ) {
        let GoExpression::Composite { fields, .. } = composite else {
            unreachable!("invariant violated: only composites are numbered")
        };
        for (_, field) in fields {
            if cell_type(field).as_ref() == Some(type_) {
                let cell = std::mem::replace(field, GoExpression::Integer(0));
                let GoExpression::Address(nested) = cell else {
                    unreachable!("invariant violated: a cell is the address of a composite")
                };
                *field = GoExpression::Address(Box::new(element(slice, cells.len())));
                self.number(*nested, type_, slice, cells);
            } else if let GoExpression::Composite { .. } = field {
                self.number_fields(field, type_, slice, cells);
            } else {
                self.expression(field);
            }
        }
    }

    /// `exprs` for a slice of `Expr`, unless the declaration uses that name.
    fn fresh_name(&mut self, type_: &GoType) -> String {
        let type_name = match type_ {
            GoType::Named(name) | GoType::Generic { name, .. } => name,
            _ => unreachable!("invariant violated: only named types are cells"),
        };
        let unqualified = type_name.rsplit('.').next().unwrap_or(type_name);
        let mut base = lower_first(unqualified);
        base.push_str(if base.ends_with('s') { "Cells" } else { "s" });
        let name = numbered(&base, |name| self.names.contains(name) || (self.taken)(name));
        self.names.insert(name.clone());
        name
    }
}

/// The type of a cell: the address of a composite of a named type.
fn cell_type(value: &GoExpression) -> Option<GoType> {
    let GoExpression::Address(composite) = value else { return None };
    let GoExpression::Composite { type_, .. } = composite.as_ref() else { return None };
    matches!(type_, GoType::Named(_) | GoType::Generic { .. }).then(|| type_.clone())
}

/// The cells of `type_` in `value`, counting it, that are reached through
/// fields alone.
fn nested_cells(value: &GoExpression, type_: &GoType) -> usize {
    let fields = match value {
        GoExpression::Address(composite) => match composite.as_ref() {
            GoExpression::Composite { fields, .. } => fields,
            _ => return 0,
        },
        GoExpression::Composite { fields, .. } => fields,
        _ => return 0,
    };
    let own = usize::from(matches!(value, GoExpression::Address(_)));
    let nested: usize = fields
        .iter()
        .map(|(_, field)| match field {
            GoExpression::Address(_) if cell_type(field).as_ref() == Some(type_) => {
                nested_cells(field, type_)
            }
            GoExpression::Composite { .. } => nested_cells(field, type_),
            _ => 0,
        })
        .sum();
    own + nested
}

/// `slice[index]`.
fn element(slice: &str, index: usize) -> GoExpression {
    GoExpression::Index {
        value: Box::new(GoExpression::Identifier(slice.into())),
        index: Box::new(GoExpression::Integer(index as i64)),
    }
}
