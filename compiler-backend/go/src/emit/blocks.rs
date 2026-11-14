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

use super::chunks::lower_first;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

/// The fewest cells of one type in one expression that are allocated together.
const MINIMUM_CELLS: usize = 3;

/// Rewrites every expression that nests enough cells of one type. `taken`
/// tells which names a new local must not shadow.
pub fn allocate_nested_cells_together(
    declarations: &mut [GoDeclaration],
    taken: &dyn Fn(&str) -> bool,
) {
    for declaration in declarations {
        let mut names = FxHashSet::default();
        declaration.for_each_name_mut(&mut |name| {
            let (crate::syntax::Name::Reference(name) | crate::syntax::Name::Binder(name)) = name;
            names.insert(name.clone());
        });
        let mut function = Function { names, taken };
        match declaration {
            GoDeclaration::Function { body, .. } => function.block(body),
            GoDeclaration::Variable { value, .. } => function.expression(value, None),
            _ => {}
        }
    }
}

struct Function<'a> {
    /// Every name the declaration uses, so that a block shadows none of them.
    names: FxHashSet<String>,
    taken: &'a dyn Fn(&str) -> bool,
}

impl Function<'_> {
    /// A list of statements, each preceded by the blocks its expressions need.
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        let mut rewritten = Vec::with_capacity(body.len());
        for mut statement in std::mem::take(body) {
            let mut blocks = vec![];
            self.statement(&mut statement, &mut blocks);
            rewritten.extend(blocks);
            rewritten.push(statement);
        }
        *body = rewritten;
    }

    fn statement(&mut self, statement: &mut GoStatement, blocks: &mut Vec<GoStatement>) {
        match statement {
            GoStatement::Define { values, .. } => {
                values.iter_mut().for_each(|value| self.expression(value, Some(blocks)))
            }
            GoStatement::Variable { value, .. } => {
                if let Some(value) = value {
                    self.expression(value, Some(blocks));
                }
            }
            GoStatement::Assign { targets, values } => {
                targets.iter_mut().for_each(|target| self.expression(target, None));
                values.iter_mut().for_each(|value| self.expression(value, Some(blocks)));
            }
            GoStatement::Expression(value) | GoStatement::Return(Some(value)) => {
                self.expression(value, Some(blocks))
            }
            GoStatement::Defer(value) => self.expression(value, None),
            GoStatement::If { condition, then, otherwise } => {
                self.expression(condition, None);
                self.block(then);
                self.block(otherwise);
            }
            GoStatement::Switch { value, cases, default } => {
                if let Some(value) = value {
                    self.expression(value, None);
                }
                for case in cases {
                    case.values.iter_mut().for_each(|value| self.expression(value, None));
                    self.block(&mut case.body);
                }
                if let Some(default) = default {
                    self.block(&mut default.body);
                }
            }
            GoStatement::IfAssert { value, then, .. } => {
                self.expression(value, None);
                self.block(then);
            }
            GoStatement::Range { iterable, body, .. } => {
                self.expression(iterable, None);
                self.block(body);
            }
            GoStatement::Counting { start, end, body, .. } => {
                self.expression(start, None);
                self.expression(end, None);
                self.block(body);
            }
            GoStatement::CountingDown { start, body, .. } => {
                self.expression(start, None);
                self.block(body);
            }
            GoStatement::Loop(body)
            | GoStatement::LabeledLoop { body, .. }
            | GoStatement::Block(body) => self.block(body),
            GoStatement::Return(None)
            | GoStatement::Continue
            | GoStatement::Break
            | GoStatement::BreakTo(_) => {}
        }
    }

    /// An expression. With `blocks`, its statement always evaluates it, and
    /// the blocks its cells need go there; without, only the function
    /// literals inside it are rewritten.
    fn expression(&mut self, value: &mut GoExpression, mut blocks: Option<&mut Vec<GoStatement>>) {
        if let Some(blocks) = blocks.as_deref_mut()
            && let Some(type_) = cell_type(value)
            && nested_cells(value, &type_) >= MINIMUM_CELLS
        {
            return self.allocate_together(value, type_, blocks);
        }
        match value {
            GoExpression::Function { body, .. } => self.block(body),
            GoExpression::Binary { operator: "&&" | "||", left, right } => {
                self.expression(left, blocks);
                self.expression(right, None);
            }
            GoExpression::Binary { left, right, .. } => {
                self.expression(left, blocks.as_deref_mut());
                self.expression(right, blocks);
            }
            GoExpression::Call { function, arguments } => {
                self.expression(function, blocks.as_deref_mut());
                for argument in arguments {
                    self.expression(argument, blocks.as_deref_mut());
                }
            }
            GoExpression::Index { value, index } => {
                self.expression(value, blocks.as_deref_mut());
                self.expression(index, blocks);
            }
            GoExpression::Composite { fields, .. } => {
                for (_, field) in fields {
                    self.expression(field, blocks.as_deref_mut());
                }
            }
            GoExpression::Unary { operand: value, .. }
            | GoExpression::Field { value, .. }
            | GoExpression::Address(value)
            | GoExpression::Conversion { value, .. }
            | GoExpression::TypeAssertion { value, .. }
            | GoExpression::Spread(value)
            | GoExpression::Instantiation { function: value, .. } => self.expression(value, blocks),
            GoExpression::Identifier(_)
            | GoExpression::Qualified { .. }
            | GoExpression::Integer(_)
            | GoExpression::Float(_)
            | GoExpression::String(_)
            | GoExpression::Rune(_)
            | GoExpression::Boolean(_)
            | GoExpression::Type(_) => {}
        }
    }

    /// Replaces the cell `value` and the cells of `type_` nested in it with
    /// cells of one slice, built in `blocks`.
    fn allocate_together(
        &mut self,
        value: &mut GoExpression,
        type_: GoType,
        blocks: &mut Vec<GoStatement>,
    ) {
        let slice = self.fresh_name(&type_);
        let mut cells = vec![];
        let root = std::mem::replace(value, GoExpression::Integer(0));
        let GoExpression::Address(root) = root else {
            unreachable!("invariant violated: a cell is the address of a composite")
        };
        self.number(*root, &type_, &slice, &mut cells, blocks);
        let allocation = GoExpression::Call {
            function: Box::new(GoExpression::Identifier("make".into())),
            arguments: vec![
                GoExpression::Type(GoType::Slice(Box::new(type_))),
                GoExpression::Integer(cells.len() as i64),
            ],
        };
        blocks.push(GoStatement::Define { names: vec![slice.clone()], values: vec![allocation] });
        for (index, cell) in cells.into_iter().enumerate() {
            blocks.push(GoStatement::Assign {
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
        blocks: &mut Vec<GoStatement>,
    ) {
        let index = cells.len();
        cells.push(GoExpression::Integer(0));
        self.number_fields(&mut composite, type_, slice, cells, blocks);
        cells[index] = composite;
    }

    fn number_fields(
        &mut self,
        composite: &mut GoExpression,
        type_: &GoType,
        slice: &str,
        cells: &mut Vec<GoExpression>,
        blocks: &mut Vec<GoStatement>,
    ) {
        let GoExpression::Composite { fields, .. } = composite else {
            unreachable!("invariant violated: only composites are numbered")
        };
        for (_, field) in fields {
            if cell_type(field).as_ref() == Some(type_) {
                let GoExpression::Address(nested) =
                    std::mem::replace(field, GoExpression::Integer(0))
                else {
                    unreachable!("invariant violated: a cell is the address of a composite")
                };
                *field = GoExpression::Address(Box::new(element(slice, cells.len())));
                self.number(*nested, type_, slice, cells, blocks);
            } else if let GoExpression::Composite { .. } = field {
                self.number_fields(field, type_, slice, cells, blocks);
            } else {
                self.expression(field, Some(blocks));
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
        let mut name = base.clone();
        let mut counter = 2;
        while self.names.contains(&name) || (self.taken)(&name) {
            name = format!("{base}{counter}");
            counter += 1;
        }
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
