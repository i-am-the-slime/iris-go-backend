//! A reused cell, overwritten field by field.
//!
//! `*cell = T{Tag: TNode, Node0: h, Node1: s, Node2: k, Node3: v, Node4: l, Node5: r}` makes Go
//! build the whole struct in a temporary on the stack and copy it into the cell, through
//! `runtime.wbMove` while the collector runs. A balanced tree's insert overwrites one cell per
//! level, so the copy is most of its cost. Storing each field directly,
//!
//! ```go
//! cell.Node0 = h
//! cell.Node1 = s
//! ...
//! ```
//!
//! writes the same values in place. The stores happen one after another, so a value that could read
//! the cell, or that calls anything, is computed into a local first, as the struct literal would
//! have computed it before the copy.
//!
//! The tag is stored only when another constructor has fields: a reused cell held a constructor
//! with fields, so when there is one such constructor the tag is already right. A slot this
//! constructor leaves empty but another one uses keeps the value the struct literal would have
//! cleared, so such constructors, and layouts with an `Origin` field, keep the literal. A field of
//! type `struct{}` holds nothing and is not stored.

use rustc_hash::FxHashSet;

use super::{DataKind, DataLayout, Emitter, call, identifier_expression};
use crate::error::GoResult;
use crate::go_traversal::{self, Walk};
use crate::monomorphic::{Edge, Expression, ExpressionKind, Kept, Literal};
use crate::monotype::DataType;
use crate::syntax::{GoExpression, GoStatement, GoType};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn reused(
        &mut self,
        reuse: &ExpressionKind,
        edges: &[(usize, Expression)],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let ExpressionKind::Reuse { cell, data, constructor, arguments, kept } = reuse else {
            unreachable!("invariant violated: a reused cell is emitted from a reuse")
        };
        let constructor = *constructor;
        let values = self.values(arguments, out)?;
        let cell = self.value(cell, out)?;
        let layout = self.data_layout(data)?;
        let cell_name = match &cell {
            GoExpression::Identifier(name) => Some(name.as_str()),
            _ => None,
        };
        let mask = self.unique_mask(data, constructor, edges, cell_name, out)?;
        if let Some(name) = cell_name
            && let Some(stores) = self.reuse_stores(
                &layout,
                constructor,
                name,
                Stored { values: values.clone(), kept: *kept },
                mask.clone(),
                out,
            )
        {
            out.extend(stores);
            return Ok(cell);
        }
        let composite = self.composite(&layout, constructor, values);
        let composite = with_unique_mask(composite, mask);
        let target = GoExpression::Unary { operator: "*", operand: Box::new(cell.clone()) };
        out.push(GoStatement::Assign { targets: vec![target], values: vec![composite] });
        Ok(cell)
    }

    pub(super) fn unique_edge(
        &mut self,
        owned: &Expression,
        cell: &Expression,
        edge: &Edge,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let layout = self.data_layout(&edge.data)?;
        let bits = layout.edges.as_ref();
        let Some(bit) = bits.and_then(|bits| bits.bit(edge.constructor, edge.field)) else {
            unreachable!("invariant violated: an edge is read from a cell that does not track it")
        };
        let cell = self.value(cell, out)?;
        let unique = GoExpression::Field { value: Box::new(cell), name: "Unique".into() };
        let set = GoExpression::Binary {
            operator: "&",
            left: Box::new(unique),
            right: Box::new(GoExpression::Integer(i64::from(bit))),
        };
        let edge = GoExpression::Binary {
            operator: "!=",
            left: Box::new(set),
            right: Box::new(GoExpression::Integer(0)),
        };
        if is_true(owned) {
            return Ok(edge);
        }
        let owned = self.value(owned, out)?;
        Ok(GoExpression::Binary { operator: "&&", left: Box::new(owned), right: Box::new(edge) })
    }

    pub(super) fn unique_mask(
        &mut self,
        data: &DataType,
        constructor: usize,
        edges: &[(usize, Expression)],
        cell: Option<&str>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Option<GoExpression>> {
        let Some(bits) = self.data_layout(data)?.edges else { return Ok(None) };
        let mut constant = 0;
        let mut terms = vec![];
        for (field, owned) in edges {
            let Some(bit) = bits.bit(constructor, *field) else { continue };
            match &owned.kind {
                ExpressionKind::Literal(Literal::Boolean(true)) => constant |= bit,
                ExpressionKind::Literal(Literal::Boolean(false)) => {}
                _ => {
                    let mut owned = self.value(owned, out)?;
                    if let Some(cell) = cell
                        && !independent_of(&mut owned, cell)
                    {
                        owned = self.shared(owned, "owned", out);
                    }
                    let unique_bit = self.support_function("uniqueBit", UNIQUE_BIT_SOURCE);
                    let bit = GoExpression::Integer(i64::from(bit));
                    terms.push(call(identifier_expression(&unique_bit), vec![owned, bit]));
                }
            }
        }
        let constant =
            (constant != 0 || terms.is_empty()).then(|| GoExpression::Integer(i64::from(constant)));
        let mask = constant.into_iter().chain(terms).reduce(|left, right| GoExpression::Binary {
            operator: "|",
            left: Box::new(left),
            right: Box::new(right),
        });
        Ok(mask)
    }

    pub(super) fn reuse_stores(
        &mut self,
        layout: &DataLayout,
        constructor: usize,
        cell: &str,
        stored: Stored,
        mask: Option<GoExpression>,
        out: &mut Vec<GoStatement>,
    ) -> Option<Vec<GoStatement>> {
        let Stored { values, kept } = stored;
        if !layout.boxed || layout.erases_arguments || layout.maybe.is_some() {
            return None;
        }
        if layout.kind == DataKind::Enumeration {
            return None;
        }
        let constructor_layout = &layout.constructors[constructor];
        let slots: FxHashSet<&str> =
            constructor_layout.fields.iter().map(|(name, _)| name.as_str()).collect();
        let others_with_fields = layout
            .constructors
            .iter()
            .enumerate()
            .filter(|(index, other)| *index != constructor && !other.fields.is_empty())
            .map(|(_, other)| other)
            .collect::<Vec<_>>();
        let covered = others_with_fields
            .iter()
            .all(|other| other.fields.iter().all(|(name, _)| slots.contains(name.as_str())));
        // A cell that holds this constructor already holds nothing in the other slots.
        if !covered && !kept.constructor {
            return None;
        }
        let field = |name: &str| GoExpression::Field {
            value: Box::new(identifier_expression(cell)),
            name: name.to_string(),
        };
        let mut stores = vec![];
        if layout.kind == DataKind::Tagged && !others_with_fields.is_empty() && !kept.constructor {
            stores.push(GoStatement::Assign {
                targets: vec![field("Tag")],
                values: vec![identifier_expression(&constructor_layout.tag)],
            });
        }
        for (position, ((name, _), mut value)) in
            constructor_layout.fields.iter().zip(values).enumerate()
        {
            if matches!(&value, GoExpression::Composite { type_: GoType::EmptyStruct, .. })
                || holds_field(out, cell, name, &value)
            {
                continue;
            }
            if kept.field(position) {
                continue;
            }
            if !independent_of(&mut value, cell) {
                let local = self.temporary("field");
                out.push(GoStatement::Define { names: vec![local.clone()], values: vec![value] });
                value = identifier_expression(&local);
            }
            stores.push(GoStatement::Assign { targets: vec![field(name)], values: vec![value] });
        }
        if let Some(mask) = mask {
            stores.push(GoStatement::Assign { targets: vec![field("Unique")], values: vec![mask] });
        }
        Some(stores)
    }
}

/// The values a reuse stores in its cell's fields, and which of them the fields already hold.
pub(super) struct Stored {
    pub values: Vec<GoExpression>,
    pub kept: Kept,
}

pub(super) fn with_unique_mask(
    constructed: GoExpression,
    mask: Option<GoExpression>,
) -> GoExpression {
    let Some(mask) = mask.filter(|mask| !matches!(mask, GoExpression::Integer(0))) else {
        return constructed;
    };
    match constructed {
        GoExpression::Address(composite) => {
            GoExpression::Address(Box::new(with_unique_mask(*composite, Some(mask))))
        }
        GoExpression::Composite { type_, mut fields } => {
            fields.push((Some("Unique".into()), mask));
            GoExpression::Composite { type_, fields }
        }
        constructed => constructed,
    }
}

fn is_true(expression: &Expression) -> bool {
    matches!(expression.kind, ExpressionKind::Literal(Literal::Boolean(true)))
}

const UNIQUE_BIT_SOURCE: &str = "func {name}(owned bool, bit uint8) uint8 {
\tif owned {
\t\treturn bit
\t}
\treturn 0
}
";

/// Whether the value is a local that the statements before the store define as the cell's own
/// field, `x := cell.Name`, with only definitions that call nothing in between: storing it back
/// would change nothing.
fn holds_field(before: &[GoStatement], cell: &str, name: &str, value: &GoExpression) -> bool {
    let GoExpression::Identifier(local) = value else { return false };
    for statement in before.iter().rev() {
        match statement {
            GoStatement::Line(_) => {}
            GoStatement::Define { names, values } if names.len() == values.len() => {
                let mut values = values.clone();
                if let Some(position) = names.iter().position(|defined| defined == local) {
                    return matches!(&values[position], GoExpression::Field { value, name: read }
                        if read == name
                            && matches!(value.as_ref(), GoExpression::Identifier(read_cell) if read_cell == cell));
                }
                if !values.iter_mut().all(calls_nothing) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    false
}

fn calls_nothing(value: &mut GoExpression) -> bool {
    struct Search {
        calls: bool,
    }
    impl Walk for Search {
        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Call { .. } | GoExpression::Function { .. } => self.calls = true,
                _ => go_traversal::expression(self, value),
            }
        }
    }
    let mut search = Search { calls: false };
    search.expression(value);
    !search.calls
}

/// Whether storing into the cell's fields before computing the value leaves the value unchanged:
/// it neither names the cell nor calls anything that might reach it.
fn independent_of(value: &mut GoExpression, cell: &str) -> bool {
    struct Search<'a> {
        cell: &'a str,
        independent: bool,
    }
    impl Walk for Search<'_> {
        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Identifier(name) if name == self.cell => self.independent = false,
                GoExpression::Call { .. } | GoExpression::Function { .. } => {
                    self.independent = false
                }
                _ => go_traversal::expression(self, value),
            }
        }
    }
    let mut search = Search { cell, independent: true };
    search.expression(value);
    search.independent
}
