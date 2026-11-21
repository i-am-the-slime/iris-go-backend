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

use super::{DataKind, DataLayout, Emitter, identifier_expression};
use crate::syntax::{GoExpression, GoStatement, GoType};
use crate::walk::{self, Walk};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn reuse_stores(
        &mut self,
        layout: &DataLayout,
        constructor: usize,
        cell: &str,
        values: Vec<GoExpression>,
        out: &mut Vec<GoStatement>,
    ) -> Option<Vec<GoStatement>> {
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
        if !covered {
            return None;
        }
        let field = |name: &str| GoExpression::Field {
            value: Box::new(identifier_expression(cell)),
            name: name.to_string(),
        };
        let mut stores = vec![];
        if layout.kind == DataKind::Tagged && !others_with_fields.is_empty() {
            stores.push(GoStatement::Assign {
                targets: vec![field("Tag")],
                values: vec![identifier_expression(&constructor_layout.tag)],
            });
        }
        for ((name, _), mut value) in constructor_layout.fields.iter().zip(values) {
            if matches!(&value, GoExpression::Composite { type_: GoType::EmptyStruct, .. }) {
                continue;
            }
            if !independent_of(&mut value, cell) {
                let local = self.temporary("field");
                out.push(GoStatement::Define { names: vec![local.clone()], values: vec![value] });
                value = identifier_expression(&local);
            }
            stores.push(GoStatement::Assign { targets: vec![field(name)], values: vec![value] });
        }
        Some(stores)
    }
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
                _ => walk::expression(self, value),
            }
        }
    }
    let mut search = Search { cell, independent: true };
    search.expression(value);
    search.independent
}
