//! A field read again where an earlier read of it is still in scope reuses that read.
//!
//! Each use of a record's field reads it afresh, `stArray := items.Second … stArray2 :=
//! items.Second`. A field changes only when the function stores into it: a callee that could
//! change it in place owns the record, and the caller does not read it again. So while neither
//! the record's variable nor the earlier read's variable is assigned anywhere in the function,
//! and no field of that name is stored, the later read is a copy of the earlier one, which
//! `substitute_aliases` then replaces.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::go_traversal::{self, Walk};
use crate::syntax::{
    GoDeclaration, GoExpression, GoStatement, GoType, GoUnaryOperator, Name, statements_names,
};

pub(super) fn reuse_field_reads(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let GoDeclaration::Function { parameters, body, .. } = declaration else { continue };
        let Some(unchanging) = Unchanging::of(parameters, body) else { continue };
        let mut copies = FxHashMap::default();
        reuse_in_block(body, &FxHashMap::default(), &unchanging, &mut copies);
        if copies.is_empty() {
            continue;
        }
        go_traversal::each_block(body, |block| {
            block.retain(|statement| !is_copy(statement, &copies));
        });
        statements_names(body, &mut |name| {
            if let Name::Reference(name) | Name::Written(name) = name
                && let Some(earlier) = copies.get(name.as_str())
            {
                *name = earlier.clone();
            }
        });
    }
}

/// Whether the statement is the definition of a copy of an earlier read.
fn is_copy(statement: &GoStatement, copies: &FxHashMap<String, String>) -> bool {
    matches!(statement, GoStatement::Define { names, values }
        if matches!((names.as_slice(), values.as_slice()),
            ([name], [GoExpression::Identifier(earlier)]) if copies.get(name) == Some(earlier)))
}

/// The reads in scope: the variable holding each record's field.
type Reads = FxHashMap<(String, String), String>;

struct Unchanging {
    assigned: FxHashSet<String>,
    stored_fields: FxHashSet<String>,
}

impl Unchanging {
    /// `None` when the function overwrites a whole struct through a pointer, which stores
    /// every field.
    fn of(parameters: &[(String, GoType)], body: &mut [GoStatement]) -> Option<Unchanging> {
        let mut assigned = FxHashSet::default();
        let mut bound: FxHashSet<String> =
            parameters.iter().map(|(name, _)| name.clone()).collect();
        statements_names(body, &mut |name| match name {
            Name::Written(name) => {
                assigned.insert(name.clone());
            }
            // A name bound twice may mean another variable where it is read.
            Name::Binder(name) => {
                if !bound.insert(name.clone()) {
                    assigned.insert(name.clone());
                }
            }
            Name::Reference(_) => {}
        });
        let mut stores = Stores { fields: FxHashSet::default(), whole: false };
        body.iter_mut().for_each(|statement| stores.statement(statement));
        (!stores.whole).then_some(Unchanging { assigned, stored_fields: stores.fields })
    }

    /// The record and field a definition reads, when neither can change.
    fn read<'s>(&self, statement: &'s GoStatement) -> Option<(&'s str, (String, String))> {
        let GoStatement::Define { names, values } = statement else { return None };
        let ([name], [GoExpression::Field { value, name: field }]) =
            (names.as_slice(), values.as_slice())
        else {
            return None;
        };
        let GoExpression::Identifier(record) = value.as_ref() else { return None };
        let fixed = !self.assigned.contains(record)
            && !self.assigned.contains(name)
            && !self.stored_fields.contains(field);
        fixed.then(|| (name.as_str(), (record.clone(), field.clone())))
    }
}

fn reuse_in_block(
    block: &mut [GoStatement],
    outer: &Reads,
    unchanging: &Unchanging,
    copies: &mut FxHashMap<String, String>,
) {
    let mut reads = outer.clone();
    for statement in block.iter_mut() {
        if let Some((name, key)) = unchanging.read(statement) {
            let name = name.to_string();
            match reads.get(&key) {
                Some(earlier) => {
                    let value = GoExpression::Identifier(earlier.clone());
                    copies.insert(name.clone(), earlier.clone());
                    *statement = GoStatement::Define { names: vec![name], values: vec![value] };
                }
                None => {
                    reads.insert(key, name);
                }
            }
            continue;
        }
        let mut nested = Nested { reads: &reads, unchanging, copies };
        go_traversal::statement(&mut nested, statement);
    }
}

struct Nested<'r> {
    reads: &'r Reads,
    unchanging: &'r Unchanging,
    copies: &'r mut FxHashMap<String, String>,
}

impl Walk for Nested<'_> {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        reuse_in_block(body, self.reads, self.unchanging, self.copies);
    }
}

/// The names of the fields the code stores into, and whether it stores a whole struct through a
/// pointer.
struct Stores {
    fields: FxHashSet<String>,
    whole: bool,
}

impl Walk for Stores {
    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Assign { targets, .. } = statement {
            for target in targets {
                match target {
                    GoExpression::Field { name, .. } => {
                        self.fields.insert(name.clone());
                    }
                    GoExpression::Unary { operator: GoUnaryOperator::Dereference, .. } => {
                        self.whole = true
                    }
                    _ => {}
                }
            }
        }
        go_traversal::statement(self, statement);
    }
}
