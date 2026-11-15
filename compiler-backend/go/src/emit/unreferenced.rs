//! Drops the definitions that emission left without a reference.
//!
//! A local is defined when the program reads it, but a read whose result is Unit emits as
//! `struct{}{}` without the value it was read from, and the code after a diverging statement is
//! cut. A record or loop element whose every read was such a field, or a local read only after a
//! `panic`, is then defined and never used, which Go rejects. A definition whose value has no
//! effect and cannot fail is dropped; one whose value is a call keeps the call.

use rustc_hash::FxHashSet;

use super::{discarded, is_effectful_call};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, Name};
use crate::walk::each_block_in_declaration;

pub(super) fn drop_unreferenced_definitions(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        // Dropping a definition can leave the definitions its value read without a reference.
        while drop_unreferenced(declaration) {}
    }
}

fn drop_unreferenced(declaration: &mut GoDeclaration) -> bool {
    let referenced = referenced_names(declaration);
    let mut dropped = false;
    each_block_in_declaration(declaration, |block| {
        block.retain(|statement| {
            let unreferenced = match statement {
                GoStatement::Define { names, values } => {
                    matches!(names.as_slice(), [name] if !referenced.contains(name))
                        && matches!(values.as_slice(), [value] if is_inert(value))
                }
                GoStatement::Variable { name, value, .. } => {
                    !referenced.contains(name) && value.as_ref().is_none_or(is_inert)
                }
                _ => false,
            };
            dropped |= unreferenced;
            !unreferenced
        });
        for statement in block.iter_mut() {
            match statement {
                GoStatement::Define { names, values }
                    if matches!(names.as_slice(), [name] if !referenced.contains(name))
                        && matches!(values.as_slice(), [value] if is_effectful_call(value)) =>
                {
                    let value = values.pop().expect("a definition with one name has one value");
                    *statement = discarded(value);
                    dropped = true;
                }
                GoStatement::Range { element, .. }
                    if element != "_" && !referenced.contains(element) =>
                {
                    *element = "_".into();
                    dropped = true;
                }
                _ => {}
            }
        }
    });
    dropped
}

/// Every name the statements read or write; a write counts, since Go accepts a local that is
/// only written through a field or an index.
fn referenced_names(declaration: &mut GoDeclaration) -> FxHashSet<String> {
    let mut referenced = FxHashSet::default();
    declaration.for_each_name_mut(&mut |name| {
        if let Name::Reference(name) | Name::Written(name) = name {
            referenced.insert(name.clone());
        }
    });
    referenced
}

/// Whether evaluating the value has no effect and cannot panic.
fn is_inert(value: &GoExpression) -> bool {
    match value {
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Utf16(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_)
        | GoExpression::Function { .. } => true,
        GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. } => is_inert(value),
        GoExpression::Composite { fields, .. } => fields.iter().all(|(_, value)| is_inert(value)),
        // Integer division by zero panics, and so does dereferencing nil.
        GoExpression::Binary { operator, left, right } => {
            !matches!(*operator, "/" | "%") && is_inert(left) && is_inert(right)
        }
        GoExpression::Unary { operator, operand } => *operator != "*" && is_inert(operand),
        GoExpression::Call { .. }
        | GoExpression::Index { .. }
        | GoExpression::TypeAssertion { .. }
        | GoExpression::Type(_)
        | GoExpression::Spread(_)
        | GoExpression::Instantiation { .. } => false,
    }
}
