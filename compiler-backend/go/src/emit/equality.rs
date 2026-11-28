//! Two structs compared field by field, as a record's `Eq` instance does once its getters are
//! inlined, `ra.Rank == rb.Rank && ra.Suit == rb.Suit`, are Go's struct equality, `ra == rb`,
//! when the comparisons cover every field of the struct type both parameters have: Go compares
//! structs field by field with each field's `==`, which the comparisons already use.

use rustc_hash::FxHashMap;

use super::scalars::Structs;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoBinaryOperator, GoDeclaration, GoExpression, GoType};

pub(super) fn compare_structs_whole(declarations: &mut [GoDeclaration], structs: &Structs) {
    for declaration in declarations {
        let GoDeclaration::Function { parameters, .. } = declaration else { continue };
        let types = parameters.iter().filter_map(|(name, type_)| match type_ {
            GoType::Named(type_name) if structs.contains_key(type_name) => {
                Some((name.clone(), type_name.clone()))
            }
            _ => None,
        });
        let types: FxHashMap<String, String> = types.collect();
        if types.len() < 2 {
            continue;
        }
        go_traversal::declaration(&mut Whole { structs, types: &types }, declaration);
    }
}

struct Whole<'s> {
    structs: &'s Structs,
    /// The struct type of each parameter of one.
    types: &'s FxHashMap<String, String>,
}

impl Walk for Whole<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        if let Some(whole) = self.whole_comparison(value) {
            *value = whole;
        }
    }
}

impl Whole<'_> {
    fn whole_comparison(&self, value: &GoExpression) -> Option<GoExpression> {
        let GoExpression::Binary { operator: GoBinaryOperator::LogicalAnd, .. } = value else {
            return None;
        };
        let mut conjuncts = vec![];
        conjunction(value, &mut conjuncts);
        let mut compared: Option<(&str, &str)> = None;
        let mut fields = vec![];
        for conjunct in conjuncts {
            let (left, right, field) = field_equality(conjunct)?;
            if *compared.get_or_insert((left, right)) != (left, right) {
                return None;
            }
            fields.push(field);
        }
        let (left, right) = compared?;
        let type_name = self.types.get(left)?;
        if self.types.get(right) != Some(type_name) {
            return None;
        }
        let declared = &self.structs[type_name];
        let covered = fields.len() == declared.len()
            && declared.iter().all(|(name, _)| fields.contains(&name.as_str()));
        covered.then(|| GoExpression::Binary {
            operator: GoBinaryOperator::Equal,
            left: Box::new(GoExpression::Identifier(left.to_string())),
            right: Box::new(GoExpression::Identifier(right.to_string())),
        })
    }
}

fn conjunction<'e>(value: &'e GoExpression, conjuncts: &mut Vec<&'e GoExpression>) {
    match value {
        GoExpression::Binary { operator: GoBinaryOperator::LogicalAnd, left, right } => {
            conjunction(left, conjuncts);
            conjunction(right, conjuncts);
        }
        value => conjuncts.push(value),
    }
}

/// `a.F == b.F`, as the names of `a` and `b` and the field.
fn field_equality(value: &GoExpression) -> Option<(&str, &str, &str)> {
    let GoExpression::Binary { operator: GoBinaryOperator::Equal, left, right } = value else {
        return None;
    };
    let (
        GoExpression::Field { value: left, name: left_field },
        GoExpression::Field { value: right, name: right_field },
    ) = (&**left, &**right)
    else {
        return None;
    };
    let (GoExpression::Identifier(left), GoExpression::Identifier(right)) = (&**left, &**right)
    else {
        return None;
    };
    (left_field == right_field && left != right).then_some((
        left.as_str(),
        right.as_str(),
        left_field.as_str(),
    ))
}
