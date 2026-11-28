use rustc_hash::FxHashMap;

use super::nil;
use crate::emit::{call, identifier_expression};
use crate::syntax::{GoDeclaration, GoExpression, GoType, GoUnaryOperator};

/// The zero values of Go types, for the value a function returns beside a failure.
pub(super) struct Zeros {
    declared: FxHashMap<String, GoType>,
}

impl Zeros {
    pub(super) fn new(type_declarations: &[GoDeclaration]) -> Zeros {
        let declared = type_declarations
            .iter()
            .filter_map(|declaration| match declaration {
                GoDeclaration::Type { name, type_, .. }
                | GoDeclaration::Alias { name, type_, .. } => Some((name.clone(), type_.clone())),
                _ => None,
            })
            .collect();
        Zeros { declared }
    }

    pub(super) fn zero(&self, type_: &GoType) -> GoExpression {
        self.literal(type_, type_, 0).unwrap_or_else(|| GoExpression::Unary {
            operator: GoUnaryOperator::Dereference,
            operand: Box::new(call(
                identifier_expression("new"),
                vec![GoExpression::Type(type_.clone())],
            )),
        })
    }

    fn literal(&self, spelled: &GoType, type_: &GoType, depth: usize) -> Option<GoExpression> {
        Some(match type_ {
            GoType::Int | GoType::Float64 | GoType::Rune => GoExpression::Integer(0),
            GoType::Bool => GoExpression::Boolean(false),
            GoType::String => GoExpression::String(String::new()),
            GoType::Pointer(_)
            | GoType::Slice(_)
            | GoType::Function { .. }
            | GoType::Any
            | GoType::Erased(_) => nil(),
            GoType::EmptyStruct | GoType::Struct(_) => {
                GoExpression::Composite { type_: spelled.clone(), fields: vec![] }
            }
            GoType::Named(name)
                if matches!(
                    name.as_str(),
                    "int32"
                        | "int64"
                        | "uint64"
                        | "uint32"
                        | "uint16"
                        | "uint8"
                        | "int"
                        | "float64"
                ) =>
            {
                GoExpression::Integer(0)
            }
            GoType::Named(name) if depth < 8 => {
                let underlying = self.declared.get(name)?;
                let spelled = match underlying {
                    GoType::Struct(_) | GoType::EmptyStruct => spelled,
                    _ => underlying,
                };
                return self.literal(spelled, underlying, depth + 1);
            }
            _ => return None,
        })
    }
}
