use rustc_hash::FxHashMap;

use super::EitherShape;
use super::values::{CALL_MARK, LITERAL_MARK};
use crate::foreign::ForeignPackages;
use crate::go_traversal;
use crate::naming::capitalise;
use crate::primitives::RESULTS_VARIANTS;
use crate::syntax::{GoDeclaration, GoExpression, GoType};

struct Variant {
    package: String,
    foreign: String,
    results: String,
}

pub(super) struct Variants {
    variants: Vec<Variant>,
}

impl Variants {
    pub(super) fn provided(foreign: &ForeignPackages) -> Variants {
        let variants = RESULTS_VARIANTS
            .iter()
            .filter(|known| foreign.provides(known.module))
            .map(|known| Variant {
                package: ForeignPackages::package_name(known.module),
                foreign: capitalise(known.foreign),
                results: capitalise(known.results),
            })
            .filter(|variant| foreign.signature(&variant.package, &variant.results).is_some());
        Variants { variants: variants.collect() }
    }

    pub(super) fn either_built(
        &self,
        function: &GoExpression,
        arguments: &[GoExpression],
        shapes: &FxHashMap<String, EitherShape>,
    ) -> Option<String> {
        self.variant(function)?;
        either_every_literal_builds(arguments, shapes)
    }

    fn variant(&self, function: &GoExpression) -> Option<&Variant> {
        let (package, name) = qualified_name(function)?;
        self.variants.iter().find(|variant| variant.package == package && variant.foreign == name)
    }

    pub(super) fn call(
        &self,
        declarations: &mut [GoDeclaration],
        shapes: &FxHashMap<String, EitherShape>,
    ) -> bool {
        if self.variants.is_empty() {
            return false;
        }
        let mut called = false;
        for declaration in declarations.iter_mut() {
            go_traversal::each_expression_in_declaration(declaration, |expression| {
                if let Some(call) = self.results_variant_call(expression, shapes) {
                    *expression = call;
                    called = true;
                }
            });
        }
        called
    }

    fn results_variant_call(
        &self,
        expression: &mut GoExpression,
        shapes: &FxHashMap<String, EitherShape>,
    ) -> Option<GoExpression> {
        let GoExpression::Call { function, arguments } = expression else { return None };
        let variant = self.variant(function)?;
        let shape = either_every_literal_builds(arguments, shapes)?;
        let function = GoExpression::Qualified {
            package: variant.package.clone(),
            name: variant.results.clone(),
        };
        let literals = std::mem::take(arguments)
            .into_iter()
            .map(|literal| marked(LITERAL_MARK, &shape, vec![literal]));
        let mut marked_arguments = vec![function];
        marked_arguments.extend(literals);
        Some(marked(CALL_MARK, &shape, marked_arguments))
    }
}

fn qualified_name(function: &GoExpression) -> Option<(&str, &str)> {
    match function.unattributed() {
        GoExpression::Qualified { package, name } => Some((package, name)),
        GoExpression::Instantiation { function, .. } => qualified_name(function),
        _ => None,
    }
}

fn either_every_literal_builds(
    arguments: &[GoExpression],
    shapes: &FxHashMap<String, EitherShape>,
) -> Option<String> {
    let mut built: Option<&str> = None;
    for argument in arguments {
        let GoExpression::Function { result: Some(GoType::Named(either)), .. } =
            argument.unattributed()
        else {
            return None;
        };
        if !shapes.contains_key(either) || built.is_some_and(|built| built != either) {
            return None;
        }
        built = Some(either);
    }
    built.map(str::to_string)
}

fn marked(mark: &str, shape: &str, arguments: Vec<GoExpression>) -> GoExpression {
    GoExpression::Call {
        function: Box::new(GoExpression::Identifier(format!("{mark}{shape}"))),
        arguments,
    }
}
