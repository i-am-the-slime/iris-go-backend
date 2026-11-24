use rustc_hash::FxHashMap;

use crate::foreign::ForeignPackages;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression};

pub(super) struct Forwarders {
    methods: FxHashMap<(String, String), String>,
}

impl Forwarders {
    pub(super) fn new(foreign_packages: &ForeignPackages) -> Forwarders {
        let methods = foreign_packages
            .sources
            .iter()
            .flat_map(|source| {
                let package = ForeignPackages::package_name(&source.module);
                source.forwarders.iter().map(move |(function, method)| {
                    ((package.clone(), function.clone()), method.clone())
                })
            })
            .collect();
        Forwarders { methods }
    }

    pub(super) fn call_methods(&self, declarations: &mut [GoDeclaration]) {
        if self.methods.is_empty() {
            return;
        }
        for declaration in declarations {
            go_traversal::declaration(&mut MethodCalls { forwarders: self }, declaration);
        }
    }

    fn method(&self, function: &GoExpression) -> Option<&String> {
        let function = match function.unattributed() {
            GoExpression::Instantiation { function, .. } => function.unattributed(),
            function => function,
        };
        let GoExpression::Qualified { package, name } = function else { return None };
        self.methods.get(&(package.clone(), name.clone()))
    }
}

struct MethodCalls<'f> {
    forwarders: &'f Forwarders,
}

impl Walk for MethodCalls<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        let GoExpression::Call { function, arguments } = value else { return };
        let Some(method) = self.forwarders.method(function) else { return };
        if arguments.is_empty() {
            return;
        }
        let receiver = arguments.remove(0);
        **function = GoExpression::Field { value: Box::new(receiver), name: method.clone() };
    }
}
