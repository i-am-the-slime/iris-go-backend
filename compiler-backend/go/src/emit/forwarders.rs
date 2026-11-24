use rustc_hash::FxHashMap;

use crate::foreign::{ForeignPackages, Forward};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression};

pub(super) struct Forwarders {
    forwards: FxHashMap<(String, String), Forward>,
}

impl Forwarders {
    pub(super) fn new(foreign_packages: &ForeignPackages) -> Forwarders {
        let forwards = foreign_packages
            .sources
            .iter()
            .flat_map(|source| {
                let package = ForeignPackages::package_name(&source.module);
                source.forwarders.iter().map(move |(function, forward)| {
                    ((package.clone(), function.clone()), forward.clone())
                })
            })
            .collect();
        Forwarders { forwards }
    }

    pub(super) fn call_forwarded(&self, declarations: &mut [GoDeclaration]) {
        if self.forwards.is_empty() {
            return;
        }
        for declaration in declarations {
            go_traversal::declaration(&mut ForwardedCalls { forwarders: self }, declaration);
        }
    }

    fn forward(&self, function: &GoExpression) -> Option<&Forward> {
        let function = match function.unattributed() {
            GoExpression::Instantiation { function, .. } => function.unattributed(),
            function => function,
        };
        let GoExpression::Qualified { package, name } = function else { return None };
        self.forwards.get(&(package.clone(), name.clone()))
    }
}

struct ForwardedCalls<'f> {
    forwarders: &'f Forwarders,
}

impl Walk for ForwardedCalls<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        if let GoExpression::Qualified { package, name } = value
            && let Some(Forward::Function(function)) =
                self.forwarders.forwards.get(&(package.clone(), name.clone()))
        {
            *name = function.clone();
            return;
        }
        let GoExpression::Call { function, arguments } = value else { return };
        let Some(Forward::Method(method)) = self.forwarders.forward(function) else { return };
        if arguments.is_empty() {
            return;
        }
        let receiver = arguments.remove(0);
        **function = GoExpression::Field { value: Box::new(receiver), name: method.clone() };
    }
}
