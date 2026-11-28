use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};

use super::cells::{Calls, WriteBack, caught_functions, loops, terminates};
use super::headers::Effects;
use super::inlining::fresh;
use crate::foreign::ForeignPackages;
use crate::go_traversal::{self, Walk};
use crate::naming::capitalise;
use crate::primitives::SHARED_CELLS;
use crate::syntax::{GoDeclaration, GoExpression, GoQualifier, GoStatement, GoType};

type InPlace = FxHashMap<(String, String), Vec<usize>>;

pub(super) fn keep_confined_cells_in_locals(
    declarations: &mut [GoDeclaration],
    foreign_packages: &ForeignPackages,
    helpers: &FxHashSet<String>,
    effects: &Effects,
    never_recovering: &BTreeSet<String>,
) {
    let in_place = foreign_packages.arguments_called_in_place();
    let declared: FxHashSet<String> = declarations
        .iter()
        .filter_map(|declaration| match declaration {
            GoDeclaration::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    for known in SHARED_CELLS {
        if !foreign_packages.provides(known.module) {
            continue;
        }
        let cell = SharedCell {
            package: ForeignPackages::package_name(known.module),
            new: capitalise(known.new),
            read: capitalise(known.read),
            write: capitalise(known.write),
            modify: capitalise(known.modify),
        };
        let facts = Facts::of(declarations, &cell, &in_place, &declared);
        let confined = facts.confined();
        let unshared = facts.unshared(&confined);
        if unshared.is_empty() {
            continue;
        }
        let caught = caught_functions(declarations, &declared, never_recovering);
        let calls = Calls { declared: &declared, helpers, effects };
        for declaration in declarations.iter_mut() {
            let GoDeclaration::Function { name, .. } = declaration else { continue };
            let Some(parameters) = unshared.get(name.as_str()) else { continue };
            let parameters = parameters.clone();
            let caught = caught.contains(name.as_str());
            keep_in_locals(declaration, &cell, &facts, &parameters, &calls, caught);
        }
    }
}

struct SharedCell {
    package: String,
    new: String,
    read: String,
    write: String,
    modify: String,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Access {
    New,
    Read,
    Write,
    Modify,
}

impl Access {
    fn cell_position(self) -> Option<usize> {
        match self {
            Access::New => None,
            Access::Read | Access::Write => Some(0),
            Access::Modify => Some(3),
        }
    }
}

impl SharedCell {
    fn access(&self, function: &GoExpression) -> Option<Access> {
        let function = match function {
            GoExpression::Instantiation { function, .. } => function,
            function => function,
        };
        let GoExpression::Qualified { package, name } = function else { return None };
        if package.name() != self.package {
            return None;
        }
        [
            (&self.new, Access::New),
            (&self.read, Access::Read),
            (&self.write, Access::Write),
            (&self.modify, Access::Modify),
        ]
        .into_iter()
        .find_map(|(known, access)| (known == name).then_some(access))
    }

    fn accessed<'e>(&self, expression: &'e GoExpression, access: Access) -> Option<&'e str> {
        let GoExpression::Call { function, arguments } = expression else { return None };
        if self.access(function) != Some(access) {
            return None;
        }
        match arguments.get(access.cell_position()?) {
            Some(GoExpression::Identifier(name)) => Some(name),
            _ => None,
        }
    }

    fn call(&self, function: &str, arguments: Vec<GoExpression>) -> GoExpression {
        let function = GoExpression::Qualified {
            package: GoQualifier::Named(self.package.clone()),
            name: function.to_string(),
        };
        GoExpression::Call { function: Box::new(function), arguments }
    }
}

#[derive(Default)]
struct Binding {
    binds: usize,
    depth: usize,
    escapes: bool,
    accessed: bool,
    modified: bool,
    made_here: bool,
    passed: Vec<(String, usize)>,
}

#[derive(Default)]
struct FunctionFacts {
    parameters: Vec<(String, GoType)>,
    bindings: FxHashMap<String, Binding>,
}

struct CallSite {
    caller: String,
    arguments: Vec<Option<String>>,
}

type CallSites = FxHashMap<String, Vec<CallSite>>;

struct Facts {
    functions: FxHashMap<String, FunctionFacts>,
    call_sites: CallSites,
    values: FxHashSet<String>,
}

impl Facts {
    fn of(
        declarations: &mut [GoDeclaration],
        cell: &SharedCell,
        in_place: &InPlace,
        declared: &FxHashSet<String>,
    ) -> Facts {
        let mut facts = Facts {
            functions: FxHashMap::default(),
            call_sites: FxHashMap::default(),
            values: FxHashSet::default(),
        };
        for declaration in declarations.iter_mut() {
            if let GoDeclaration::Written { source, .. } = declaration {
                let mentioned = declared.iter().filter(|name| source.contains(name.as_str()));
                facts.values.extend(mentioned.cloned());
                continue;
            }
            let Some(name) = declaration.name().map(str::to_string) else { continue };
            let parameters = match declaration {
                GoDeclaration::Function { parameters, .. } => parameters.clone(),
                _ => vec![],
            };
            let mut uses = Uses {
                cell,
                in_place,
                declared,
                caller: &name,
                crossed: 0,
                bindings: FxHashMap::default(),
                call_sites: &mut facts.call_sites,
                values: &mut facts.values,
            };
            parameters.iter().for_each(|(parameter, _)| uses.bind(parameter));
            go_traversal::declaration(&mut uses, declaration);
            let bindings = uses.bindings;
            facts.functions.insert(name, FunctionFacts { parameters, bindings });
        }
        facts
    }

    fn binding(&self, function: &str, name: &str) -> Option<&Binding> {
        self.functions.get(function)?.bindings.get(name)
    }

    fn confined(&self) -> FxHashSet<(String, String)> {
        let mut confined: FxHashSet<(String, String)> = FxHashSet::default();
        for (function, facts) in &self.functions {
            for (name, binding) in &facts.bindings {
                if binding.binds == 1 && !binding.escapes {
                    confined.insert((function.clone(), name.clone()));
                }
            }
        }
        loop {
            let refuted: Vec<(String, String)> = confined
                .iter()
                .filter(|(function, name)| {
                    let binding = &self.functions[function].bindings[name];
                    !binding.passed.iter().all(|(callee, position)| {
                        let parameter = self
                            .functions
                            .get(callee)
                            .and_then(|facts| facts.parameters.get(*position));
                        parameter.is_some_and(|(parameter, _)| {
                            confined.contains(&(callee.clone(), parameter.clone()))
                        })
                    })
                })
                .cloned()
                .collect();
            if refuted.is_empty() {
                return confined;
            }
            refuted.iter().for_each(|refuted| {
                confined.remove(refuted);
            });
        }
    }

    fn unshared(&self, confined: &FxHashSet<(String, String)>) -> FxHashMap<String, Vec<usize>> {
        let mut unshared: FxHashSet<(String, usize)> = FxHashSet::default();
        for (function, facts) in &self.functions {
            if self.values.contains(function) {
                continue;
            }
            for (position, (parameter, _)) in facts.parameters.iter().enumerate() {
                if confined.contains(&(function.clone(), parameter.clone())) {
                    unshared.insert((function.clone(), position));
                }
            }
        }
        loop {
            let refuted: Vec<(String, usize)> = unshared
                .iter()
                .filter(|(function, position)| {
                    let sites =
                        self.call_sites.get(function).map(Vec::as_slice).unwrap_or_default();
                    !sites.iter().all(|site| {
                        let argument = site.arguments.get(*position).cloned().flatten();
                        argument.is_some_and(|argument| {
                            self.unshared_in(&site.caller, &argument, confined, &unshared)
                        })
                    })
                })
                .cloned()
                .collect();
            if refuted.is_empty() {
                break;
            }
            refuted.iter().for_each(|refuted| {
                unshared.remove(refuted);
            });
        }
        let mut by_function: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        for (function, position) in unshared {
            by_function.entry(function).or_default().push(position);
        }
        by_function
    }

    fn unshared_in(
        &self,
        caller: &str,
        argument: &str,
        confined: &FxHashSet<(String, String)>,
        unshared: &FxHashSet<(String, usize)>,
    ) -> bool {
        let Some(binding) = self.binding(caller, argument) else { return false };
        if !confined.contains(&(caller.to_string(), argument.to_string())) {
            return false;
        }
        let parameters = &self.functions[caller].parameters;
        match parameters.iter().position(|(parameter, _)| parameter == argument) {
            Some(position) => unshared.contains(&(caller.to_string(), position)),
            None => binding.made_here,
        }
    }
}

struct Uses<'a> {
    cell: &'a SharedCell,
    in_place: &'a InPlace,
    declared: &'a FxHashSet<String>,
    caller: &'a str,
    crossed: usize,
    bindings: FxHashMap<String, Binding>,
    call_sites: &'a mut CallSites,
    values: &'a mut FxHashSet<String>,
}

enum Use {
    Accessed(Access),
    Passed(String, usize),
    Other,
}

impl Uses<'_> {
    fn bind(&mut self, name: &str) {
        let binding = self.bindings.entry(name.to_string()).or_default();
        binding.binds += 1;
        binding.depth = self.crossed;
    }

    fn refer(&mut self, name: &str, used: Use) {
        let Some(binding) = self.bindings.get_mut(name) else {
            if self.declared.contains(name) {
                self.values.insert(name.to_string());
            }
            return;
        };
        if binding.depth != self.crossed {
            binding.escapes = true;
        }
        match used {
            Use::Accessed(Access::Modify) => binding.modified = true,
            Use::Accessed(_) => binding.accessed = true,
            Use::Passed(callee, position) => binding.passed.push((callee, position)),
            Use::Other => binding.escapes = true,
        }
    }

    fn run_in_place(&mut self, parameters: &[(String, GoType)], body: &mut Vec<GoStatement>) {
        parameters.iter().for_each(|(parameter, _)| self.bind(parameter));
        self.block(body);
    }

    fn call(&mut self, function: &mut GoExpression, arguments: &mut [GoExpression]) {
        if let Some(access) = self.cell.access(function) {
            for (position, argument) in arguments.iter_mut().enumerate() {
                match argument {
                    GoExpression::Identifier(name) if access.cell_position() == Some(position) => {
                        let name = name.clone();
                        self.refer(&name, Use::Accessed(access));
                    }
                    argument => self.expression(argument),
                }
            }
            return;
        }
        let function = match function {
            GoExpression::Instantiation { function, .. }
                if matches!(function.as_ref(), GoExpression::Qualified { .. }) =>
            {
                function.as_mut()
            }
            function => function,
        };
        match function {
            GoExpression::Identifier(callee) if self.declared.contains(callee.as_str()) => {
                let callee = callee.clone();
                let mut passed = vec![];
                for (position, argument) in arguments.iter_mut().enumerate() {
                    if let GoExpression::Identifier(name) = argument {
                        let name = name.clone();
                        self.refer(&name, Use::Passed(callee.clone(), position));
                        passed.push(Some(name));
                    } else {
                        self.expression(argument);
                        passed.push(None);
                    }
                }
                let site = CallSite { caller: self.caller.to_string(), arguments: passed };
                self.call_sites.entry(callee).or_default().push(site);
            }
            GoExpression::Qualified { package, name } => {
                let key = (package.name().to_string(), name.clone());
                let positions = self.in_place.get(&key).cloned().unwrap_or_default();
                for (position, argument) in arguments.iter_mut().enumerate() {
                    match argument {
                        GoExpression::Function { parameters, body, .. }
                            if positions.contains(&position) =>
                        {
                            self.run_in_place(parameters, body)
                        }
                        argument => self.expression(argument),
                    }
                }
            }
            GoExpression::Function { parameters, body, .. } => {
                self.run_in_place(parameters, body);
                arguments.iter_mut().for_each(|argument| self.expression(argument));
            }
            function => {
                self.expression(function);
                arguments.iter_mut().for_each(|argument| self.expression(argument));
            }
        }
    }
}

impl Walk for Uses<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values } => {
                let made_here = matches!(values.as_slice(), [GoExpression::Call { function, .. }]
                    if self.cell.access(function) == Some(Access::New));
                values.iter_mut().for_each(|value| self.expression(value));
                for name in names.iter() {
                    self.bind(name);
                    if made_here && names.len() == 1 {
                        self.bindings.get_mut(name.as_str()).expect("just bound").made_here = true;
                    }
                }
                return;
            }
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                let name = name.clone();
                self.bind(&name);
            }
            GoStatement::Range { index, element, .. } => {
                let names: Vec<String> = index.iter().chain([&*element]).cloned().collect();
                names.iter().for_each(|name| self.bind(name));
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                let variable = variable.clone();
                self.bind(&variable);
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Call { function, arguments } => self.call(function, arguments),
            GoExpression::Function { parameters, body, .. } => {
                self.crossed += 1;
                self.run_in_place(parameters, body);
                self.crossed -= 1;
            }
            GoExpression::Identifier(name) => {
                let name = name.clone();
                self.refer(&name, Use::Other);
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

fn keep_in_locals(
    declaration: &mut GoDeclaration,
    cell: &SharedCell,
    facts: &Facts,
    unshared: &[usize],
    calls: &Calls,
    caught: bool,
) {
    let mut names = declaration.all_names();
    let GoDeclaration::Function { name, parameters, result, body } = declaration else { return };
    if !loops(body) {
        return;
    }
    let function = &facts.functions[name.as_str()];
    let kept: Vec<String> = unshared
        .iter()
        .map(|&position| &parameters[position])
        .filter(|(parameter, type_)| {
            let binding = &function.bindings[parameter.as_str()];
            let alone = parameters.iter().filter(|(_, other)| other == type_).count() == 1;
            alone && binding.accessed && !binding.modified && binding.passed.is_empty()
        })
        .map(|(parameter, _)| parameter.clone())
        .collect();
    if kept.is_empty() || !only_calls_kept(body, cell, &kept, calls) {
        return;
    }
    let procedure = result.is_none();
    for parameter in kept {
        let local = fresh(&format!("{parameter}Value"), &mut names);
        for statement in body.iter_mut() {
            go_traversal::each_expression_in_statement(statement, |expression| {
                if cell.accessed(expression, Access::Read) == Some(parameter.as_str()) {
                    *expression = GoExpression::Identifier(local.clone());
                }
            });
        }
        go_traversal::each_block(body, |block| {
            for statement in block.iter_mut() {
                let GoStatement::Expression(written) = statement else { continue };
                if cell.accessed(written, Access::Write) != Some(parameter.as_str()) {
                    continue;
                }
                let GoExpression::Call { arguments, .. } = written else { continue };
                let value = arguments.pop().expect("a write has a value");
                *statement = GoStatement::Assign {
                    targets: vec![GoExpression::Identifier(local.clone())],
                    values: vec![value],
                };
            }
        });
        let identifiers = [&parameter, &local].map(|name| GoExpression::Identifier(name.clone()));
        let write_back = GoStatement::Expression(cell.call(&cell.write, identifiers.to_vec()));
        WriteBack { statement: &write_back, caught }.block(body);
        if procedure && !terminates(body) {
            body.push(write_back);
        }
        let read = cell.call(&cell.read, vec![GoExpression::Identifier(parameter.clone())]);
        body.insert(0, GoStatement::Define { names: vec![local], values: vec![read] });
    }
}

fn only_calls_kept(
    body: &mut Vec<GoStatement>,
    cell: &SharedCell,
    kept: &[String],
    calls: &Calls,
) -> bool {
    struct Only<'a> {
        cell: &'a SharedCell,
        kept: &'a [String],
        calls: &'a Calls<'a>,
        only: bool,
    }
    impl Walk for Only<'_> {
        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Defer(_) => self.only = false,
                GoStatement::Expression(written) => {
                    let write = self.cell.accessed(written, Access::Write);
                    if write.is_some_and(|cell| self.kept.iter().any(|kept| kept == cell)) {
                        let GoExpression::Call { arguments, .. } = written else { unreachable!() };
                        self.expression(&mut arguments[1]);
                        return;
                    }
                }
                _ => {}
            }
            go_traversal::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Function { .. } => self.only = false,
                _ if self
                    .cell
                    .accessed(value, Access::Read)
                    .is_some_and(|cell| self.kept.iter().any(|kept| kept == cell)) => {}
                GoExpression::Call { function, .. } => {
                    self.only &= self.calls.keeps_cells(function);
                    go_traversal::expression(self, value);
                }
                _ => go_traversal::expression(self, value),
            }
        }
    }
    let mut only = Only { cell, kept, calls, only: true };
    only.block(body);
    only.only
}
