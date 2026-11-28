use rustc_hash::{FxHashMap, FxHashSet};

use super::aliases::target_root;
use super::cells::holds_cells;
use super::locals::NUMBERED;
use super::scalars::Structs;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

const LARGEST_INLINED_LOOP: usize = 64;

struct Callee {
    parameters: Vec<(String, GoType)>,
    result: Option<GoType>,
    body: Vec<GoStatement>,
}

pub(super) fn inline_called_cell_loops(declarations: &mut Vec<GoDeclaration>, structs: &Structs) {
    let callees: FxHashMap<String, Callee> =
        declarations.iter().filter_map(|declaration| callee(declaration, structs)).collect();
    if callees.is_empty() {
        return;
    }
    for declaration in declarations.iter_mut() {
        let GoDeclaration::Function { name, .. } = declaration else { continue };
        let caller = name.clone();
        let mut names = declaration.all_names();
        let GoDeclaration::Function { body, .. } = declaration else { continue };
        let mut inliner =
            Inliner { callees: &callees, caller: &caller, names: &mut names, depth: 0 };
        inliner.block(body);
    }
    drop_inlined_everywhere(declarations, &callees);
}

/// Removes the callees no other function calls any more, now that their callers hold them.
fn drop_inlined_everywhere(
    declarations: &mut Vec<GoDeclaration>,
    callees: &FxHashMap<String, Callee>,
) {
    let mut referenced = FxHashSet::default();
    for declaration in declarations.iter_mut() {
        let own = match declaration {
            GoDeclaration::Function { name, .. } => Some(name.clone()),
            _ => None,
        };
        let names = declaration.declared_names();
        referenced.extend(
            names
                .names
                .into_iter()
                .filter(|name| !names.locals.contains(name) && Some(name) != own.as_ref()),
        );
    }
    declarations.retain(|declaration| match declaration {
        GoDeclaration::Function { name, .. } if callees.contains_key(name) => {
            referenced.contains(name)
        }
        _ => true,
    });
}

pub(super) fn inline_cell_constructors(declarations: &mut [GoDeclaration]) {
    let constructors: FxHashMap<String, Vec<GoStatement>> =
        declarations.iter().filter_map(constructor).collect();
    if constructors.is_empty() {
        return;
    }
    for declaration in declarations.iter_mut() {
        let GoDeclaration::Function { name, .. } = declaration else { continue };
        let caller = name.clone();
        let mut names = declaration.all_names();
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                let GoStatement::Define { names: defined, values } = &block[position] else {
                    position += 1;
                    continue;
                };
                let ([local], [GoExpression::Call { function, arguments }]) =
                    (defined.as_slice(), values.as_slice())
                else {
                    position += 1;
                    continue;
                };
                let constructor = match function.as_ref() {
                    GoExpression::Identifier(called)
                        if *called != caller && arguments.is_empty() =>
                    {
                        constructors.get(called)
                    }
                    _ => None,
                };
                let Some(constructor) = constructor else {
                    position += 1;
                    continue;
                };
                let local = local.clone();
                let mut body = constructor.clone();
                let mut renamed = FxHashMap::default();
                for bound in bound_names(&mut body) {
                    let fresh = fresh(&bound, &mut names);
                    renamed.insert(bound, fresh);
                }
                Rename { renamed: &renamed }.block(&mut body);
                if let Some(GoStatement::Return(Some(value))) = body.pop() {
                    body.push(GoStatement::Define { names: vec![local], values: vec![value] });
                }
                let count = body.len();
                block.splice(position..=position, body);
                position += count;
            }
        });
    }
}

fn constructor(declaration: &GoDeclaration) -> Option<(String, Vec<GoStatement>)> {
    let GoDeclaration::Function { name, parameters, result: Some(GoType::Pointer(_)), body } =
        declaration
    else {
        return None;
    };
    if !parameters.is_empty() {
        return None;
    }
    let statements: Vec<GoStatement> = body
        .iter()
        .filter(|statement| !matches!(statement, GoStatement::Line(_)))
        .cloned()
        .collect();
    let Some((GoStatement::Return(Some(built)), allocations)) = statements.split_last() else {
        return None;
    };
    let allocates = allocations.iter().all(|statement| match statement {
        GoStatement::Define { names, values } => {
            names.len() == 1 && values.len() == 1 && is_allocation(&values[0])
        }
        _ => false,
    });
    let holds_cells = !allocations.is_empty();
    (allocates && holds_cells && is_allocation(built)).then(|| (name.clone(), statements))
}

fn is_allocation(value: &GoExpression) -> bool {
    let GoExpression::Address(composite) = value else { return false };
    let GoExpression::Composite { fields, .. } = composite.as_ref() else { return false };
    fields.iter().all(|(_, field)| {
        matches!(
            field,
            GoExpression::Identifier(_)
                | GoExpression::Integer(_)
                | GoExpression::Float(_)
                | GoExpression::String(_)
                | GoExpression::Rune(_)
                | GoExpression::Boolean(_)
        )
    })
}

fn callee(declaration: &GoDeclaration, structs: &Structs) -> Option<(String, Callee)> {
    let GoDeclaration::Function { name, parameters, result, body } = declaration else {
        return None;
    };
    let mut statements = body.iter().filter(|statement| !matches!(statement, GoStatement::Line(_)));
    let (Some(GoStatement::Loop(looped)), None) = (statements.next(), statements.next()) else {
        return None;
    };
    let holds_cell = parameters.iter().any(|(_, type_)| holds_cells(type_, structs));
    if name == "main" || !holds_cell {
        return None;
    }
    let mut looped = looped.clone();
    let mut census = Census { name, size: 0, inlinable: true };
    census.block(&mut looped);
    if !census.inlinable || census.size > LARGEST_INLINED_LOOP {
        return None;
    }
    let callee = Callee { parameters: parameters.clone(), result: result.clone(), body: looped };
    Some((name.clone(), callee))
}

struct Census<'a> {
    name: &'a str,
    size: usize,
    inlinable: bool,
}

impl Walk for Census<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        self.size += 1;
        if matches!(
            statement,
            GoStatement::Defer(_) | GoStatement::LabeledLoop { .. } | GoStatement::BreakTo(_)
        ) {
            self.inlinable = false;
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Function { .. } => self.inlinable = false,
            GoExpression::Identifier(name) if name == self.name => self.inlinable = false,
            _ => go_traversal::expression(self, value),
        }
    }
}

struct Inliner<'a> {
    callees: &'a FxHashMap<String, Callee>,
    caller: &'a str,
    names: &'a mut FxHashSet<String>,
    depth: usize,
}

impl Walk for Inliner<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        if let GoExpression::Function { body, .. } = value {
            let outside = std::mem::replace(&mut self.depth, 0);
            self.block(body);
            self.depth = outside;
            return;
        }
        go_traversal::expression(self, value);
    }

    fn statement(&mut self, statement: &mut GoStatement) {
        let looped = matches!(
            statement,
            GoStatement::Loop(_)
                | GoStatement::LabeledLoop { .. }
                | GoStatement::Range { .. }
                | GoStatement::Counting { .. }
                | GoStatement::CountingDown { .. }
        );
        self.depth += usize::from(looped);
        go_traversal::statement(self, statement);
        self.depth -= usize::from(looped);
    }

    fn block(&mut self, body: &mut Vec<GoStatement>) {
        let mut position = 0;
        while position < body.len() {
            self.statement(&mut body[position]);
            let inlined = if self.depth > 0 { self.inlined(&body[position]) } else { None };
            match inlined {
                Some(statements) => {
                    let count = statements.len();
                    body.splice(position..=position, statements);
                    position += count;
                }
                None => position += 1,
            }
        }
    }
}

impl Inliner<'_> {
    fn inlined(&mut self, statement: &GoStatement) -> Option<Vec<GoStatement>> {
        let (call, result) = match statement {
            GoStatement::Expression(call) => (call, None),
            GoStatement::Define { names, values } if names.len() == 1 && values.len() == 1 => {
                (&values[0], Some(names[0].clone()))
            }
            _ => return None,
        };
        let GoExpression::Call { function, arguments } = call else { return None };
        let GoExpression::Identifier(name) = function.as_ref() else { return None };
        let callee = self.callees.get(name).filter(|_| name != self.caller)?;
        let spread = arguments.iter().any(|argument| matches!(argument, GoExpression::Spread(_)));
        if spread || arguments.len() != callee.parameters.len() {
            return None;
        }
        let result = match (result, &callee.result) {
            (None, None) => None,
            (Some(result), Some(type_)) => Some((result, type_.clone())),
            _ => return None,
        };
        let mut body = callee.body.clone();
        let bound = bound_names(&mut body);
        let written = written_names(&mut body, &callee.parameters);
        let mut renamed: FxHashMap<String, String> = FxHashMap::default();
        let mut statements = vec![];
        if let Some((name, type_)) = &result {
            statements.push(GoStatement::Variable {
                name: name.clone(),
                type_: type_.clone(),
                value: None,
            });
        }
        for ((parameter, type_), argument) in callee.parameters.iter().zip(arguments) {
            if let GoExpression::Identifier(passed) = argument
                && passed != "nil"
                && !written.contains(parameter)
                && !bound.contains(parameter)
            {
                renamed.insert(parameter.clone(), passed.clone());
                continue;
            }
            let local = fresh(parameter, self.names);
            renamed.insert(parameter.clone(), local.clone());
            statements.push(GoStatement::Variable {
                name: local,
                type_: type_.clone(),
                value: Some(argument.clone()),
            });
        }
        for name in bound {
            if renamed.contains_key(&name) {
                continue;
            }
            let local = fresh(&name, self.names);
            renamed.insert(name, local);
        }
        Rename { renamed: &renamed }.block(&mut body);
        let label = fresh(name, self.names);
        let result_name = result.map(|(name, _)| name);
        let mut exits = Exits { label: &label, result: result_name.as_deref(), count: 0 };
        exits.block(&mut body);
        statements.push(if exits.count > 0 {
            GoStatement::LabeledLoop { label, body }
        } else {
            GoStatement::Loop(body)
        });
        Some(statements)
    }
}

pub(super) fn fresh(name: &str, names: &mut FxHashSet<String>) -> String {
    let base = match name.rfind(NUMBERED) {
        Some(mark) => &name[..mark],
        None => name,
    };
    let mut candidate = format!("{base}{NUMBERED}");
    let mut counter = 2;
    while names.contains(&candidate) {
        candidate = format!("{base}{NUMBERED}{counter}");
        counter += 1;
    }
    names.insert(candidate.clone());
    candidate
}

fn bound_names(body: &mut Vec<GoStatement>) -> FxHashSet<String> {
    struct Bound(FxHashSet<String>);
    impl Walk for Bound {
        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Define { names, .. } => self.0.extend(names.iter().cloned()),
                GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                    self.0.insert(name.clone());
                }
                GoStatement::Range { index, element, .. } => {
                    self.0.extend(index.iter().cloned());
                    self.0.insert(element.clone());
                }
                GoStatement::Counting { variable, .. }
                | GoStatement::CountingDown { variable, .. } => {
                    self.0.insert(variable.clone());
                }
                _ => {}
            }
            go_traversal::statement(self, statement);
        }
    }
    let mut bound = Bound(FxHashSet::default());
    bound.block(body);
    bound.0.remove("_");
    bound.0
}

fn written_names(
    body: &mut Vec<GoStatement>,
    parameters: &[(String, GoType)],
) -> FxHashSet<String> {
    struct Written<'a> {
        parameters: &'a [(String, GoType)],
        written: FxHashSet<String>,
    }
    impl Written<'_> {
        fn place(&mut self, place: &GoExpression, through_pointer: bool) {
            let Some(root) = target_root(place) else { return };
            let Some((_, type_)) = self.parameters.iter().find(|(name, _)| name == root) else {
                return;
            };
            let shared = matches!(type_, GoType::Pointer(_) | GoType::Slice(_));
            let whole = matches!(place, GoExpression::Identifier(_));
            if whole || !(shared || through_pointer) {
                self.written.insert(root.to_string());
            }
        }
    }
    impl Walk for Written<'_> {
        fn statement(&mut self, statement: &mut GoStatement) {
            if let GoStatement::Assign { targets, .. } = statement {
                for target in targets.iter() {
                    self.place(target, false);
                }
            }
            go_traversal::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            if let GoExpression::Address(place) = value {
                let place = place.as_ref().clone();
                self.place(&place, false);
            }
            go_traversal::expression(self, value);
        }
    }
    let mut written = Written { parameters, written: FxHashSet::default() };
    written.block(body);
    written.written
}

pub(super) struct Rename<'a> {
    pub(super) renamed: &'a FxHashMap<String, String>,
}

impl Rename<'_> {
    fn name(&self, name: &mut String) {
        if let Some(renamed) = self.renamed.get(name.as_str()) {
            *name = renamed.clone();
        }
    }
}

impl Walk for Rename<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, .. } => names.iter_mut().for_each(|name| self.name(name)),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                self.name(name)
            }
            GoStatement::Range { index, element, .. } => {
                index.iter_mut().for_each(|index| self.name(index));
                self.name(element);
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.name(variable)
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        if let GoExpression::Identifier(name) = value {
            self.name(name);
            return;
        }
        go_traversal::expression(self, value);
    }
}

struct Exits<'a> {
    label: &'a str,
    result: Option<&'a str>,
    count: usize,
}

impl Walk for Exits<'_> {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        for statement in std::mem::take(body) {
            match statement {
                GoStatement::Return(value) => {
                    if let (Some(result), Some(value)) = (self.result, value) {
                        body.push(GoStatement::Assign {
                            targets: vec![GoExpression::Identifier(result.to_string())],
                            values: vec![value],
                        });
                    }
                    body.push(GoStatement::BreakTo(self.label.to_string()));
                    self.count += 1;
                }
                mut statement => {
                    self.statement(&mut statement);
                    body.push(statement);
                }
            }
        }
    }
}
