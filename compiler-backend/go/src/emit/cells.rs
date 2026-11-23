use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};

use super::aliases::{is_named, target_root};
use super::build::breaks_to;
use super::headers::{BUILTINS, Effects};
use super::inlining::fresh;
use super::scalars::Structs;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Cell {
    Reference,
    Array,
}

pub(super) fn holds_cells(type_: &GoType, structs: &Structs) -> bool {
    if Cell::of(type_).is_some() {
        return true;
    }
    let GoType::Pointer(pointee) = type_ else { return false };
    let GoType::Named(name) = pointee.as_ref() else { return false };
    structs
        .get(name)
        .is_some_and(|fields| fields.iter().any(|(_, field)| Cell::of(field).is_some()))
}

impl Cell {
    fn of(type_: &GoType) -> Option<Cell> {
        let GoType::Pointer(pointee) = type_ else { return None };
        match pointee.as_ref() {
            GoType::Slice(_) => Some(Cell::Array),
            GoType::Generic { name, .. } if name == "Ref" => Some(Cell::Reference),
            _ => None,
        }
    }

    fn access(self, cell: &str) -> GoExpression {
        let cell = Box::new(GoExpression::Identifier(cell.to_string()));
        match self {
            Cell::Reference => GoExpression::Field { value: cell, name: "Value".into() },
            Cell::Array => GoExpression::Unary { operator: "*", operand: cell },
        }
    }

    fn accessed(self, expression: &GoExpression) -> Option<&GoExpression> {
        match (self, expression) {
            (Cell::Reference, GoExpression::Field { value, name }) if name == "Value" => {
                Some(value)
            }
            (Cell::Array, GoExpression::Unary { operator: "*", operand }) => Some(operand),
            _ => None,
        }
    }

    fn local_base(self, parameter: &str) -> String {
        match self {
            Cell::Reference => format!("{parameter}Value"),
            Cell::Array => format!("{parameter}Elements"),
        }
    }
}

pub(super) fn keep_parameter_cells_in_locals(
    declarations: &mut [GoDeclaration],
    helpers: &FxHashSet<String>,
    effects: &Effects,
    never_recovering: &BTreeSet<String>,
) {
    let declared: FxHashSet<String> = declarations
        .iter()
        .filter_map(|declaration| match declaration {
            GoDeclaration::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let caught = caught_functions(declarations, &declared, never_recovering);
    let calls = Calls { declared: &declared, helpers, effects };
    for declaration in declarations.iter_mut() {
        let GoDeclaration::Function { name, .. } = declaration else { continue };
        let caught = caught.contains(name.as_str());
        let mut names = declaration.all_names();
        let GoDeclaration::Function { parameters, result, body, .. } = declaration else {
            continue;
        };
        if !loops(body) || !calls.keep_cells(body, caught) {
            continue;
        }
        let typed = parameters.clone();
        for (parameter, type_) in &typed {
            let Some(cell) = Cell::of(type_) else { continue };
            if !only_accessed(body, parameter, cell) || !unaliased(body, &typed, parameter, cell) {
                continue;
            }
            let local = fresh(&cell.local_base(parameter), &mut names);
            keep_in_local(body, parameter, &local, cell, result.is_none(), caught);
        }
    }
}

const NEVER_RECOVERING: &[&str] = &[
    "prim",
    "array",
    "object",
    "nullable",
    "lazy",
    "alloc",
    "regex",
    "bigints",
    "jsbigint",
    "console",
    "now",
    "datetime",
    "refeq",
    "argonaut",
    "foreignvalue",
    "eventloop",
    "strconv",
    "strings",
    "slices",
    "maps",
    "math",
    "bits",
    "utf8",
    "utf16",
    "unicode",
    "sort",
    "fmt",
    "os",
    "simd",
    "archsimd",
    "bytes",
    "time",
    "sync",
    "atomic",
    "unsafe",
];

fn caught_functions(
    declarations: &mut [GoDeclaration],
    declared: &FxHashSet<String>,
    never_recovering: &BTreeSet<String>,
) -> FxHashSet<String> {
    let mut references = FxHashMap::default();
    let mut caught = FxHashSet::default();
    let mut escaped = FxHashSet::default();
    let mut recovering = false;
    for declaration in declarations.iter_mut() {
        let Some(name) = declaration.name().map(str::to_string) else { continue };
        let mut walk = References {
            declared,
            never_recovering,
            referenced: FxHashSet::default(),
            caught: &mut caught,
            escaped: &mut escaped,
            recovering: &mut recovering,
            catching: 0,
            literals: 0,
        };
        go_traversal::declaration(&mut walk, declaration);
        references.insert(name, walk.referenced);
    }
    if !recovering {
        return FxHashSet::default();
    }
    let mut pending: Vec<String> = caught.into_iter().chain(escaped).collect();
    let mut reached = FxHashSet::default();
    while let Some(name) = pending.pop() {
        if let Some(referenced) = references.get(&name)
            && reached.insert(name)
        {
            pending.extend(referenced.iter().cloned());
        }
    }
    reached
}

struct References<'a> {
    declared: &'a FxHashSet<String>,
    never_recovering: &'a BTreeSet<String>,
    referenced: FxHashSet<String>,
    caught: &'a mut FxHashSet<String>,
    escaped: &'a mut FxHashSet<String>,
    recovering: &'a mut bool,
    catching: usize,
    literals: usize,
}

impl References<'_> {
    fn recovers(&self, function: &GoExpression) -> bool {
        match function {
            GoExpression::Qualified { package, name } if package == "direct" => {
                name.starts_with("Catch")
            }
            GoExpression::Qualified { package, .. } => {
                !NEVER_RECOVERING.contains(&package.as_str())
                    && !self.never_recovering.contains(package)
            }
            GoExpression::Instantiation { function, .. } => self.recovers(function),
            _ => false,
        }
    }

    fn refer(&mut self, name: &str, called: bool) {
        if !self.declared.contains(name) {
            return;
        }
        self.referenced.insert(name.to_string());
        if self.catching > 0 {
            self.caught.insert(name.to_string());
        }
        if self.literals > 0 || !called {
            self.escaped.insert(name.to_string());
        }
    }
}

impl Walk for References<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Call { function, arguments } => {
                let recovers = self.recovers(function);
                match function.as_mut() {
                    GoExpression::Identifier(name) => {
                        let name = name.clone();
                        self.refer(&name, true);
                    }
                    function => self.expression(function),
                }
                if recovers {
                    self.catching += 1;
                    *self.recovering = true;
                }
                arguments.iter_mut().for_each(|argument| self.expression(argument));
                if recovers {
                    self.catching -= 1;
                }
            }
            GoExpression::Identifier(name) => {
                let name = name.clone();
                self.refer(&name, false);
            }
            GoExpression::Function { .. } => {
                self.literals += 1;
                go_traversal::expression(self, value);
                self.literals -= 1;
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

pub(super) fn forward_constructed_fields(declarations: &mut [GoDeclaration]) {
    for declaration in declarations.iter_mut() {
        if !matches!(declaration, GoDeclaration::Function { .. }) {
            continue;
        }
        let fixed = fixed_names(declaration);
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if forward_at(block, position, &fixed) {
                    block.remove(position);
                } else {
                    position += 1;
                }
            }
        });
    }
}

fn forward_at(block: &mut [GoStatement], position: usize, fixed: &FxHashSet<String>) -> bool {
    let GoStatement::Define { names, values } = &block[position] else { return false };
    let ([name], [GoExpression::Address(composite)]) = (names.as_slice(), values.as_slice()) else {
        return false;
    };
    let GoExpression::Composite { fields, .. } = composite.as_ref() else { return false };
    let mut forwarded = vec![];
    for (field, value) in fields {
        let fixed_value = match value {
            GoExpression::Identifier(value_name) => fixed.contains(value_name),
            GoExpression::Integer(_) | GoExpression::Boolean(_) | GoExpression::Rune(_) => true,
            _ => false,
        };
        let Some(field) = field.as_ref().filter(|_| fixed_value) else { return false };
        forwarded.push((field.clone(), value.clone()));
    }
    if !fixed.contains(name) {
        return false;
    }
    let name = name.clone();
    let rest = &mut block[position + 1..];
    let mut reads = FieldReads { name: &name, fields: &forwarded, only: true };
    rest.iter_mut().for_each(|statement| reads.statement(statement));
    if !reads.only {
        return false;
    }
    for statement in rest {
        go_traversal::each_expression_in_statement(statement, |expression| {
            if let GoExpression::Field { value, name: field } = expression
                && is_named(value, &name)
                && let Some((_, forwarded)) = forwarded.iter().find(|(known, _)| known == field)
            {
                *expression = forwarded.clone();
            }
        });
    }
    true
}

pub(super) fn substitute_cell_aliases(declarations: &mut [GoDeclaration]) {
    for declaration in declarations.iter_mut() {
        if !matches!(declaration, GoDeclaration::Function { .. }) {
            continue;
        }
        let fixed = fixed_names(declaration);
        let mut allocations = FxHashSet::default();
        go_traversal::each_block_in_declaration(declaration, |block| {
            for statement in block.iter() {
                if let GoStatement::Define { names, values } = statement
                    && let ([name], [GoExpression::Address(_)]) =
                        (names.as_slice(), values.as_slice())
                    && fixed.contains(name)
                {
                    allocations.insert(name.clone());
                }
            }
        });
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                let alias = match &block[position] {
                    GoStatement::Define { names, values } => match (&names[..], &values[..]) {
                        ([alias], [GoExpression::Identifier(cell)])
                            if fixed.contains(alias) && allocations.contains(cell) =>
                        {
                            Some((alias.clone(), cell.clone()))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let Some((alias, cell)) = alias else {
                    position += 1;
                    continue;
                };
                for statement in &mut block[position + 1..] {
                    go_traversal::each_expression_in_statement(statement, |expression| {
                        if is_named(expression, &alias) {
                            *expression = GoExpression::Identifier(cell.clone());
                        }
                    });
                }
                block.remove(position);
            }
        });
    }
}

struct FieldReads<'a> {
    name: &'a str,
    fields: &'a [(String, GoExpression)],
    only: bool,
}

impl Walk for FieldReads<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Assign { targets, .. } = statement
            && targets.iter().any(|target| target_root(target) == Some(self.name))
        {
            self.only = false;
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Field { value: base, name }
                if is_named(base, self.name)
                    && self.fields.iter().any(|(field, _)| field == name) => {}
            GoExpression::Address(place)
            | GoExpression::Unary { operator: "&", operand: place }
                if target_root(place) == Some(self.name) =>
            {
                self.only = false;
            }
            GoExpression::Identifier(name) if name == self.name => self.only = false,
            _ => go_traversal::expression(self, value),
        }
    }
}

fn fixed_names(declaration: &mut GoDeclaration) -> FxHashSet<String> {
    struct Bindings {
        counts: FxHashMap<String, usize>,
        written: FxHashSet<String>,
    }
    impl Bindings {
        fn bind(&mut self, name: &str) {
            *self.counts.entry(name.to_string()).or_insert(0) += 1;
        }
    }
    impl Walk for Bindings {
        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Define { names, .. } => names.iter().for_each(|name| self.bind(name)),
                GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                    self.bind(name)
                }
                GoStatement::Range { index, element, .. } => {
                    index.iter().for_each(|index| self.bind(index));
                    self.bind(element);
                }
                GoStatement::Counting { variable, .. }
                | GoStatement::CountingDown { variable, .. } => self.bind(variable),
                GoStatement::Assign { targets, .. } => {
                    for target in targets.iter() {
                        if let GoExpression::Identifier(name) = target {
                            self.written.insert(name.clone());
                        }
                    }
                }
                _ => {}
            }
            go_traversal::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Function { parameters, .. } => {
                    parameters.iter().for_each(|(name, _)| self.bind(name));
                }
                GoExpression::Address(place)
                | GoExpression::Unary { operator: "&", operand: place } => {
                    if let GoExpression::Identifier(name) = place.as_ref() {
                        self.written.insert(name.clone());
                    }
                }
                _ => {}
            }
            go_traversal::expression(self, value);
        }
    }
    let mut bindings = Bindings { counts: FxHashMap::default(), written: FxHashSet::default() };
    if let GoDeclaration::Function { parameters, .. } = declaration {
        parameters.iter().for_each(|(name, _)| bindings.bind(name));
    }
    go_traversal::declaration(&mut bindings, declaration);
    bindings
        .counts
        .into_iter()
        .filter(|(name, count)| *count == 1 && !bindings.written.contains(name))
        .map(|(name, _)| name)
        .collect()
}

fn keep_in_local(
    body: &mut Vec<GoStatement>,
    parameter: &str,
    local: &str,
    cell: Cell,
    procedure: bool,
    caught: bool,
) {
    for statement in body.iter_mut() {
        go_traversal::each_expression_in_statement(statement, |expression| {
            if cell.accessed(expression).is_some_and(|base| is_named(base, parameter)) {
                *expression = GoExpression::Identifier(local.to_string());
            }
        });
    }
    let write_back = GoStatement::Assign {
        targets: vec![cell.access(parameter)],
        values: vec![GoExpression::Identifier(local.to_string())],
    };
    WriteBack { statement: &write_back, caught }.block(body);
    if procedure && !terminates(body) {
        body.push(write_back);
    }
    let read = GoStatement::Define {
        names: vec![local.to_string()],
        values: vec![cell.access(parameter)],
    };
    body.insert(0, read);
}

struct WriteBack<'a> {
    statement: &'a GoStatement,
    caught: bool,
}

impl Walk for WriteBack<'_> {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        for mut statement in std::mem::take(body) {
            let returns = matches!(statement, GoStatement::Return(_));
            if returns || (self.caught && calls_before_its_blocks(&mut statement)) {
                body.push(self.statement.clone());
            }
            if !returns {
                self.statement(&mut statement);
            }
            body.push(statement);
        }
    }
}

fn calls_before_its_blocks(statement: &mut GoStatement) -> bool {
    let mut calls = ThrowingCalls { found: false };
    match statement {
        GoStatement::Define { values, .. } => values.iter_mut().for_each(|value| {
            calls.expression(value);
        }),
        GoStatement::Variable { value: Some(value), .. }
        | GoStatement::Expression(value)
        | GoStatement::Defer(value)
        | GoStatement::Return(Some(value))
        | GoStatement::If { condition: value, .. }
        | GoStatement::IfAssert { value, .. }
        | GoStatement::Range { iterable: value, .. }
        | GoStatement::CountingDown { start: value, .. } => calls.expression(value),
        GoStatement::Assign { targets, values } => {
            targets.iter_mut().chain(values.iter_mut()).for_each(|value| calls.expression(value))
        }
        GoStatement::Switch { value, cases, .. } => {
            value.iter_mut().for_each(|value| calls.expression(value));
            for case in cases.iter_mut() {
                case.values.iter_mut().for_each(|value| calls.expression(value));
            }
        }
        GoStatement::Counting { start, end, .. } => {
            calls.expression(start);
            calls.expression(end);
        }
        GoStatement::Variable { value: None, .. }
        | GoStatement::Return(None)
        | GoStatement::Loop(_)
        | GoStatement::LabeledLoop { .. }
        | GoStatement::Continue
        | GoStatement::Break
        | GoStatement::BreakTo(_)
        | GoStatement::Line(_) => {}
    }
    calls.found
}

struct ThrowingCalls {
    found: bool,
}

impl Walk for ThrowingCalls {
    fn expression(&mut self, value: &mut GoExpression) {
        if let GoExpression::Call { function, .. } = value {
            let builtin = matches!(function.as_ref(), GoExpression::Identifier(name)
                if name != "panic" && BUILTINS.contains(&name.as_str()));
            self.found |= !builtin;
        }
        go_traversal::expression(self, value);
    }
}

fn terminates(statements: &[GoStatement]) -> bool {
    let last = statements.iter().rev().find(|statement| !matches!(statement, GoStatement::Line(_)));
    match last {
        Some(GoStatement::Return(_) | GoStatement::Continue) => true,
        Some(GoStatement::If { then, otherwise, .. }) => terminates(then) && terminates(otherwise),
        Some(GoStatement::Switch { cases, default: Some(default), .. }) => {
            cases.iter().all(|case| terminates(&case.body) && !breaks(&case.body))
                && terminates(&default.body)
                && !breaks(&default.body)
        }
        Some(GoStatement::Loop(body)) => !breaks(body),
        Some(GoStatement::LabeledLoop { label, body }) => !breaks(body) && !breaks_to(body, label),
        _ => false,
    }
}

fn breaks(statements: &[GoStatement]) -> bool {
    statements.iter().any(|statement| match statement {
        GoStatement::Break => true,
        GoStatement::If { then, otherwise, .. } => breaks(then) || breaks(otherwise),
        GoStatement::IfAssert { then, .. } => breaks(then),
        _ => false,
    })
}

fn loops(body: &mut Vec<GoStatement>) -> bool {
    let mut found = false;
    go_traversal::each_block(body, |block| {
        found |= block.iter().any(|statement| {
            matches!(
                statement,
                GoStatement::Loop(_)
                    | GoStatement::LabeledLoop { .. }
                    | GoStatement::Range { .. }
                    | GoStatement::Counting { .. }
                    | GoStatement::CountingDown { .. }
            )
        });
    });
    found
}

struct Calls<'a> {
    declared: &'a FxHashSet<String>,
    helpers: &'a FxHashSet<String>,
    effects: &'a Effects,
}

impl Calls<'_> {
    fn keep_cells(&self, body: &mut Vec<GoStatement>, caught: bool) -> bool {
        let mut keeps = true;
        go_traversal::each_block(body, |block| {
            keeps &= !block.iter().any(|statement| matches!(statement, GoStatement::Defer(_)));
            for statement in block.iter_mut() {
                if let GoStatement::Counting { end, .. } = statement
                    && caught
                {
                    let mut calls = ThrowingCalls { found: false };
                    calls.expression(end);
                    keeps &= !calls.found;
                }
            }
        });
        for statement in body.iter_mut() {
            go_traversal::each_expression_in_statement(statement, |expression| match expression {
                GoExpression::Function { .. } => keeps = false,
                GoExpression::Call { function, .. } => keeps &= self.keeps_cells(function),
                _ => {}
            });
        }
        keeps
    }

    fn keeps_cells(&self, function: &GoExpression) -> bool {
        match function {
            GoExpression::Identifier(name) if self.declared.contains(name.as_str()) => false,
            GoExpression::Identifier(name) if name == "panic" => false,
            GoExpression::Identifier(name) => {
                BUILTINS.contains(&name.as_str()) || self.helpers.contains(name.as_str())
            }
            GoExpression::Qualified { package, name } => {
                !self.effects.contains(&(package.clone(), name.clone()))
            }
            GoExpression::Instantiation { function, .. } => self.keeps_cells(function),
            _ => false,
        }
    }
}

fn only_accessed(body: &mut [GoStatement], parameter: &str, cell: Cell) -> bool {
    struct Accesses<'a> {
        parameter: &'a str,
        cell: Cell,
        only: bool,
    }
    impl Walk for Accesses<'_> {
        fn statement(&mut self, statement: &mut GoStatement) {
            let rebinds = match statement {
                GoStatement::Define { names, .. } => {
                    names.iter().any(|name| name == self.parameter)
                }
                GoStatement::Variable { name, .. } => name == self.parameter,
                _ => false,
            };
            self.only &= !rebinds;
            go_traversal::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            if self.cell.accessed(value).is_some_and(|base| is_named(base, self.parameter)) {
                return;
            }
            if is_named(value, self.parameter) {
                self.only = false;
                return;
            }
            go_traversal::expression(self, value);
        }
    }
    let mut accesses = Accesses { parameter, cell, only: true };
    body.iter_mut().for_each(|statement| accesses.statement(statement));
    accesses.only
}

fn unaliased(
    body: &mut [GoStatement],
    parameters: &[(String, GoType)],
    parameter: &str,
    cell: Cell,
) -> bool {
    let (_, type_) = parameters.iter().find(|(name, _)| name == parameter).expect("a parameter");
    let distinct = |base: &GoExpression| match base {
        GoExpression::Identifier(name) if name == parameter => true,
        GoExpression::Identifier(name) => {
            parameters.iter().any(|(other, other_type)| other == name && other_type != type_)
        }
        _ => false,
    };
    let mut unaliased = true;
    for statement in body.iter_mut() {
        go_traversal::each_expression_in_statement(statement, |expression| {
            if let Some(base) = cell.accessed(expression) {
                unaliased &= distinct(base);
            }
        });
    }
    unaliased
}
