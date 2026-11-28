use rustc_hash::FxHashSet;

use super::aliases::is_named;
use super::locals::NUMBERED;
use crate::go_traversal::{self, Walk};
use crate::syntax::{
    GoBuiltin, GoDeclaration, GoExpression, GoPackage, GoStatement, GoType, GoUnaryOperator,
};

const BUILTINS: &[GoBuiltin] = &[
    GoBuiltin::Len,
    GoBuiltin::Cap,
    GoBuiltin::Append,
    GoBuiltin::Min,
    GoBuiltin::Max,
    GoBuiltin::Copy,
    GoBuiltin::Make,
];
const RUNTIME_PACKAGES: &[GoPackage] =
    &[GoPackage::Prim, GoPackage::Array, GoPackage::Math, GoPackage::Slices];

pub(super) fn promote_array_parameters(
    declarations: &mut [GoDeclaration],
    helpers: &FxHashSet<String>,
) {
    for declaration in declarations.iter_mut() {
        let Some(array) = promotable_parameter(declaration) else { continue };
        let mut names = declaration.all_names();
        let GoDeclaration::Function { body, result, .. } = declaration else { continue };
        if !loops_without_defers(body) {
            continue;
        }
        let mut uses = Uses { array: &array, escapes: false, dereferences: 0, writes: 0 };
        uses.block(body);
        if uses.escapes || uses.writes == 0 {
            continue;
        }
        let local = fresh(&array, &mut names);
        let original = body.clone();
        let mut promotion =
            Promotion { array: &array, local: &local, helpers, reaches_the_array: false };
        promotion.rewrite(body);
        if promotion.reaches_the_array {
            *body = original;
            continue;
        }
        let falls_through = !matches!(body.last(), Some(GoStatement::Return(_)));
        if result.is_none() && falls_through {
            body.push(promotion.write_back());
        }
        let read =
            GoStatement::Define { names: vec![local.clone()], values: vec![dereference(&array)] };
        body.insert(0, read);
    }
}

fn promotable_parameter(declaration: &GoDeclaration) -> Option<String> {
    let GoDeclaration::Function { parameters, .. } = declaration else { return None };
    let mut arrays = parameters.iter().filter(|(_, type_)| is_array_cell(type_));
    let (array, _) = arrays.next()?;
    if arrays.next().is_some() {
        return None;
    }
    let others_are_scalars =
        parameters.iter().all(|(name, type_)| name == array || is_scalar(type_));
    others_are_scalars.then(|| array.clone())
}

fn is_array_cell(type_: &GoType) -> bool {
    matches!(type_, GoType::Pointer(cell) if matches!(cell.as_ref(), GoType::Slice(_)))
}

fn is_scalar(type_: &GoType) -> bool {
    matches!(
        type_,
        GoType::Int
            | GoType::Float64
            | GoType::Bool
            | GoType::Rune
            | GoType::String
            | GoType::EmptyStruct
    )
}

fn dereference(array: &str) -> GoExpression {
    GoExpression::Unary {
        operator: GoUnaryOperator::Dereference,
        operand: Box::new(GoExpression::Identifier(array.to_string())),
    }
}

fn is_dereference(expression: &GoExpression, array: &str) -> bool {
    matches!(expression, GoExpression::Unary { operator: GoUnaryOperator::Dereference, operand } if is_named(operand, array))
}

fn fresh(array: &str, names: &mut FxHashSet<String>) -> String {
    let mut candidate = format!("{array}Elements{NUMBERED}");
    let mut counter = 2;
    while names.contains(&candidate) {
        candidate = format!("{array}Elements{NUMBERED}{counter}");
        counter += 1;
    }
    names.insert(candidate.clone());
    candidate
}

struct Uses<'a> {
    array: &'a str,
    escapes: bool,
    dereferences: usize,
    writes: usize,
}

impl Walk for Uses<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Assign { targets, .. } = statement {
            self.writes +=
                targets.iter().filter(|target| is_dereference(target, self.array)).count();
        }
        let bound: Vec<&str> = match statement {
            GoStatement::Define { names, .. } => names.iter().map(String::as_str).collect(),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => vec![name],
            GoStatement::Range { element, index, .. } => {
                index.iter().map(String::as_str).chain([element.as_str()]).collect()
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                vec![variable.as_str()]
            }
            _ => vec![],
        };
        if bound.contains(&self.array) {
            self.escapes = true;
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            _ if is_dereference(value, self.array) => self.dereferences += 1,
            GoExpression::Identifier(name) if name == self.array => self.escapes = true,
            GoExpression::Function { .. } => {
                let mut inner =
                    Uses { array: self.array, escapes: false, dereferences: 0, writes: 0 };
                go_traversal::expression(&mut inner, value);
                self.escapes |= inner.escapes || inner.dereferences > 0;
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

struct Promotion<'a> {
    array: &'a str,
    local: &'a str,
    helpers: &'a FxHashSet<String>,
    reaches_the_array: bool,
}

impl Promotion<'_> {
    fn write_back(&self) -> GoStatement {
        GoStatement::Assign {
            targets: vec![dereference(self.array)],
            values: vec![GoExpression::Identifier(self.local.to_string())],
        }
    }

    fn rewrite(&mut self, block: &mut Vec<GoStatement>) {
        let statements = std::mem::take(block);
        for mut statement in statements {
            if self.may_reach_the_array(&mut statement) {
                self.reaches_the_array = true;
                block.push(statement);
                continue;
            }
            if self.may_throw(&mut statement) || matches!(statement, GoStatement::Return(_)) {
                block.push(self.write_back());
            }
            self.replace_in_headers(&mut statement);
            self.rewrite_nested(&mut statement);
            block.push(statement);
        }
    }

    fn may_reach_the_array(&self, statement: &mut GoStatement) -> bool {
        if matches!(statement, GoStatement::Defer(_)) {
            return true;
        }
        let mut headers = Headers { helpers: self.helpers, reaches: false, throws: false };
        headers.header_expressions(statement);
        headers.reaches
    }

    fn may_throw(&self, statement: &mut GoStatement) -> bool {
        let mut headers = Headers { helpers: self.helpers, reaches: false, throws: false };
        headers.header_expressions(statement);
        headers.throws
    }

    fn replace_in_headers(&self, statement: &mut GoStatement) {
        let mut replace = Replace { array: self.array, local: self.local };
        for_each_header(statement, |expression| replace.expression(expression));
    }

    fn rewrite_nested(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::If { then, otherwise, .. } => {
                self.rewrite(then);
                self.rewrite(otherwise);
            }
            GoStatement::Switch { cases, default, .. } => {
                for case in cases {
                    self.rewrite(&mut case.body);
                }
                if let Some(default) = default {
                    self.rewrite(&mut default.body);
                }
            }
            GoStatement::IfAssert { then: body, .. }
            | GoStatement::Range { body, .. }
            | GoStatement::Counting { body, .. }
            | GoStatement::CountingDown { body, .. }
            | GoStatement::Loop(body)
            | GoStatement::LabeledLoop { body, .. } => self.rewrite(body),
            _ => {}
        }
    }
}

fn for_each_header(statement: &mut GoStatement, mut visit: impl FnMut(&mut GoExpression)) {
    match statement {
        GoStatement::Define { values, .. } => values.iter_mut().for_each(visit),
        GoStatement::Variable { value: Some(value), .. }
        | GoStatement::Return(Some(value))
        | GoStatement::Expression(value)
        | GoStatement::Defer(value)
        | GoStatement::If { condition: value, .. }
        | GoStatement::IfAssert { value, .. }
        | GoStatement::Range { iterable: value, .. }
        | GoStatement::CountingDown { start: value, .. } => visit(value),
        GoStatement::Assign { targets, values } => {
            targets.iter_mut().chain(values.iter_mut()).for_each(visit)
        }
        GoStatement::Switch { value, cases, default } => {
            value.iter_mut().for_each(&mut visit);
            for case in cases {
                case.values.iter_mut().for_each(&mut visit);
            }
            if let Some(default) = default {
                default.covers.iter_mut().for_each(&mut visit);
            }
        }
        GoStatement::Counting { start, end, .. } => {
            visit(start);
            visit(end);
        }
        _ => {}
    }
}

struct Headers<'a> {
    helpers: &'a FxHashSet<String>,
    reaches: bool,
    throws: bool,
}

impl Headers<'_> {
    fn header_expressions(&mut self, statement: &mut GoStatement) {
        for_each_header(statement, |expression| self.expression(expression));
    }

    fn is_safe_callee(&self, function: &GoExpression) -> bool {
        match function {
            GoExpression::Identifier(name) => {
                function.is_one_of(BUILTINS) || self.helpers.contains(name)
            }
            GoExpression::Qualified { package, .. } => {
                RUNTIME_PACKAGES.iter().any(|runtime| package.is(*runtime))
            }
            GoExpression::Instantiation { function, .. } => self.is_safe_callee(function),
            _ => false,
        }
    }
}

impl Walk for Headers<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Function { .. } => self.reaches = true,
            GoExpression::Call { function, .. } if !self.is_safe_callee(function) => {
                self.reaches = true
            }
            GoExpression::Call { function, .. } if is_runtime_call(function) => {
                self.throws = true;
                go_traversal::expression(self, value);
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

struct Replace<'a> {
    array: &'a str,
    local: &'a str,
}

impl Walk for Replace<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        if is_dereference(value, self.array) {
            *value = GoExpression::Identifier(self.local.to_string());
            return;
        }
        go_traversal::expression(self, value);
    }
}

fn loops_without_defers(body: &mut Vec<GoStatement>) -> bool {
    let mut loops = false;
    let mut defers = false;
    go_traversal::each_block(body, |block| {
        for statement in block.iter() {
            loops |= matches!(
                statement,
                GoStatement::Loop(_)
                    | GoStatement::LabeledLoop { .. }
                    | GoStatement::Range { .. }
                    | GoStatement::Counting { .. }
                    | GoStatement::CountingDown { .. }
            );
            defers |= matches!(statement, GoStatement::Defer(_));
        }
    });
    loops && !defers
}

fn is_runtime_call(function: &GoExpression) -> bool {
    match function {
        GoExpression::Qualified { .. } => !is_arithmetic(function),
        GoExpression::Instantiation { function, .. } => is_runtime_call(function),
        _ => false,
    }
}

fn is_arithmetic(function: &GoExpression) -> bool {
    let is_prim_arithmetic = |name: &str| {
        (name.starts_with("Int") || name.starts_with("Number"))
            && !name.starts_with("NumberTo")
            && !name.starts_with("IntToString")
    };
    function.name_in(GoPackage::Math).is_some()
        || function.name_in(GoPackage::Prim).is_some_and(is_prim_arithmetic)
}
