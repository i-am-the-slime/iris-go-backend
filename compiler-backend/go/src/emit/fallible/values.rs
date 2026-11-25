//! Function values that return an `Either` return Go's `(A, EFailure)` too.
//!
//! The decision is made for each Go function type, `func(P) E`, over the whole program: when
//! every value of the type is made and called by generated code, the type becomes `func(P) (A,
//! EFailure)` everywhere it appears, in parameters, results, struct fields, slices and the type
//! arguments of foreign holders such as `IORef[func(P) (A, EFailure)]`. Its function literals
//! return their two results and its calls are marked for the rewrite of the enclosing function,
//! which then splits their results as it splits a top-level function's.
//!
//! Foreign functions see the Go types their signatures fix. A foreign parameter that is a type
//! parameter itself takes the value as it is; one that is a function type, such as `action func()
//! A`, is passed a function literal that keeps building the `Either`, or a literal that converts a
//! value with `EFromResults`. A type stays `Either` where the program calls a value whose type
//! comes out of a foreign function untold, or keeps one that a foreign function built.

use rustc_hash::{FxHashMap, FxHashSet};

use super::EitherShape;
use crate::foreign::{ForeignPackages, ForeignShape};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

/// The head of `§call:E(f, x)`, a call of a function value that returns two results.
pub(super) const CALL_MARK: &str = "§call:";
/// The head of `§literal:E(func(…) E { … })`, a function literal that returns two results.
pub(super) const LITERAL_MARK: &str = "§literal:";

/// The methods of a foreign holder that return the value it holds.
const READING_METHODS: &[&str] = &["Load", "Swap"];

const BUILTINS: &[&str] = &[
    "append", "cap", "clear", "close", "copy", "delete", "len", "make", "max", "min", "new",
    "panic",
];

/// Lowers the function types whose values only generated code makes and calls, marking their
/// calls and literals. The types it lowered, with what they became.
pub(super) fn lower_function_values(
    declarations: &mut [GoDeclaration],
    type_declarations: &mut [GoDeclaration],
    shapes: &FxHashMap<String, EitherShape>,
    foreign: &ForeignPackages,
) -> Vec<(GoType, GoType)> {
    let candidates = candidates(declarations, type_declarations, shapes);
    if candidates.is_empty() {
        return vec![];
    }
    let program = Program::new(declarations, type_declarations, candidates);
    let mut lowered = vec![true; program.candidates.len()];
    for declaration in declarations.iter() {
        if let GoDeclaration::Written { source, .. } = declaration {
            for (index, candidate) in program.candidates.iter().enumerate() {
                if source.contains(either_of(candidate)) {
                    lowered[index] = false;
                }
            }
        }
    }
    loop {
        let mut typer = Typer::new(&program, &lowered, foreign, false);
        for declaration in declarations.iter_mut() {
            typer.declaration(declaration);
        }
        if typer.removed.is_empty() {
            break;
        }
        for index in typer.removed {
            lowered[index] = false;
        }
    }
    if !lowered.contains(&true) {
        return vec![];
    }
    let mut typer = Typer::new(&program, &lowered, foreign, true);
    for declaration in declarations.iter_mut() {
        typer.declaration(declaration);
    }
    let mut lowered: Vec<(GoType, GoType)> = program
        .candidates
        .iter()
        .zip(&lowered)
        .filter(|(_, lowered)| **lowered)
        .map(|(candidate, _)| {
            let GoType::Function { parameters, .. } = candidate else {
                unreachable!("invariant violated: a candidate is a function type")
            };
            let results = shapes[either_of(candidate)].results();
            let to = GoType::Function {
                parameters: parameters.clone(),
                result: Some(Box::new(results)),
            };
            (candidate.clone(), to)
        })
        .collect();
    loop {
        let before = lowered.clone();
        for (_, to) in lowered.iter_mut() {
            let GoType::Function { parameters, result } = to else { continue };
            for parameter in parameters.iter_mut() {
                lower_type(parameter, &before);
            }
            if let Some(result) = result
                && let GoType::Results(results) = result.as_mut()
            {
                for result in results.iter_mut() {
                    lower_type(result, &before);
                }
            }
        }
        if lowered == before {
            break;
        }
    }
    let mut retype = |type_: &mut GoType| lower_type(type_, &lowered);
    for declaration in declarations.iter_mut().chain(type_declarations.iter_mut()) {
        each_type_in_declaration(declaration, &mut retype);
    }
    lowered
}

/// The `Either` a candidate function type returns.
fn either_of(candidate: &GoType) -> &str {
    match candidate {
        GoType::Function { result: Some(result), .. } => match result.as_ref() {
            GoType::Named(name) => name,
            _ => "",
        },
        _ => "",
    }
}

/// The function types that return an `Either`, in the order the program first names them.
fn candidates(
    declarations: &mut [GoDeclaration],
    type_declarations: &mut [GoDeclaration],
    shapes: &FxHashMap<String, EitherShape>,
) -> Vec<GoType> {
    let mut found: Vec<GoType> = vec![];
    for declaration in type_declarations.iter_mut().chain(declarations.iter_mut()) {
        each_type_in_declaration(declaration, &mut |type_| {
            collect_function_types(type_, shapes, &mut found);
        });
        each_literal_signature(declaration, &mut |parameters, result| {
            let type_ = GoType::Function {
                parameters: parameters.to_vec(),
                result: result.cloned().map(Box::new),
            };
            collect_function_types(&mut type_.clone(), shapes, &mut found);
        });
        if let GoDeclaration::Function { parameters, result, .. } = declaration {
            let mut type_ = GoType::Function {
                parameters: parameters.iter().map(|(_, type_)| type_.clone()).collect(),
                result: result.clone().map(Box::new),
            };
            collect_function_types(&mut type_, shapes, &mut found);
        }
    }
    found
}

fn collect_function_types(
    type_: &mut GoType,
    shapes: &FxHashMap<String, EitherShape>,
    found: &mut Vec<GoType>,
) {
    each_nested_type(type_, &mut |type_| {
        if let GoType::Function { result: Some(result), .. } = type_
            && let GoType::Named(name) = result.as_ref()
            && shapes.contains_key(name)
            && !found.contains(type_)
        {
            found.push(type_.clone());
        }
    });
}

/// Calls `visit` with the signature of every function literal of the declaration.
fn each_literal_signature(
    declaration: &mut GoDeclaration,
    visit: &mut impl FnMut(&[GoType], Option<&GoType>),
) {
    crate::go_traversal::each_expression_in_declaration(declaration, |expression| {
        if let GoExpression::Function { parameters, result, .. } = expression {
            let types: Vec<GoType> = parameters.iter().map(|(_, type_)| type_.clone()).collect();
            visit(&types, result.as_ref());
        }
    });
}

/// The type with every lowered function type in it returning two results. The lowered types
/// are spelled as the program first spelled them, so a type is matched before its parts are.
pub(in crate::emit) fn lower_type(type_: &mut GoType, lowered: &[(GoType, GoType)]) {
    if let Some((_, to)) = lowered.iter().find(|(from, _)| from == type_) {
        *type_ = to.clone();
        return;
    }
    match type_ {
        GoType::Function { parameters, result } => {
            parameters.iter_mut().for_each(|parameter| lower_type(parameter, lowered));
            if let Some(result) = result {
                lower_type(result, lowered);
            }
        }
        GoType::Slice(element) | GoType::Pointer(element) => lower_type(element, lowered),
        GoType::Generic { arguments, .. } => {
            arguments.iter_mut().for_each(|argument| lower_type(argument, lowered))
        }
        GoType::Struct(fields) => {
            fields.iter_mut().for_each(|field| lower_type(&mut field.type_, lowered))
        }
        GoType::Results(results) => {
            results.iter_mut().for_each(|result| lower_type(result, lowered))
        }
        _ => {}
    }
}

/// Calls `visit` on the type and every type inside it, outer ones first.
fn each_nested_type(type_: &mut GoType, visit: &mut impl FnMut(&mut GoType)) {
    visit(type_);
    match type_ {
        GoType::Function { parameters, result } => {
            parameters.iter_mut().for_each(|parameter| each_nested_type(parameter, visit));
            if let Some(result) = result {
                each_nested_type(result, visit);
            }
        }
        GoType::Slice(element) | GoType::Pointer(element) => each_nested_type(element, visit),
        GoType::Generic { arguments, .. } => {
            arguments.iter_mut().for_each(|argument| each_nested_type(argument, visit))
        }
        GoType::Struct(fields) => {
            fields.iter_mut().for_each(|field| each_nested_type(&mut field.type_, visit))
        }
        GoType::Results(results) => {
            results.iter_mut().for_each(|result| each_nested_type(result, visit))
        }
        _ => {}
    }
}

/// Calls `visit` on every type the declaration spells, outermost ones only.
fn each_type_in_declaration(declaration: &mut GoDeclaration, visit: &mut impl FnMut(&mut GoType)) {
    match declaration {
        GoDeclaration::Type { type_, .. }
        | GoDeclaration::Alias { type_, .. }
        | GoDeclaration::GenericType { type_, .. } => visit(type_),
        GoDeclaration::Constant { type_, value, .. } => {
            if let Some(type_) = type_ {
                visit(type_);
            }
            each_type_in_expression(value, visit);
        }
        GoDeclaration::Variable { type_, value, .. } => {
            if let Some(type_) = type_ {
                visit(type_);
            }
            each_type_in_expression(value, visit);
        }
        GoDeclaration::Function { parameters, result, body, .. } => {
            parameters.iter_mut().for_each(|(_, type_)| visit(type_));
            if let Some(result) = result {
                visit(result);
            }
            each_type_in_statements(body, visit);
        }
        GoDeclaration::Source { .. }
        | GoDeclaration::Written { .. }
        | GoDeclaration::Constants { .. } => {}
    }
}

fn each_type_in_statements(body: &mut [GoStatement], visit: &mut impl FnMut(&mut GoType)) {
    struct Types<'v, F>(&'v mut F);
    impl<F: FnMut(&mut GoType)> crate::go_traversal::Walk for Types<'_, F> {
        fn statement(&mut self, statement: &mut GoStatement) {
            if let GoStatement::Variable { type_, .. } | GoStatement::IfAssert { type_, .. } =
                statement
            {
                (self.0)(type_);
            }
            crate::go_traversal::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Type(type_)
                | GoExpression::Conversion { type_, .. }
                | GoExpression::TypeAssertion { type_, .. }
                | GoExpression::Composite { type_, .. } => (self.0)(type_),
                GoExpression::Function { parameters, result, .. } => {
                    parameters.iter_mut().for_each(|(_, type_)| (self.0)(type_));
                    if let Some(result) = result {
                        (self.0)(result);
                    }
                }
                GoExpression::Instantiation { arguments, .. } => {
                    arguments.iter_mut().for_each(|argument| (self.0)(argument))
                }
                _ => {}
            }
            crate::go_traversal::expression(self, value);
        }
    }
    let mut types = Types(visit);
    body.iter_mut()
        .for_each(|statement| crate::go_traversal::Walk::statement(&mut types, statement));
}

fn each_type_in_expression(value: &mut GoExpression, visit: &mut impl FnMut(&mut GoType)) {
    let mut statement =
        GoStatement::Expression(std::mem::replace(value, GoExpression::Boolean(false)));
    each_type_in_statements(std::slice::from_mut(&mut statement), visit);
    let GoStatement::Expression(taken) = statement else { unreachable!() };
    *value = taken;
}

/// What the program declares that typing its code needs.
struct Program {
    candidates: Vec<GoType>,
    /// Top-level functions, by name, with their types.
    functions: FxHashMap<String, GoType>,
    variables: FxHashMap<String, GoType>,
    /// Named types, by name, with the types they stand for.
    named: FxHashMap<String, GoType>,
    generic: FxHashMap<String, (String, GoType)>,
}

impl Program {
    fn new(
        declarations: &[GoDeclaration],
        type_declarations: &[GoDeclaration],
        candidates: Vec<GoType>,
    ) -> Program {
        let mut program = Program {
            candidates,
            functions: FxHashMap::default(),
            variables: FxHashMap::default(),
            named: FxHashMap::default(),
            generic: FxHashMap::default(),
        };
        for declaration in type_declarations.iter().chain(declarations) {
            match declaration {
                GoDeclaration::Type { name, type_, .. }
                | GoDeclaration::Alias { name, type_, .. } => {
                    program.named.insert(name.clone(), type_.clone());
                }
                GoDeclaration::GenericType { name, parameter, type_ } => {
                    program.generic.insert(name.clone(), (parameter.clone(), type_.clone()));
                }
                GoDeclaration::Function { name, parameters, result, .. } => {
                    let type_ = GoType::Function {
                        parameters: parameters.iter().map(|(_, type_)| type_.clone()).collect(),
                        result: result.clone().map(Box::new),
                    };
                    program.functions.insert(name.clone(), type_);
                }
                GoDeclaration::Variable { name, type_, value, .. } => {
                    let type_ = type_.clone().or_else(|| match value.unattributed() {
                        GoExpression::Composite { type_, .. }
                        | GoExpression::Conversion { type_, .. } => Some(type_.clone()),
                        GoExpression::Function { parameters, result, .. } => {
                            Some(GoType::Function {
                                parameters: parameters
                                    .iter()
                                    .map(|(_, type_)| type_.clone())
                                    .collect(),
                                result: result.clone().map(Box::new),
                            })
                        }
                        _ => None,
                    });
                    if let Some(type_) = type_ {
                        program.variables.insert(name.clone(), type_);
                    }
                }
                _ => {}
            }
        }
        for declaration in declarations {
            let GoDeclaration::Variable { name, type_: None, value, .. } = declaration else {
                continue;
            };
            let GoExpression::Call { function, .. } = value.unattributed() else { continue };
            let GoExpression::Identifier(function) = function.unattributed() else { continue };
            if let Some(GoType::Function { result: Some(result), .. }) =
                program.functions.get(function)
            {
                let result = result.as_ref().clone();
                program.variables.insert(name.clone(), result);
            }
        }
        program
    }

    /// The type a named or generic type stands for, through names.
    fn underlying(&self, type_: &GoType) -> GoType {
        let mut current = type_.clone();
        for _ in 0..16 {
            current = match &current {
                GoType::Named(name) => match self.named.get(name) {
                    Some(type_) => type_.clone(),
                    None => return current,
                },
                GoType::Generic { name, arguments } => match self.generic.get(name) {
                    Some((parameter, type_)) if arguments.len() == 1 => {
                        substitute(type_, parameter, &arguments[0])
                    }
                    _ => return current,
                },
                _ => return current,
            };
        }
        current
    }

    fn candidate(&self, type_: &GoType) -> Option<usize> {
        let underlying = self.underlying(type_);
        self.candidates.iter().position(|candidate| *candidate == underlying)
    }

    fn field(&self, holder: &GoType, field: &str) -> Option<GoType> {
        let holder = match self.underlying(holder) {
            GoType::Pointer(inner) => self.underlying(&inner),
            holder => holder,
        };
        let GoType::Struct(fields) = holder else { return None };
        fields.iter().find(|candidate| candidate.name == field).map(|field| field.type_.clone())
    }

    fn element(&self, holder: &GoType) -> Option<GoType> {
        match holder {
            GoType::Slice(element) => Some(*element.clone()),
            GoType::Generic { arguments, .. } if arguments.len() == 1 => Some(arguments[0].clone()),
            GoType::Pointer(inner) => match inner.as_ref() {
                GoType::Generic { arguments, .. } if arguments.len() == 1 => {
                    Some(arguments[0].clone())
                }
                _ => None,
            },
            GoType::Named(_) => match self.underlying(holder) {
                GoType::Slice(element) => Some(*element),
                _ => None,
            },
            _ => None,
        }
    }
}

fn substitute(type_: &GoType, parameter: &str, argument: &GoType) -> GoType {
    let mut type_ = type_.clone();
    each_nested_type(&mut type_, &mut |nested| {
        if matches!(nested, GoType::Named(name) if name == parameter) {
            *nested = argument.clone();
        }
    });
    type_
}

/// The type of a value as far as the program tells.
#[derive(Clone)]
enum Ty {
    Known(GoType),
    /// A foreign holder of values of the type, such as an `IORef`.
    Holder(Box<Ty>),
    /// A foreign function that returns a value of the type, such as an `IORef`'s `Load`.
    Returning(Box<Ty>),
    /// A value of a type the code does not tell: a foreign function's result, told by the
    /// candidates it may hold and those of them it may hold as `Either`-building functions.
    Unknown {
        all: FxHashSet<usize>,
        either: FxHashSet<usize>,
        told: bool,
    },
}

impl Ty {
    fn unknown() -> Ty {
        Ty::Unknown { all: FxHashSet::default(), either: FxHashSet::default(), told: false }
    }

    fn foreign(all: FxHashSet<usize>, either: FxHashSet<usize>) -> Ty {
        Ty::Unknown { all, either, told: true }
    }
}

struct Typer<'t> {
    program: &'t Program,
    lowered: &'t [bool],
    foreign: &'t ForeignPackages,
    rewrite: bool,
    scopes: Vec<FxHashMap<String, Ty>>,
    removed: FxHashSet<usize>,
    names: FxHashSet<String>,
    contents: FxHashMap<String, FxHashSet<usize>>,
}

impl<'t> Typer<'t> {
    fn new(
        program: &'t Program,
        lowered: &'t [bool],
        foreign: &'t ForeignPackages,
        rewrite: bool,
    ) -> Typer<'t> {
        Typer {
            program,
            lowered,
            foreign,
            rewrite,
            scopes: vec![],
            removed: FxHashSet::default(),
            names: FxHashSet::default(),
            contents: FxHashMap::default(),
        }
    }

    fn lowered(&self, type_: &GoType) -> Option<usize> {
        self.program
            .candidate(type_)
            .filter(|index| self.lowered[*index] && !self.removed.contains(index))
    }

    fn remove(&mut self, index: usize) {
        if self.lowered[index] {
            self.removed.insert(index);
        }
    }

    /// The candidates the type holds anywhere in it.
    fn contained(&mut self, type_: &GoType) -> FxHashSet<usize> {
        let mut found = FxHashSet::default();
        self.collect_contained(type_, &mut found, &mut FxHashSet::default());
        found
    }

    fn collect_contained(
        &mut self,
        type_: &GoType,
        found: &mut FxHashSet<usize>,
        visiting: &mut FxHashSet<String>,
    ) {
        if let Some(index) = self.program.candidates.iter().position(|candidate| candidate == type_)
        {
            found.insert(index);
        }
        match type_ {
            GoType::Named(name) => {
                if let Some(known) = self.contents.get(name) {
                    found.extend(known.iter().copied());
                    return;
                }
                if !visiting.insert(name.clone()) {
                    return;
                }
                let mut own = FxHashSet::default();
                if let Some(underlying) = self.program.named.get(name).cloned() {
                    self.collect_contained(&underlying, &mut own, visiting);
                }
                found.extend(own.iter().copied());
                self.contents.insert(name.clone(), own);
            }
            GoType::Function { parameters, result } => {
                for parameter in parameters {
                    self.collect_contained(parameter, found, visiting);
                }
                if let Some(result) = result {
                    self.collect_contained(result, found, visiting);
                }
            }
            GoType::Slice(element) | GoType::Pointer(element) => {
                self.collect_contained(element, found, visiting)
            }
            GoType::Generic { name, arguments } => {
                for argument in arguments {
                    self.collect_contained(argument, found, visiting);
                }
                if self.program.generic.contains_key(name) {
                    let underlying = self.program.underlying(type_);
                    if underlying != *type_ {
                        self.collect_contained(&underlying, found, visiting);
                    }
                }
            }
            GoType::Struct(fields) => {
                for field in fields {
                    self.collect_contained(&field.type_, found, visiting);
                }
            }
            GoType::Results(results) => {
                for result in results {
                    self.collect_contained(result, found, visiting);
                }
            }
            _ => {}
        }
    }

    /// What a field or an element of a value of a type the program does not declare is: a
    /// foreign type's, which holds no more of the program's than its type does.
    fn opaque(&mut self, type_: &GoType) -> Ty {
        let foreign = match self.program.underlying(type_) {
            GoType::Pointer(inner) => is_foreign_type(&inner),
            underlying => is_foreign_type(&underlying),
        };
        match foreign {
            true => {
                let all = self.contained(type_);
                Ty::foreign(all, FxHashSet::default())
            }
            false => Ty::unknown(),
        }
    }

    fn ty_contained(&mut self, ty: &Ty) -> FxHashSet<usize> {
        match ty {
            Ty::Known(type_) => self.contained(type_),
            Ty::Holder(inner) | Ty::Returning(inner) => self.ty_contained(inner),
            Ty::Unknown { all, .. } => all.clone(),
        }
    }

    /// A value of the program's types that a foreign value holds, its parts unknown.
    fn held(&mut self, ty: &Ty) -> Ty {
        let all = self.ty_contained(ty);
        Ty::foreign(all, FxHashSet::default())
    }

    fn declaration(&mut self, declaration: &mut GoDeclaration) {
        self.names = declaration.all_names();
        self.scopes = vec![FxHashMap::default()];
        match declaration {
            GoDeclaration::Function { parameters, body, .. } => {
                for (parameter, type_) in parameters.iter() {
                    self.bind(parameter, Ty::Known(type_.clone()));
                }
                self.statements(body);
            }
            GoDeclaration::Variable { value, .. } | GoDeclaration::Constant { value, .. } => {
                self.expression(value, false);
            }
            _ => {}
        }
        self.scopes.clear();
    }

    fn bind(&mut self, name: &str, ty: Ty) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), ty);
        }
    }

    fn local(&self, name: &str) -> Option<Ty> {
        self.scopes.iter().rev().find_map(|scope| scope.get(name)).cloned()
    }

    fn block(&mut self, body: &mut [GoStatement]) {
        self.scopes.push(FxHashMap::default());
        self.statements(body);
        self.scopes.pop();
    }

    fn statements(&mut self, body: &mut [GoStatement]) {
        for statement in body.iter_mut() {
            self.statement(statement);
        }
    }

    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values } => {
                let types: Vec<Ty> =
                    values.iter_mut().map(|value| self.expression(value, false)).collect();
                match types.as_slice() {
                    [Ty::Known(GoType::Results(results))] if names.len() == results.len() => {
                        for (name, type_) in names.iter().zip(results) {
                            self.bind(name, Ty::Known(type_.clone()));
                        }
                    }
                    [single] if names.len() > 1 => {
                        let spread = match single {
                            Ty::Unknown { .. } => single.clone(),
                            _ => Ty::unknown(),
                        };
                        for name in names.iter() {
                            self.bind(name, spread.clone());
                        }
                    }
                    _ => {
                        for (name, ty) in names.iter().zip(types) {
                            self.bind(name, ty);
                        }
                    }
                }
            }
            GoStatement::Variable { name, type_, value } => {
                if let Some(value) = value {
                    self.expression(value, false);
                }
                let name = name.clone();
                self.bind(&name, Ty::Known(type_.clone()));
            }
            GoStatement::Assign { targets, values } => {
                for target in targets.iter_mut() {
                    self.expression(target, false);
                }
                for value in values.iter_mut() {
                    self.expression(value, false);
                }
            }
            GoStatement::Expression(value) | GoStatement::Defer(value) => {
                self.discarded(value);
            }
            GoStatement::Return(value) => {
                if let Some(value) = value {
                    self.expression(value, false);
                }
            }
            GoStatement::If { condition, then, otherwise } => {
                self.expression(condition, false);
                self.block(then);
                self.block(otherwise);
            }
            GoStatement::Switch { value, cases, default } => {
                if let Some(value) = value {
                    self.expression(value, false);
                }
                for case in cases.iter_mut() {
                    for value in case.values.iter_mut() {
                        self.expression(value, false);
                    }
                    self.block(&mut case.body);
                }
                if let Some(default) = default {
                    for value in default.covers.iter_mut() {
                        self.expression(value, false);
                    }
                    self.block(&mut default.body);
                }
            }
            GoStatement::IfAssert { name, value, type_, then } => {
                self.expression(value, false);
                self.scopes.push(FxHashMap::default());
                let name = name.clone();
                self.bind(&name, Ty::Known(type_.clone()));
                self.statements(then);
                self.scopes.pop();
            }
            GoStatement::Range { index, element, iterable, body } => {
                let iterated = self.expression(iterable, false);
                let element_ty = match &iterated {
                    Ty::Known(type_) => match self.program.element(type_) {
                        Some(element) => Ty::Known(element),
                        None => Ty::unknown(),
                    },
                    Ty::Holder(inner) => *inner.clone(),
                    returning @ Ty::Returning(_) => self.held(returning),
                    unknown @ Ty::Unknown { .. } => unknown.clone(),
                };
                self.scopes.push(FxHashMap::default());
                if let Some(index) = index {
                    let index = index.clone();
                    self.bind(&index, Ty::Known(GoType::Int));
                }
                let element = element.clone();
                self.bind(&element, element_ty);
                self.statements(body);
                self.scopes.pop();
            }
            GoStatement::Counting { variable, start, end, body } => {
                self.expression(start, false);
                self.expression(end, false);
                self.scopes.push(FxHashMap::default());
                let variable = variable.clone();
                self.bind(&variable, Ty::Known(GoType::Int));
                self.statements(body);
                self.scopes.pop();
            }
            GoStatement::CountingDown { variable, start, body } => {
                self.expression(start, false);
                self.scopes.push(FxHashMap::default());
                let variable = variable.clone();
                self.bind(&variable, Ty::Known(GoType::Int));
                self.statements(body);
                self.scopes.pop();
            }
            GoStatement::Loop(body) | GoStatement::LabeledLoop { body, .. } => self.block(body),
            GoStatement::Continue
            | GoStatement::Break
            | GoStatement::BreakTo(_)
            | GoStatement::Line(_) => {}
        }
    }

    /// A value whose result nothing keeps: a foreign call's result may build `Either`s here.
    fn discarded(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Attributed { value, .. } => self.discarded(value),
            GoExpression::Call { function, arguments } if is_foreign(function) => {
                self.foreign_call(function, arguments);
            }
            value => {
                self.expression(value, false);
            }
        }
    }

    fn expression(&mut self, value: &mut GoExpression, foreign_argument: bool) -> Ty {
        match value {
            GoExpression::Attributed { value, .. } => self.expression(value, foreign_argument),
            GoExpression::Identifier(name) => {
                if let Some(ty) = self.local(name) {
                    return ty;
                }
                if let Some(type_) = self.program.variables.get(name.as_str()) {
                    return Ty::Known(type_.clone());
                }
                let Some(type_) = self.program.functions.get(name.as_str()).cloned() else {
                    return Ty::unknown();
                };
                if let Some(index) = self.lowered(&type_)
                    && !foreign_argument
                    && self.rewrite
                {
                    let function = name.clone();
                    *value = self.function_wrapper(&function, index);
                }
                Ty::Known(type_)
            }
            GoExpression::Call { function, arguments } => self.call(function, arguments),
            GoExpression::Function { parameters, result, body } => {
                let type_ = GoType::Function {
                    parameters: parameters.iter().map(|(_, type_)| type_.clone()).collect(),
                    result: result.clone().map(Box::new),
                };
                self.scopes.push(FxHashMap::default());
                for (parameter, parameter_type) in parameters.iter() {
                    self.bind(parameter, Ty::Known(parameter_type.clone()));
                }
                self.statements(body);
                self.scopes.pop();
                if !foreign_argument
                    && self.rewrite
                    && let Some(index) = self.lowered(&type_)
                {
                    let literal = std::mem::replace(value, GoExpression::Boolean(false));
                    *value = self.marked(LITERAL_MARK, index, vec![literal]);
                }
                Ty::Known(type_)
            }
            GoExpression::Field { value: holder, name } => {
                let holder = self.expression(holder, false);
                if READING_METHODS.contains(&name.as_str()) {
                    match &holder {
                        Ty::Holder(inner) => return Ty::Returning(inner.clone()),
                        Ty::Known(type_)
                            if self.program.field(type_, name).is_none()
                                && let Some(element) = self.program.element(type_) =>
                        {
                            return Ty::Returning(Box::new(Ty::Known(element)));
                        }
                        _ => {}
                    }
                }
                match holder {
                    Ty::Known(type_) => match self.program.field(&type_, name) {
                        Some(field) => Ty::Known(field),
                        None => self.opaque(&type_),
                    },
                    held @ (Ty::Holder(_) | Ty::Returning(_)) => self.held(&held),
                    unknown @ Ty::Unknown { .. } => unknown,
                }
            }
            GoExpression::Index { value: holder, index } => {
                self.expression(index, false);
                match self.expression(holder, false) {
                    Ty::Known(type_) => match self.program.element(&type_) {
                        Some(element) => Ty::Known(element),
                        None => self.opaque(&type_),
                    },
                    Ty::Holder(inner) => *inner,
                    returning @ Ty::Returning(_) => self.held(&returning),
                    unknown @ Ty::Unknown { .. } => unknown,
                }
            }
            GoExpression::Composite { type_, fields } => {
                let type_ = type_.clone();
                for (_, field) in fields.iter_mut() {
                    self.expression(field, false);
                }
                Ty::Known(type_)
            }
            GoExpression::Conversion { type_, value }
            | GoExpression::TypeAssertion { value, type_ } => {
                let type_ = type_.clone();
                self.expression(value, false);
                Ty::Known(type_)
            }
            GoExpression::Type(type_) => Ty::Known(type_.clone()),
            GoExpression::Unary { operator, operand } => {
                let operand = self.expression(operand, false);
                match (*operator, operand) {
                    ("*", Ty::Known(GoType::Pointer(inner))) => Ty::Known(*inner),
                    _ => Ty::unknown(),
                }
            }
            GoExpression::Address(inner) => match self.expression(inner, false) {
                Ty::Known(type_) => Ty::Known(GoType::Pointer(Box::new(type_))),
                _ => Ty::unknown(),
            },
            GoExpression::Spread(inner) => self.expression(inner, foreign_argument),
            GoExpression::Binary { left, right, .. } => {
                self.expression(left, false);
                self.expression(right, false);
                Ty::unknown()
            }
            GoExpression::Instantiation { function, .. } => {
                self.expression(function, false);
                Ty::unknown()
            }
            GoExpression::Results(values) => {
                for value in values.iter_mut() {
                    self.expression(value, false);
                }
                Ty::unknown()
            }
            GoExpression::Qualified { .. }
            | GoExpression::Integer(_)
            | GoExpression::Float(_)
            | GoExpression::String(_)
            | GoExpression::Utf16(_)
            | GoExpression::Rune(_)
            | GoExpression::Boolean(_) => Ty::unknown(),
        }
    }

    fn call(&mut self, function: &mut Box<GoExpression>, arguments: &mut Vec<GoExpression>) -> Ty {
        if is_foreign(function) {
            let (result, either) = self.foreign_call(function, arguments);
            if !either.is_empty() {
                let held = self.ty_contained(&result);
                let held_either = match &result {
                    Ty::Unknown { either, .. } => either.clone(),
                    _ => FxHashSet::default(),
                };
                for index in either {
                    if held.contains(&index) || held_either.contains(&index) {
                        self.remove(index);
                    }
                }
            }
            return result;
        }
        if let GoExpression::Identifier(name) = function.unattributed()
            && self.local(name).is_none()
        {
            let name = name.clone();
            let types: Vec<Ty> =
                arguments.iter_mut().map(|argument| self.expression(argument, false)).collect();
            if let Some(GoType::Function { result, .. }) = self.program.functions.get(&name) {
                return match result {
                    Some(result) => Ty::Known(*result.clone()),
                    None => Ty::unknown(),
                };
            }
            if let Some(type_) = self.program.variables.get(&name).cloned() {
                return self.dynamic_call(function, arguments, Ty::Known(type_));
            }
            return match (name.as_str(), types.as_slice()) {
                ("make", [Ty::Known(type_), ..]) => Ty::Known(type_.clone()),
                ("new", [Ty::Known(type_)]) => Ty::Known(GoType::Pointer(Box::new(type_.clone()))),
                ("append", [first, ..]) => first.clone(),
                _ if BUILTINS.contains(&name.as_str()) => Ty::unknown(),
                _ => {
                    let mut all = FxHashSet::default();
                    for ty in &types {
                        all.extend(self.ty_contained(ty));
                    }
                    Ty::foreign(all, FxHashSet::default())
                }
            };
        }
        let callee = self.expression(function, false);
        for argument in arguments.iter_mut() {
            self.expression(argument, false);
        }
        self.dynamic_call(function, arguments, callee)
    }

    /// The call of a function value, marked when its type returns two results.
    fn dynamic_call(
        &mut self,
        function: &mut Box<GoExpression>,
        arguments: &mut Vec<GoExpression>,
        callee: Ty,
    ) -> Ty {
        match callee {
            Ty::Known(type_) => {
                let underlying = self.program.underlying(&type_);
                if let Some(index) = self.lowered(&type_)
                    && self.rewrite
                {
                    let callee = std::mem::replace(function.as_mut(), GoExpression::Boolean(false));
                    let mut marked = vec![callee];
                    marked.append(arguments);
                    let GoExpression::Call { function: head, arguments: rest } =
                        self.marked(CALL_MARK, index, marked)
                    else {
                        unreachable!("invariant violated: a mark is a call")
                    };
                    *function = head;
                    *arguments = rest;
                }
                match underlying {
                    GoType::Function { result: Some(result), .. } => Ty::Known(*result),
                    _ => Ty::unknown(),
                }
            }
            Ty::Returning(result) => *result,
            Ty::Holder(_) => Ty::unknown(),
            Ty::Unknown { all, either, told } => {
                let count = arguments.len();
                let removed: Vec<usize> = (0..self.program.candidates.len())
                    .filter(|index| {
                        (all.contains(index) || !told)
                            && matches!(&self.program.candidates[*index],
                                GoType::Function { parameters, .. } if parameters.len() == count)
                    })
                    .collect();
                for index in removed {
                    self.remove(index);
                }
                Ty::Unknown { all, either, told }
            }
        }
    }

    /// A call of a foreign function, with the candidates passed to it as `Either`-building
    /// functions.
    fn foreign_call(
        &mut self,
        function: &mut Box<GoExpression>,
        arguments: &mut [GoExpression],
    ) -> (Ty, FxHashSet<usize>) {
        let (package, name, instantiated) = match function.unattributed() {
            GoExpression::Qualified { package, name } => (package.clone(), name.clone(), vec![]),
            GoExpression::Instantiation { function, arguments } => match function.unattributed() {
                GoExpression::Qualified { package, name } => {
                    (package.clone(), name.clone(), arguments.clone())
                }
                _ => unreachable!("invariant violated: a foreign instantiation"),
            },
            _ => unreachable!("invariant violated: a foreign call"),
        };
        let signature = self.foreign.signature(&package, &name).cloned();
        let shape_at = |position: usize| match &signature {
            Some(signature) => {
                signature.parameters.get(position).cloned().unwrap_or(ForeignShape::Other)
            }
            None => ForeignShape::Other,
        };
        let mut all: FxHashSet<usize> = FxHashSet::default();
        let mut either: FxHashSet<usize> = FxHashSet::default();
        let mut types = Vec::with_capacity(arguments.len());
        for type_ in &instantiated {
            all.extend(self.contained(type_));
        }
        for (position, argument) in arguments.iter_mut().enumerate() {
            let shape = shape_at(position);
            let bare = matches!(shape, ForeignShape::Parameter(_));
            let literal = matches!(argument.unattributed(), GoExpression::Function { .. });
            let ty = self.expression(argument, !bare);
            if let Ty::Known(type_) = &ty
                && let Some(index) = self.lowered(type_)
                && !bare
            {
                if literal || self.is_top_level_function(argument) {
                    either.insert(index);
                } else if is_plain(argument) {
                    either.insert(index);
                    if self.rewrite {
                        let value = std::mem::replace(argument, GoExpression::Boolean(false));
                        *argument = self.converting_wrapper(value, index);
                    }
                } else {
                    self.remove(index);
                }
            }
            if let Ty::Known(type_) = &ty
                && shape == ForeignShape::Other
                && self.lowered(type_).is_none()
            {
                for index in self.contained(type_) {
                    self.remove(index);
                }
            }
            all.extend(self.ty_contained(&ty));
            if let Ty::Unknown { either: held, .. } = &ty {
                either.extend(held.iter().copied());
            }
            types.push((shape, ty));
        }
        let unknown = Ty::foreign(all.clone(), either.clone());
        let result = match signature.as_ref().map(|signature| &signature.result) {
            Some(ForeignShape::Parameter(parameter)) => {
                let bare = types
                    .iter()
                    .find(|(shape, _)| *shape == ForeignShape::Parameter(parameter.clone()));
                let held = types
                    .iter()
                    .find(|(shape, _)| *shape == ForeignShape::Holder(parameter.clone()));
                match (bare, held) {
                    (Some((_, ty)), _) => ty.clone(),
                    (None, Some((_, Ty::Known(type_)))) => match self.program.element(type_) {
                        Some(element) => Ty::Known(element),
                        None => unknown,
                    },
                    (None, Some((_, Ty::Holder(inner)))) => *inner.clone(),
                    _ => unknown,
                }
            }
            Some(ForeignShape::Holder(parameter)) => {
                match types
                    .iter()
                    .find(|(shape, _)| *shape == ForeignShape::Parameter(parameter.clone()))
                {
                    Some((_, ty)) => Ty::Holder(Box::new(ty.clone())),
                    None => unknown,
                }
            }
            _ => unknown,
        };
        (result, either)
    }

    fn is_top_level_function(&self, value: &GoExpression) -> bool {
        match value.unattributed() {
            GoExpression::Identifier(name) => {
                self.local(name).is_none() && self.program.functions.contains_key(name)
            }
            _ => false,
        }
    }

    fn marked(&mut self, mark: &str, index: usize, arguments: Vec<GoExpression>) -> GoExpression {
        let either = either_of(&self.program.candidates[index]);
        GoExpression::Call {
            function: Box::new(GoExpression::Identifier(format!("{mark}{either}"))),
            arguments,
        }
    }

    fn parameters_of(&mut self, index: usize) -> (Vec<(String, GoType)>, GoType) {
        let GoType::Function { parameters, result: Some(result) } =
            self.program.candidates[index].clone()
        else {
            unreachable!("invariant violated: a candidate returns an Either")
        };
        let named = parameters
            .into_iter()
            .map(|type_| (super::super::inlining::fresh("x", &mut self.names), type_))
            .collect();
        (named, *result)
    }

    /// `func(p) E { return EFromResults(value(p)) }`, for a foreign parameter of a function type.
    fn converting_wrapper(&mut self, value: GoExpression, index: usize) -> GoExpression {
        let (parameters, result) = self.parameters_of(index);
        let mut marked = vec![value];
        marked.extend(parameters.iter().map(|(name, _)| GoExpression::Identifier(name.clone())));
        let call = self.marked(CALL_MARK, index, marked);
        GoExpression::Function {
            parameters,
            result: Some(result),
            body: vec![GoStatement::Return(Some(call))],
        }
    }

    /// `func(p) E { return f(p) }` returning two results, for a top-level function passed as a
    /// value of a lowered type.
    fn function_wrapper(&mut self, function: &str, index: usize) -> GoExpression {
        let (parameters, result) = self.parameters_of(index);
        let arguments =
            parameters.iter().map(|(name, _)| GoExpression::Identifier(name.clone())).collect();
        let literal = GoExpression::Function {
            parameters,
            result: Some(result),
            body: vec![GoStatement::Return(Some(GoExpression::Call {
                function: Box::new(GoExpression::Identifier(function.to_string())),
                arguments,
            }))],
        };
        self.marked(LITERAL_MARK, index, vec![literal])
    }
}

fn is_foreign(function: &GoExpression) -> bool {
    match function.unattributed() {
        GoExpression::Qualified { .. } => true,
        GoExpression::Instantiation { function, .. } => {
            matches!(function.unattributed(), GoExpression::Qualified { .. })
        }
        _ => false,
    }
}

/// A type of another package, which the program's code does not declare.
fn is_foreign_type(type_: &GoType) -> bool {
    match type_ {
        GoType::Named(name) | GoType::Generic { name, .. } => name.contains('.'),
        _ => false,
    }
}

/// A value that reading again reads the same: a local, or a field of one.
fn is_plain(value: &GoExpression) -> bool {
    match value.unattributed() {
        GoExpression::Identifier(_) => true,
        GoExpression::Field { value, .. } => is_plain(value),
        _ => false,
    }
}

/// `f(x)` for `§call:E(f, x)`, and the literal of `§literal:E(literal)`. A literal returning two
/// results that only passes its parameters on to a top-level function of its own type is that
/// function.
pub(super) fn unmark(declarations: &mut [GoDeclaration]) {
    let functions: FxHashMap<String, (Vec<GoType>, Option<GoType>)> = declarations
        .iter()
        .filter_map(|declaration| match declaration {
            GoDeclaration::Function { name, parameters, result, .. } => Some((
                name.clone(),
                (parameters.iter().map(|(_, type_)| type_.clone()).collect(), result.clone()),
            )),
            _ => None,
        })
        .collect();
    for declaration in declarations.iter_mut() {
        let locals = declaration.declared_names().locals;
        crate::go_traversal::each_expression_in_declaration(declaration, |expression| {
            if let Some(function) = forwarded_function(expression, &functions, &locals) {
                *expression = GoExpression::Identifier(function);
                return;
            }
            let GoExpression::Call { function, arguments } = expression else { return };
            let GoExpression::Identifier(head) = function.unattributed() else { return };
            if head.starts_with(CALL_MARK) && !arguments.is_empty() {
                let callee = arguments.remove(0);
                **function = callee;
            } else if head.starts_with(LITERAL_MARK) && arguments.len() == 1 {
                *expression = arguments.remove(0);
            }
        });
    }
}

/// The top-level function of the literal's own type that the literal, returning two results,
/// only passes its parameters on to.
fn forwarded_function(
    literal: &GoExpression,
    functions: &FxHashMap<String, (Vec<GoType>, Option<GoType>)>,
    locals: &FxHashSet<String>,
) -> Option<String> {
    let GoExpression::Function { parameters, result: Some(result @ GoType::Results(_)), body } =
        literal
    else {
        return None;
    };
    let mut statements = body.iter().filter(|statement| !matches!(statement, GoStatement::Line(_)));
    let (Some(GoStatement::Return(Some(returned))), None) = (statements.next(), statements.next())
    else {
        return None;
    };
    let GoExpression::Call { function, arguments } = returned.unattributed() else { return None };
    let GoExpression::Identifier(name) = function.unattributed() else { return None };
    let (types, own_result) = functions.get(name)?;
    let passed_on = arguments.len() == parameters.len()
        && arguments.iter().zip(parameters).all(|(argument, (parameter, _))| {
            matches!(argument.unattributed(), GoExpression::Identifier(passed) if passed == parameter)
        });
    let same_type = types.len() == parameters.len()
        && types.iter().zip(parameters).all(|(type_, (_, parameter))| type_ == parameter)
        && own_result.as_ref() == Some(result);
    (passed_on && same_type && !locals.contains(name)).then(|| name.clone())
}
