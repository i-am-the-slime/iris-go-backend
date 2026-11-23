//! Closed function types as tagged cells.
//!
//! A Go closure that outlives the call creating it is allocated on its own,
//! one call of Go's allocator per closure. When every value of a function
//! type comes from a lambda, a known function or a partial application in
//! this program, and no value of it crosses into foreign code or a coercion,
//! the type has a closed set of shapes, its lambda set. Each shape becomes a
//! tag of one struct that holds what the lambda captures, and calling a value
//! becomes a call of one function that switches on the tag and runs that
//! lambda's body (Reynolds' defunctionalisation; Roc's lambda sets, Brandon et
//! al., PLDI 2023; MLton's closure conversion). The cells are ordinary data
//! from then on: a loop that links them, as
//! `buildThunks n acc = buildThunks (n - 1) (defer \_ -> force acc + 1)` does,
//! takes them from chunks (see `chunks.rs`).
//!
//! A cell allocated on its own costs what a Go closure does; the gain is in
//! taking cells from chunks, which `chunks.rs` does for a cell that a loop
//! links to the previous value of its variable. So only types linked through
//! a loop change representation: a function passes, in a call to itself in
//! tail position, a new value that captures the parameter it replaces. Other
//! closures stay Go functions, which Go keeps on the stack where they do not
//! escape and inlines where they are known. A lambda set is at most
//! `MOST_TAGS` shapes, which bounds the function that runs them.
//!
//! The function that runs the cells reads like the PureScript it replaces:
//! it is named after the newtype's eliminator, as `force` for
//! `newtype Lazy a = Lazy (Unit -> a)` with `force (Lazy f) = f unit`, and the
//! struct after the newtype. A type without a newtype is named after its
//! arguments and result, as `IntToString`.
//!
//! Evaluation is unchanged: a lambda's body still runs only when the value is
//! called, captures are the values the lambda closes over, and a partial
//! application evaluates its arguments where it is written, as Go does.

use files::FileId;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::{SmolStr, format_smolstr};

use super::packages::Spelling;
use super::{ConstructorLayout, DataKind, DataLayout, Emitter, identifier, layout, uses_local};
use crate::arity::Arities;
use crate::context::Context;
use crate::error::GoResult;
use crate::foreign::Foreign;
use crate::lift::collect_binders;
use crate::monomorphic::traversal::{for_each_child, for_each_child_mut};
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Function, FunctionId, FunctionSpelling,
    Guard, Guarded, Local, LocalId, Pattern, PatternKind, Program,
};
use crate::monotype::{DataType, Failure, Monotype, MonotypeId, Monotypes};
use crate::naming::{capitalise, lower_first, numbered};
use crate::syntax::{GoDeclaration, GoExpression, GoType, StructField};

/// The most shapes one function type may have and still become cells.
const MOST_TAGS: usize = 8;

/// The cells of one closed function type.
pub(super) struct ClosureSet {
    /// What the struct is named after: the newtype, or the function type.
    pub name: String,
    /// The module the struct belongs to: that of the function running it.
    pub home: Option<FileId>,
    pub tags: Vec<ClosureTag>,
}

/// One shape of a closed function type: a lambda, or a known function
/// applied to some of its arguments.
pub(super) struct ClosureTag {
    /// The function the lambda is written in, or the known function.
    pub name: SmolStr,
    pub captures: Vec<Local>,
}

/// The function each newtype over a function type is eliminated with, as
/// `force` for `Lazy`, found before inlining removes it.
#[derive(Default)]
pub(crate) struct Eliminators {
    found: FxHashMap<MonotypeId, Eliminator>,
}

#[derive(Clone)]
struct Eliminator {
    name: SmolStr,
    origin: Option<FileId>,
    /// Where the newtype is among the parameters that are not unit.
    position: usize,
}

impl Eliminators {
    /// A function that matches one argument, of a newtype over a function
    /// type, and does nothing but call the function inside with its other
    /// arguments, or return it: `runRecordDraw ctx (RecordDraw run) = run ctx`.
    pub(crate) fn find(program: &Program, monotypes: &Monotypes) -> Eliminators {
        let mut eliminators = Eliminators::default();
        for function in &program.functions {
            let Some(wrapped) = eliminated(function, monotypes) else { continue };
            let parameters = &function.parameters;
            let monotype = parameters[wrapped].monotype;
            let position = parameters[..wrapped]
                .iter()
                .filter(|parameter| !matches!(monotypes.get(parameter.monotype), Monotype::Unit))
                .count();
            let found =
                Eliminator { name: function.name.clone(), origin: function.origin, position };
            // Specializations of one eliminator at types that share a
            // representation differ in their names' suffixes; the shortest
            // is chosen, so that every run picks the same.
            let known = eliminators.found.entry(monotype).or_insert_with(|| found.clone());
            if (found.name.len(), &found.name) < (known.name.len(), &known.name) {
                *known = found;
            }
        }
        eliminators
    }

    fn of(&self, monotype: MonotypeId) -> Option<&Eliminator> {
        self.found.get(&monotype)
    }
}

/// The parameter an eliminator unwraps: one matched by a `case` of its
/// parameters with one alternative of variables, whose body calls it with
/// the other parameters in order, or returns it when there are none.
fn eliminated(function: &Function, monotypes: &Monotypes) -> Option<usize> {
    let ExpressionKind::Case { scrutinees, alternatives } = &function.body.kind else {
        return None;
    };
    let [alternative] = &alternatives[..] else { return None };
    let Guarded::Unconditional(body) = &alternative.body else { return None };
    let parameters = &function.parameters;
    let position_of = |id: LocalId| parameters.iter().position(|parameter| parameter.id == id);
    let mut aliases: FxHashMap<LocalId, usize> = FxHashMap::default();
    for (scrutinee, pattern) in scrutinees.iter().zip(&alternative.patterns) {
        let ExpressionKind::Local(scrutinised) = scrutinee.kind else { return None };
        let position = position_of(scrutinised)?;
        match &pattern.kind {
            PatternKind::Variable(inner) => {
                aliases.insert(inner.id, position);
            }
            PatternKind::Wildcard => {}
            _ => return None,
        }
    }
    let parameter = |id: LocalId| aliases.get(&id).copied().or_else(|| position_of(id));
    let (wrapped, arguments) = match &body.kind {
        ExpressionKind::Local(id) => (parameter(*id)?, &[][..]),
        ExpressionKind::Apply { function, arguments } => {
            let ExpressionKind::Local(called) = function.kind else { return None };
            (parameter(called)?, &arguments[..])
        }
        _ => return None,
    };
    let unwrapped = aliases.values().any(|&position| position == wrapped);
    if !unwrapped || monotypes.function_newtype(parameters[wrapped].monotype).is_none() {
        return None;
    }
    let mut others = (0..parameters.len()).filter(|&position| position != wrapped);
    let in_order = arguments.iter().all(|argument| match argument.kind {
        ExpressionKind::Local(id) => parameter(id).is_some() && parameter(id) == others.next(),
        _ => is_unit_value(argument),
    });
    (in_order && others.next().is_none()).then_some(wrapped)
}

/// An operand that does no work, so it may be computed in any order.
fn is_value(expression: &Expression) -> bool {
    is_unit_value(expression)
        || matches!(
            expression.kind,
            ExpressionKind::Local(_) | ExpressionKind::Literal(_) | ExpressionKind::Function(_)
        )
}

fn is_unit_value(expression: &Expression) -> bool {
    matches!(
        expression.kind,
        ExpressionKind::Unit | ExpressionKind::Foreign { foreign: Foreign::Unit, .. }
    )
}

/// Turns the values of every linked, closed function type into cells, and
/// adds the function that runs each type's cells to the program.
pub(super) fn defunctionalize<Q>(
    program: &mut Program,
    monotypes: &mut Monotypes,
    queries: &Q,
    arities: &Arities,
    eliminators: &Eliminators,
) -> GoResult<FxHashMap<MonotypeId, ClosureSet>>
where
    Q: checking::ExternalQueries,
{
    let mut types = Types { monotypes, context: Context::new(queries), arities };
    let mut analysis = Analysis {
        types: &mut types,
        program,
        uses: Uses::default(),
        escaped: FxHashSet::default(),
        highest_local: 0,
        current: FunctionId(0),
    };
    for (index, function) in program.functions.iter().enumerate() {
        analysis.current = FunctionId(index as u32);
        for parameter in &function.parameters {
            analysis.bind(parameter);
        }
        analysis.expression(&function.body)?;
        analysis.tail_calls(&function.parameters, &function.body);
    }
    analysis.open_arities_reaching_inside();
    let Analysis { uses, highest_local, .. } = analysis;
    let closed = closed_types(&uses);
    if std::env::var_os("IRIS_GO_CLOSURE_STATISTICS").is_some() {
        report(&uses, &closed, types.monotypes);
    }
    if closed.is_empty() {
        return Ok(FxHashMap::default());
    }
    let mut touched: Vec<FunctionId> =
        closed.iter().flat_map(|monotype| uses.touching[monotype].iter().copied()).collect();
    touched.sort();
    touched.dedup();
    types.rewrite(program, closed, &touched, eliminators, highest_local)
}

/// How the program creates a value of a function type.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Creation {
    Lambda(LocalId),
    /// A known function, applied to this many of its arguments.
    Known(FunctionId, usize),
}

/// What the program does with the values of each function type.
#[derive(Default)]
struct Uses {
    creations: FxHashMap<MonotypeId, FxHashSet<Creation>>,
    /// The types whose new values a loop links to their previous ones.
    linked: FxHashSet<MonotypeId>,
    /// The types that stay Go functions, with the reason.
    open: FxHashMap<MonotypeId, &'static str>,
    /// The functions that create or call values of each type, in order.
    touching: FxHashMap<MonotypeId, Vec<FunctionId>>,
}

/// The closed, linked function types with few enough shapes, in the order of
/// their monotypes, so that names come out the same on every run.
fn closed_types(uses: &Uses) -> Vec<MonotypeId> {
    let mut closed: Vec<MonotypeId> = uses
        .creations
        .iter()
        .filter(|&(monotype, creations)| {
            !uses.open.contains_key(monotype)
                && uses.linked.contains(monotype)
                && creations.len() <= MOST_TAGS
        })
        .map(|(&monotype, _)| monotype)
        .collect();
    closed.sort();
    closed
}

/// What the pass asks of types: their arities, as the emitter chooses them,
/// what data holds, and names.
struct Types<'a, 'q, Q> {
    monotypes: &'a mut Monotypes,
    context: Context<'q, Q>,
    arities: &'a Arities,
}

impl<Q> Types<'_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    fn is_function(&self, monotype: MonotypeId) -> bool {
        self.monotypes.function_parts(monotype).is_some()
    }

    fn is_unit(&self, monotype: MonotypeId) -> bool {
        matches!(self.monotypes.get(monotype), Monotype::Unit)
    }

    fn canonical(&mut self, monotype: MonotypeId) -> MonotypeId {
        self.monotypes.without_causes(monotype)
    }

    /// How many arguments a value of a function type takes at once.
    fn arity(&self, monotype: MonotypeId) -> usize {
        if self.is_function(monotype) { self.arities.of(monotype) } else { 1 }
    }

    /// The arguments a value takes at once, and what it returns.
    fn leading_arrows(&self, monotype: MonotypeId) -> (Vec<MonotypeId>, MonotypeId) {
        let mut arguments = vec![];
        let mut result = monotype;
        for _ in 0..self.arity(monotype) {
            let Some((argument, rest)) = self.monotypes.function_parts(result) else { break };
            arguments.push(argument);
            result = rest;
        }
        (arguments, result)
    }

    /// The types of every constructor's fields.
    fn fields(&mut self, data: &DataType) -> GoResult<Vec<MonotypeId>> {
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(Failure::in_code_generation)?;
        Ok(constructors.iter().flat_map(|constructor| constructor.fields.iter().copied()).collect())
    }

    fn unfold(&mut self, data: &DataType) -> GoResult<MonotypeId> {
        self.monotypes.unfold_in(&mut self.context, data, "code generation")
    }

    /// `Lazy Int` is `LazyInt`, as the struct of a data type is named.
    fn data_type_name(&mut self, data: &DataType) -> GoResult<String> {
        let mut base = self.context.type_name(data.file_id, data.item)?.to_string();
        for &argument in data.arguments.iter() {
            self.context.type_suffix(argument, &mut base)?;
        }
        Ok(base)
    }

    /// `Int -> String` is `IntToString`, `Unit -> Int` is `ToInt`.
    fn function_type_name(&mut self, monotype: MonotypeId) -> GoResult<String> {
        let (arguments, result) = self.leading_arrows(monotype);
        let mut name = String::new();
        for argument in arguments {
            if !self.is_unit(argument) {
                name.push_str(&self.monotype_name(argument)?);
            }
        }
        name.push_str("To");
        name.push_str(&self.monotype_name(result)?);
        Ok(name)
    }

    /// A monotype's name within the name of a function type, as the struct
    /// of a data type or record would be named.
    fn monotype_name(&mut self, monotype: MonotypeId) -> GoResult<String> {
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Int => "Int".into(),
            Monotype::Int64 => "Int64".into(),
            Monotype::UInt64 => "UInt64".into(),
            Monotype::Number => "Number".into(),
            Monotype::Boolean => "Boolean".into(),
            Monotype::Char => "Char".into(),
            Monotype::String => "String".into(),
            Monotype::Unit => "Unit".into(),
            Monotype::Array(element) => format!("Array{}", self.monotype_name(element)?),
            Monotype::Effect(result) => format!("Effect{}", self.monotype_name(result)?),
            Monotype::Lazy(value) => format!("Lazy{}", self.monotype_name(value)?),
            Monotype::Record(fields) => {
                fields.iter().map(|field| crate::naming::go_field(&field.label)).collect()
            }
            Monotype::Data(data) | Monotype::Recursive(data) => self.data_type_name(&data)?,
            Monotype::Function(..) => "Function".into(),
            _ => "Value".into(),
        })
    }

    /// Rewrites the functions that create or call values of the closed
    /// types, and adds the function that runs each type's cells.
    fn rewrite(
        &mut self,
        program: &mut Program,
        closed: Vec<MonotypeId>,
        touched: &[FunctionId],
        eliminators: &Eliminators,
        highest_local: u32,
    ) -> GoResult<FxHashMap<MonotypeId, ClosureSet>> {
        let mut sets: FxHashMap<MonotypeId, Building> = FxHashMap::default();
        for (position, &monotype) in closed.iter().enumerate() {
            let dispatch = FunctionId((program.functions.len() + position) as u32);
            sets.insert(monotype, self.building(monotype, dispatch, eliminators));
        }
        let mut next_local = highest_local + 1;
        for &id in touched {
            self.rewrite_function(program, id, &mut sets, &mut next_local);
        }
        let mut finished = FxHashMap::default();
        for monotype in closed {
            let building = sets.remove(&monotype).expect("invariant violated: lambda set lost");
            let (function, set) =
                self.cells_function(monotype, building, eliminators, &mut next_local)?;
            program.functions.push(function);
            finished.insert(monotype, set);
        }
        Ok(finished)
    }

    /// A lambda set before its shapes are collected: the type of the
    /// function that will run its cells, which takes the cell where the
    /// eliminator takes the newtype, and no unit arguments.
    fn building(
        &mut self,
        monotype: MonotypeId,
        dispatch: FunctionId,
        eliminators: &Eliminators,
    ) -> Building {
        let (arguments, result) = self.leading_arrows(monotype);
        let mut passed: Vec<MonotypeId> =
            arguments.iter().copied().filter(|&argument| !self.is_unit(argument)).collect();
        let eliminator = eliminators.of(monotype);
        let closure_position = eliminator.map_or(0, |found| found.position).min(passed.len());
        passed.insert(closure_position, monotype);
        let type_ = passed
            .iter()
            .rev()
            .fold(result, |result, &argument| self.monotypes.function(argument, result));
        Building {
            dispatch,
            type_,
            closure_position,
            arguments,
            result,
            tags: vec![],
            known: FxHashMap::default(),
        }
    }

    fn rewrite_function(
        &mut self,
        program: &mut Program,
        id: FunctionId,
        sets: &mut FxHashMap<MonotypeId, Building>,
        next_local: &mut u32,
    ) {
        let index = id.0 as usize;
        let placeholder =
            Expression::new(ExpressionKind::Unit, program.functions[index].body.monotype);
        let mut body = std::mem::replace(&mut program.functions[index].body, placeholder);
        let function = &program.functions[index];
        let mut binders: FxHashMap<LocalId, Local> =
            function.parameters.iter().map(|parameter| (parameter.id, parameter.clone())).collect();
        collect_binders(&body, &mut binders);
        let mut rewriter = Rewriter {
            types: self,
            program,
            sets,
            binders,
            name: function.name.clone(),
            origin: function.origin,
            next_local,
        };
        rewriter.rewrite(&mut body);
        program.functions[index].body = body;
    }

    /// The function that runs the cells of a closed type, a case of one
    /// alternative per shape, named after the eliminator, or `run` and the
    /// type, and the description of the cells.
    fn cells_function(
        &mut self,
        monotype: MonotypeId,
        building: Building,
        eliminators: &Eliminators,
        next_local: &mut u32,
    ) -> GoResult<(Function, ClosureSet)> {
        let mut fresh =
            |name: SmolStr, monotype: MonotypeId| Local::fresh(next_local, name, monotype);
        let newtype = self.monotypes.function_newtype(monotype).cloned();
        let name = match &newtype {
            Some(newtype) => self.data_type_name(newtype)?,
            None => self.function_type_name(monotype)?,
        };
        let (function_name, origin) = match eliminators.of(monotype) {
            Some(found) => (found.name.clone(), found.origin),
            None => {
                let origin = newtype.as_ref().map(|newtype| newtype.file_id);
                let first = building.tags.first().and_then(|shape| shape.origin);
                let run = format_smolstr!("run{name}");
                let spelling = FunctionSpelling::Dispatch { closure: monotype };
                self.monotypes.function_spellings.entry(run.clone()).or_insert(spelling);
                (run, origin.or(first))
            }
        };
        let closure_name = match &newtype {
            Some(newtype) => self.context.type_name(newtype.file_id, newtype.item)?.to_string(),
            None => "function".to_string(),
        };
        let closure = fresh(lower_first(&closure_name).into(), monotype);
        let mut parameters = vec![];
        let mut passed = vec![];
        for (position, &argument) in building.arguments.iter().enumerate() {
            if self.is_unit(argument) {
                passed.push(None);
                continue;
            }
            let unnamed = self.monotypes.value_name(argument);
            let local = fresh(building.parameter_name(position).unwrap_or(unnamed), argument);
            passed.push(Some(local.clone()));
            parameters.push(local);
        }
        parameters.insert(building.closure_position, closure.clone());
        let mut alternatives = vec![];
        let mut tags = vec![];
        for (tag, shape) in building.tags.into_iter().enumerate() {
            let captures = shape
                .captures
                .iter()
                .map(|capture| Pattern {
                    kind: PatternKind::Variable(capture.clone()),
                    monotype: capture.monotype,
                })
                .collect();
            let pattern = Pattern { kind: PatternKind::Closure { tag, captures }, monotype };
            let body = shape.body.run(&shape.captures, &passed, building.result, self.monotypes);
            let body = Guarded::Unconditional(body);
            alternatives.push(Alternative { patterns: vec![pattern], body, position: None });
            tags.push(ClosureTag { name: shape.name, captures: shape.captures });
        }
        let scrutinee = Expression::new(ExpressionKind::Local(closure.id), monotype);
        let case = ExpressionKind::Case { scrutinees: vec![scrutinee], alternatives };
        let function = Function {
            name: function_name,
            origin,
            parameters,
            result: building.result,
            body: Expression::new(case, building.result),
            position: None,
        };
        Ok((function, ClosureSet { name, home: origin, tags }))
    }
}

struct Analysis<'t, 'a, 'q, 'p, Q> {
    types: &'t mut Types<'a, 'q, Q>,
    program: &'p Program,
    uses: Uses,
    /// The types already searched for function types that escape.
    escaped: FxHashSet<MonotypeId>,
    highest_local: u32,
    /// The function being analysed.
    current: FunctionId,
}

impl<Q> Analysis<'_, '_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    fn expression(&mut self, expression: &Expression) -> GoResult<()> {
        let monotype = expression.monotype;
        match &expression.kind {
            ExpressionKind::Local(_) => return Ok(()),
            ExpressionKind::Lambda { parameters, body } => {
                if let Some(first) = parameters.first() {
                    self.create(monotype, Creation::Lambda(first.id), parameters.len());
                }
                for parameter in parameters {
                    self.bind(parameter);
                }
                return self.expression(body);
            }
            ExpressionKind::Function(id) => {
                let parameters = self.program.function(*id).parameters.len();
                if parameters > 0 {
                    self.create(monotype, Creation::Known(*id, 0), parameters);
                }
                return Ok(());
            }
            ExpressionKind::Apply { function, arguments } => {
                let parameters = match function.kind {
                    ExpressionKind::Function(id) => self.program.function(id).parameters.len(),
                    _ => 0,
                };
                match function.kind {
                    ExpressionKind::Function(id) if parameters > arguments.len() => {
                        let creation = Creation::Known(id, arguments.len());
                        self.create(monotype, creation, parameters - arguments.len());
                    }
                    ExpressionKind::Function(_) if parameters > 0 => {
                        let result =
                            self.types.monotypes.result_after(function.monotype, parameters);
                        self.call(result, arguments.len() - parameters);
                    }
                    _ => {
                        self.call(function.monotype, arguments.len());
                        self.expression(function)?;
                    }
                }
                for argument in arguments {
                    self.expression(argument)?;
                }
                return Ok(());
            }
            ExpressionKind::Coerce(value)
                if !self.types.monotypes.same_without_causes(value.monotype, monotype) =>
            {
                self.escape(monotype)?;
                self.escape(value.monotype)?;
            }
            ExpressionKind::Foreign { foreign, arguments } => {
                if crate::arity::keeps_representation(foreign)
                    && !matches!(foreign, Foreign::UnsafeCoerce)
                {
                    // A runtime operation calls the functions it is passed and
                    // holds every other value as it is.
                    for argument in arguments {
                        if self.types.monotypes.function_parts(argument.monotype).is_some() {
                            self.open(argument.monotype, "passed to a runtime operation");
                        }
                    }
                } else {
                    self.escape(monotype)?;
                    for argument in arguments {
                        self.escape(argument.monotype)?;
                    }
                }
            }
            ExpressionKind::Let { bindings, .. } => {
                for binding in bindings {
                    self.bind(&binding.local);
                }
                for (position, binding) in bindings.iter().enumerate() {
                    let value = &binding.value;
                    if self.types.monotypes.function_parts(value.monotype).is_some()
                        && bindings[position..]
                            .iter()
                            .any(|later| uses_local(value, later.local.id))
                    {
                        self.open(value.monotype, "captures a binding still being defined");
                    }
                }
            }
            ExpressionKind::Case { alternatives, .. } => {
                for alternative in alternatives {
                    for pattern in &alternative.patterns {
                        self.bind_pattern(pattern);
                    }
                    if let Guarded::Guards(branches) = &alternative.body {
                        for branch in branches {
                            for guard in &branch.guards {
                                if let Guard::Pattern { pattern, .. } = guard {
                                    self.bind_pattern(pattern);
                                }
                            }
                        }
                    }
                }
            }
            ExpressionKind::EffectBind { local, .. }
            | ExpressionKind::EffectEach { element: local, .. } => self.bind(local),
            _ => {}
        }
        let made_otherwise = !matches!(
            expression.kind,
            ExpressionKind::Access { .. }
                | ExpressionKind::Let { .. }
                | ExpressionKind::If { .. }
                | ExpressionKind::Case { .. }
                | ExpressionKind::Coerce(_)
                | ExpressionKind::Foreign { .. }
                | ExpressionKind::Fail(_)
        );
        if made_otherwise && self.types.monotypes.function_parts(monotype).is_some() {
            self.open(monotype, "made by another construct");
        }
        let mut result = Ok(());
        for_each_child(expression, &mut |child| {
            if result.is_ok() {
                result = self.expression(child);
            }
        });
        result
    }

    fn bind(&mut self, local: &Local) {
        self.highest_local = self.highest_local.max(local.id.0);
    }

    fn bind_pattern(&mut self, pattern: &Pattern) {
        pattern.for_each_local(&mut |local| self.bind(local));
    }

    fn create(&mut self, monotype: MonotypeId, creation: Creation, parameters: usize) {
        let monotype = self.types.canonical(monotype);
        if self.types.monotypes.function_parts(monotype).is_none() {
            return;
        }
        if parameters != self.types.arity(monotype) {
            self.open(monotype, "created taking another number of arguments");
            return self.open_created_inside(monotype, parameters);
        }
        self.uses.creations.entry(monotype).or_default().insert(creation);
        self.touch(monotype);
    }

    /// Notes that the current function creates or calls values of `monotype`.
    fn touch(&mut self, monotype: MonotypeId) {
        let monotype = self.types.canonical(monotype);
        let functions = self.uses.touching.entry(monotype).or_default();
        if functions.last() != Some(&self.current) {
            functions.push(self.current);
        }
    }

    /// The calls of a function to itself in tail position, which become a
    /// loop: an argument that creates a value of a function type capturing
    /// the parameter it replaces links the new value to the previous one.
    fn tail_calls(&mut self, parameters: &[Local], expression: &Expression) {
        match &expression.kind {
            ExpressionKind::Let { body, .. } | ExpressionKind::EffectBind { body, .. } => {
                self.tail_calls(parameters, body)
            }
            ExpressionKind::If { then, otherwise, .. } => {
                self.tail_calls(parameters, then);
                self.tail_calls(parameters, otherwise);
            }
            ExpressionKind::Case { alternatives, .. } => {
                for alternative in alternatives {
                    match &alternative.body {
                        Guarded::Unconditional(body) => self.tail_calls(parameters, body),
                        Guarded::Guards(branches) => branches
                            .iter()
                            .for_each(|branch| self.tail_calls(parameters, &branch.body)),
                    }
                }
            }
            ExpressionKind::Apply { function, arguments }
                if matches!(function.kind, ExpressionKind::Function(callee) if callee == self.current)
                    && arguments.len() == parameters.len() =>
            {
                for (parameter, argument) in parameters.iter().zip(arguments) {
                    let monotypes = &self.types.monotypes;
                    if monotypes.same_without_causes(argument.monotype, parameter.monotype)
                        && self.creates(argument)
                        && uses_local(argument, parameter.id)
                    {
                        let linked = self.types.canonical(parameter.monotype);
                        self.uses.linked.insert(linked);
                    }
                }
            }
            _ => {}
        }
    }

    /// Whether an expression creates a value of a function type.
    fn creates(&self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Lambda { .. } => true,
            ExpressionKind::Apply { function, arguments } => matches!(function.kind,
                ExpressionKind::Function(id)
                    if self.program.function(id).parameters.len() > arguments.len()),
            _ => false,
        }
    }

    /// A lambda or known function taking more arguments than its type's
    /// arity creates the values of its results as Go functions.
    fn open_created_inside(&mut self, mut monotype: MonotypeId, mut parameters: usize) {
        loop {
            let arity = self.types.arity(monotype);
            if parameters <= arity || self.types.monotypes.function_parts(monotype).is_none() {
                return;
            }
            parameters -= arity;
            monotype = self.types.monotypes.result_after(monotype, arity);
            self.open(monotype, "created by a lambda taking more arguments");
        }
    }

    /// A value of `monotype` applied to `arguments` arguments.
    fn call(&mut self, monotype: MonotypeId, mut arguments: usize) {
        let mut monotype = self.types.canonical(monotype);
        while arguments > 0 && self.types.monotypes.function_parts(monotype).is_some() {
            self.touch(monotype);
            let arity = self.types.arity(monotype);
            if arguments < arity {
                return self.open(monotype, "applied to fewer arguments than it takes");
            }
            arguments -= arity;
            monotype = self.types.monotypes.result_after(monotype, arity);
        }
    }

    fn open(&mut self, monotype: MonotypeId, reason: &'static str) {
        let monotype = self.types.canonical(monotype);
        self.uses.open.entry(monotype).or_insert(reason);
    }

    /// Every function type a value of `monotype` holds crosses into code
    /// that expects Go functions.
    fn escape(&mut self, monotype: MonotypeId) -> GoResult<()> {
        let monotype = self.types.canonical(monotype);
        if !self.escaped.insert(monotype) {
            return Ok(());
        }
        let parts: Vec<MonotypeId> = match self.types.monotypes.get(monotype).clone() {
            Monotype::Function(argument, result) => {
                self.open(monotype, "crosses into foreign code or a coercion");
                vec![argument, result]
            }
            Monotype::Record(fields) => fields.iter().map(|field| field.monotype).collect(),
            Monotype::Data(data) => self.types.fields(&data)?,
            Monotype::Recursive(data) => vec![self.types.unfold(&data)?],
            container => container.element().into_iter().collect(),
        };
        for part in parts {
            self.escape(part)?;
        }
        Ok(())
    }

    /// A function type whose arity takes in some of its results' arguments
    /// creates no values of those results: its lambdas take all arguments at
    /// once, so the results stay Go functions.
    fn open_arities_reaching_inside(&mut self) {
        let widened: Vec<(MonotypeId, usize)> = self.types.arities.widened().collect();
        for (monotype, arity) in widened {
            let mut inner = monotype;
            for _ in 1..arity {
                inner = self.types.monotypes.result_after(inner, 1);
                self.open(inner, "taken apart by a wider arity");
            }
        }
    }
}

/// A lambda set being collected while the program is rewritten.
struct Building {
    dispatch: FunctionId,
    /// The type of the function that runs the cells.
    type_: MonotypeId,
    /// Where the cell is among that function's parameters: where its
    /// eliminator takes the newtype.
    closure_position: usize,
    arguments: Vec<MonotypeId>,
    result: MonotypeId,
    tags: Vec<Shape>,
    known: FxHashMap<(FunctionId, usize), usize>,
}

impl Building {
    /// The name of a parameter of the function that runs the cells: the one
    /// the lambdas that use their parameter agree on.
    fn parameter_name(&self, position: usize) -> Option<SmolStr> {
        let mut names = self.tags.iter().filter_map(|shape| match &shape.body {
            Body::Lambda { parameters, body } => parameters
                .get(position)
                .filter(|parameter| uses_local(body, parameter.id))
                .map(|parameter| &parameter.name),
            Body::Known { .. } => None,
        });
        match names.next() {
            Some(first) if names.all(|name| name == first) => Some(first.clone()),
            _ => None,
        }
    }
}

struct Shape {
    name: SmolStr,
    origin: Option<FileId>,
    captures: Vec<Local>,
    body: Body,
}

enum Body {
    Lambda {
        parameters: Vec<Local>,
        body: Expression,
    },
    /// A known function, whose leading arguments are the captures.
    Known {
        function: Expression,
    },
}

impl Body {
    /// The body of the alternative that runs this shape, given the locals
    /// the captures and arguments are bound to; a unit argument has none.
    fn run(
        self,
        captures: &[Local],
        passed: &[Option<Local>],
        result: MonotypeId,
        monotypes: &Monotypes,
    ) -> Expression {
        let argument = |position: usize, monotype: MonotypeId| match &passed[position] {
            Some(local) => Expression::new(ExpressionKind::Local(local.id), local.monotype),
            None => Expression::new(ExpressionKind::Unit, monotype),
        };
        match self {
            Body::Lambda { parameters, mut body } => {
                let renamed: FxHashMap<LocalId, Expression> = parameters
                    .iter()
                    .enumerate()
                    .map(|(position, parameter)| {
                        (parameter.id, argument(position, parameter.monotype))
                    })
                    .collect();
                rename(&mut body, &renamed);
                body
            }
            Body::Known { function } => {
                let mut arguments: Vec<Expression> = captures
                    .iter()
                    .map(|capture| {
                        Expression::new(ExpressionKind::Local(capture.id), capture.monotype)
                    })
                    .collect();
                let mut monotype = monotypes.result_after(function.monotype, captures.len());
                for position in 0..passed.len() {
                    let (parameter, rest) = monotypes
                        .function_parts(monotype)
                        .expect("invariant violated: a known function takes fewer arguments");
                    arguments.push(argument(position, parameter));
                    monotype = rest;
                }
                let apply = ExpressionKind::Apply { function: Box::new(function), arguments };
                Expression::new(apply, result)
            }
        }
    }
}

struct Rewriter<'r, 't, 'a, 'q, Q> {
    types: &'r mut Types<'a, 'q, Q>,
    program: &'r Program,
    sets: &'r mut FxHashMap<MonotypeId, Building>,
    /// Every local the current function binds.
    binders: FxHashMap<LocalId, Local>,
    /// The name and origin of the current function.
    name: SmolStr,
    origin: Option<FileId>,
    next_local: &'t mut u32,
}

impl<Q> Rewriter<'_, '_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    fn fresh(&mut self, name: SmolStr, monotype: MonotypeId) -> Local {
        Local::fresh(self.next_local, name, monotype)
    }

    fn parameters(&self, function: &Expression) -> usize {
        match function.kind {
            ExpressionKind::Function(id) => self.program.function(id).parameters.len(),
            _ => 0,
        }
    }

    fn rewrite(&mut self, expression: &mut Expression) {
        match &mut expression.kind {
            // A known function that is called is not a value of its type.
            ExpressionKind::Apply { function, arguments } if self.parameters(function) > 0 => {
                arguments.iter_mut().for_each(|argument| self.rewrite(argument))
            }
            _ => for_each_child_mut(expression, &mut |child| self.rewrite(child)),
        }
        let monotype = self.types.canonical(expression.monotype);
        if !self.sets.contains_key(&monotype) {
            if let ExpressionKind::Apply { .. } = expression.kind {
                self.call(expression);
            }
            return;
        }
        let parameters = self.parameters(expression);
        match &mut expression.kind {
            ExpressionKind::Lambda { .. } => {
                let kind = std::mem::replace(&mut expression.kind, ExpressionKind::Unit);
                let ExpressionKind::Lambda { parameters, body } = kind else { unreachable!() };
                let captures = self.captures(&body, &parameters);
                let values = captures.iter().map(Local::expression).collect();
                let shape = Shape {
                    name: self.name.clone(),
                    origin: self.origin,
                    captures,
                    body: Body::Lambda { parameters, body: *body },
                };
                let set = self.sets.get_mut(&monotype).expect("invariant violated: closed type");
                set.tags.push(shape);
                let tag = set.tags.len() - 1;
                expression.kind = ExpressionKind::Closure { tag, captures: values };
            }
            ExpressionKind::Function(id) if parameters > 0 => {
                let id = *id;
                let tag = self.known(monotype, id, expression.clone(), &[]);
                expression.kind = ExpressionKind::Closure { tag, captures: vec![] };
            }
            ExpressionKind::Apply { function, arguments }
                if self.parameters(function) > arguments.len() =>
            {
                let ExpressionKind::Function(id) = function.kind else { unreachable!() };
                let function = (**function).clone();
                let arguments = std::mem::take(arguments);
                let tag = self.known(monotype, id, function, &arguments);
                expression.kind = ExpressionKind::Closure { tag, captures: arguments };
            }
            ExpressionKind::Apply { .. } => self.call(expression),
            _ => {}
        }
    }

    /// The tag of a known function applied to `arguments`, shared by every
    /// place that applies it to as many.
    fn known(
        &mut self,
        monotype: MonotypeId,
        id: FunctionId,
        function: Expression,
        arguments: &[Expression],
    ) -> usize {
        if let Some(&tag) = self.sets[&monotype].known.get(&(id, arguments.len())) {
            return tag;
        }
        let callee = self.program.function(id);
        let captures = arguments
            .iter()
            .zip(&callee.parameters)
            .map(|(argument, parameter)| (parameter.name.clone(), argument.monotype))
            .collect::<Vec<_>>()
            .into_iter()
            .map(|(name, monotype)| self.fresh(name, monotype))
            .collect();
        let callee = self.program.function(id);
        let shape = Shape {
            name: callee.name.clone(),
            origin: callee.origin,
            captures,
            body: Body::Known { function },
        };
        let set = self.sets.get_mut(&monotype).expect("invariant violated: closed type");
        set.tags.push(shape);
        let tag = set.tags.len() - 1;
        set.known.insert((id, arguments.len()), tag);
        tag
    }

    /// An application whose function, or one of whose intermediate results,
    /// has a closed type calls the function that runs its cells.
    fn call(&mut self, expression: &mut Expression) {
        let ExpressionKind::Apply { function, arguments } = &expression.kind else { return };
        let parameters = self.parameters(function);
        let start = self.types.monotypes.result_after(function.monotype, parameters);
        if !self.reaches_closed(start, arguments.len().saturating_sub(parameters)) {
            return;
        }
        let kind = std::mem::replace(&mut expression.kind, ExpressionKind::Unit);
        let ExpressionKind::Apply { function, mut arguments } = kind else { unreachable!() };
        let (mut value, mut rest) = if parameters > 0 {
            let rest = arguments.split_off(parameters);
            (Expression::new(ExpressionKind::Apply { function, arguments }, start), rest)
        } else {
            (*function, arguments)
        };
        while !rest.is_empty() {
            let monotype = self.types.canonical(value.monotype);
            let arity = self.types.arity(monotype).min(rest.len());
            let remaining = rest.split_off(arity);
            let taken = std::mem::replace(&mut rest, remaining);
            let result = self.types.monotypes.result_after(monotype, arity);
            value = match self.sets.contains_key(&monotype) {
                true => self.dispatch(monotype, value, taken, result),
                false => {
                    let apply =
                        ExpressionKind::Apply { function: Box::new(value), arguments: taken };
                    Expression::new(apply, result)
                }
            };
        }
        *expression = value;
    }

    /// A call of the function that runs the cells of `monotype`. A unit
    /// argument is not passed. When the call takes its operands in another
    /// order, or a unit argument has to be computed, the operands that do
    /// work are computed first, in their order.
    fn dispatch(
        &mut self,
        monotype: MonotypeId,
        value: Expression,
        taken: Vec<Expression>,
        result: MonotypeId,
    ) -> Expression {
        let position = self.sets[&monotype].closure_position;
        let passed_before =
            taken.iter().filter(|argument| !self.types.is_unit(argument.monotype)).take(position);
        let reordered = (!is_value(&value)
            && passed_before.clone().any(|argument| !is_value(argument)))
            || taken
                .iter()
                .any(|argument| self.types.is_unit(argument.monotype) && !is_value(argument));
        let mut computed = vec![];
        let mut operand = |rewriter: &mut Self, operand: Expression| {
            if !reordered || is_value(&operand) {
                return operand;
            }
            let local = rewriter.fresh(SmolStr::new_static("operand"), operand.monotype);
            let reference = local.expression();
            computed.push(Binding { local, value: operand });
            reference
        };
        let value = operand(self, value);
        let mut arguments = vec![];
        for argument in taken {
            let argument = operand(self, argument);
            if !self.types.is_unit(argument.monotype) {
                arguments.push(argument);
            }
        }
        arguments.insert(position.min(arguments.len()), value);
        let set = &self.sets[&monotype];
        let function = Expression::new(ExpressionKind::Function(set.dispatch), set.type_);
        let call = ExpressionKind::Apply { function: Box::new(function), arguments };
        let call = Expression::new(call, result);
        if computed.is_empty() {
            return call;
        }
        Expression::new(ExpressionKind::Let { bindings: computed, body: Box::new(call) }, result)
    }

    fn reaches_closed(&mut self, monotype: MonotypeId, mut arguments: usize) -> bool {
        let mut monotype = self.types.canonical(monotype);
        while arguments > 0 && self.types.monotypes.function_parts(monotype).is_some() {
            if self.sets.contains_key(&monotype) {
                return true;
            }
            let arity = self.types.arity(monotype).min(arguments);
            arguments -= arity;
            monotype = self.types.monotypes.result_after(monotype, arity);
        }
        false
    }

    /// The locals a lambda's body uses that it does not bind, in order of
    /// first use.
    fn captures(&self, body: &Expression, parameters: &[Local]) -> Vec<Local> {
        let mut binders = FxHashMap::default();
        collect_binders(body, &mut binders);
        let mut seen: FxHashSet<LocalId> =
            parameters.iter().map(|parameter| parameter.id).collect();
        seen.extend(binders.keys().copied());
        let mut captures: Vec<Local> = vec![];
        crate::monomorphic::traversal::visit(body, &mut |node| {
            if let ExpressionKind::Local(id) = node.kind
                && seen.insert(id)
            {
                let local = self.binders.get(&id).cloned().unwrap_or(Local {
                    id,
                    name: SmolStr::new_static("captured"),
                    monotype: node.monotype,
                });
                captures.push(local);
            }
        });
        captures
    }
}

/// Replaces each use of a renamed local.
fn rename(expression: &mut Expression, renamed: &FxHashMap<LocalId, Expression>) {
    if let ExpressionKind::Local(id) = expression.kind
        && let Some(replacement) = renamed.get(&id)
    {
        *expression = replacement.clone();
        return;
    }
    for_each_child_mut(expression, &mut |child| rename(child, renamed));
}

fn report(uses: &Uses, closed: &[MonotypeId], monotypes: &Monotypes) {
    let mut reasons: FxHashMap<&'static str, usize> = FxHashMap::default();
    let mut not_linked = 0;
    let mut too_many = 0;
    for (monotype, creations) in &uses.creations {
        if let Some(reason) = uses.open.get(monotype) {
            *reasons.entry(reason).or_insert(0) += 1;
        } else if !uses.linked.contains(monotype) {
            not_linked += 1;
        } else if creations.len() > MOST_TAGS {
            too_many += 1;
        }
    }
    eprintln!(
        "closures: {} of {} created function types become cells; {not_linked} closed but not \
         linked, {too_many} with more than {MOST_TAGS} shapes; open: {reasons:?}",
        closed.len(),
        uses.creations.len()
    );
    for &monotype in closed {
        let shapes = uses.creations[&monotype].len();
        eprintln!("closures:   {monotype:?} {:?}: {shapes} shapes", monotypes.get(monotype));
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// The struct of a closed function type: a tag per shape and a slot per
    /// capture, shared by shapes that capture alike named values of one type.
    pub(super) fn closure_layout(&mut self, monotype: MonotypeId) -> GoResult<DataLayout> {
        let monotype = self.monotypes.without_causes(monotype);
        if let Some(layout) = self.closure_layouts.get(&monotype) {
            return Ok(layout.clone());
        }
        let set = &self.closure_sets[&monotype];
        let home = set.home;
        let shapes: Vec<(SmolStr, Vec<Local>)> =
            set.tags.iter().map(|tag| (tag.name.clone(), tag.captures.clone())).collect();
        let base = identifier(&set.name);
        let parts = self.closure_parts(monotype)?;
        let name = self.pending_global(base, super::names::PendingSpelling::Parts(parts));
        if let Some(home) = home {
            self.homes.insert(name.clone(), home);
        }
        // A linked set has a shape that captures the set's own type, so the
        // cells always have fields and are always pointers.
        let kind = if shapes.len() == 1 { DataKind::Product } else { DataKind::Tagged };
        let (slots_of_shapes, fields) = closure_slots(&shapes, self.monotypes);
        let mut constructors = vec![];
        for ((tag_name, _), slots) in shapes.iter().zip(&slots_of_shapes) {
            let suffix = crate::naming::go_field(tag_name);
            let tag = self.global_name(Spelling::derived("", name.clone(), &suffix));
            let fields = slots.iter().cloned().zip(fields_of(slots, &fields)).collect();
            constructors.push(ConstructorLayout { tag, fields });
        }
        let layout = DataLayout {
            name: name.clone(),
            kind,
            constructors: constructors.clone(),
            erases_arguments: false,
            boxed: true,
            declaration: None,
            origin_position: 0,
            maybe: None,
            edges: None,
        };
        self.closure_layouts.insert(monotype, layout.clone());
        let tags: Vec<String> =
            constructors.iter().map(|constructor| constructor.tag.clone()).collect();
        let plan = self.arrange_slots(shapes.len(), slots_of_shapes, fields)?;
        let mut struct_fields = vec![];
        for slot in plan.slots {
            struct_fields.push(match slot {
                layout::Slot::Tag => StructField::new("Tag", layout::tag_type(tags.len())),
                layout::Slot::Unique => StructField::new("Unique", layout::unique_type()),
                layout::Slot::Field { name, monotype } => {
                    StructField::new(name, self.go_type(monotype)?)
                }
            });
        }
        self.type_declarations.push(GoDeclaration::Type {
            name,
            type_: GoType::Struct(struct_fields),
            line: None,
            member_lines: vec![],
        });
        if kind == DataKind::Tagged {
            self.type_declarations.push(GoDeclaration::Constants {
                type_name: None,
                names: tags,
                line: None,
                member_lines: vec![],
            });
        }
        Ok(layout)
    }

    /// A cell of a closed function type.
    pub(super) fn closure_value(
        &mut self,
        monotype: MonotypeId,
        tag: usize,
        values: Vec<GoExpression>,
    ) -> GoResult<GoExpression> {
        let layout = self.closure_layout(monotype)?;
        let constructor = &layout.constructors[tag];
        Ok(match layout.kind {
            DataKind::Tagged if constructor.fields.is_empty() => {
                let tag = constructor.tag.clone();
                self.shared_nullary(&layout.name, &tag, true, None)
            }
            _ => GoExpression::Address(Box::new(self.composite(&layout, tag, values))),
        })
    }
}

/// The slot of each capture of each shape, and every slot once: captures
/// with the same name and type share one.
fn closure_slots(
    shapes: &[(SmolStr, Vec<Local>)],
    monotypes: &Monotypes,
) -> (Vec<Vec<String>>, Vec<(String, MonotypeId)>) {
    // Each slot with the name its captures share, before a counter kept it distinct.
    let mut slots: Vec<(String, String, MonotypeId)> = vec![];
    let mut slots_of_shapes = vec![];
    for (_, captures) in shapes {
        let mut of_shape: Vec<String> = vec![];
        for capture in captures {
            let base = capitalise(&identifier(&capture.name));
            let shared = slots.iter().find(|(name, slot_base, monotype)| {
                monotypes.same_without_causes(*monotype, capture.monotype)
                    && *slot_base == base
                    && !of_shape.contains(name)
            });
            let slot = match shared {
                Some((name, _, _)) => name.clone(),
                None => {
                    let name = numbered(&base, |name| {
                        name == "Tag" || slots.iter().any(|(taken, _, _)| taken == name)
                    });
                    slots.push((name.clone(), base, capture.monotype));
                    name
                }
            };
            of_shape.push(slot);
        }
        slots_of_shapes.push(of_shape);
    }
    let fields = slots.into_iter().map(|(name, _, monotype)| (name, monotype)).collect();
    (slots_of_shapes, fields)
}

fn fields_of(slots: &[String], fields: &[(String, MonotypeId)]) -> Vec<MonotypeId> {
    slots
        .iter()
        .map(|slot| {
            fields
                .iter()
                .find(|(name, _)| name == slot)
                .map(|(_, monotype)| *monotype)
                .expect("invariant violated: a capture's slot is declared")
        })
        .collect()
}
