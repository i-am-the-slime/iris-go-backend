//! Array pipelines fused into the loop of their consumer.
//!
//! `foldl f z (map g (filter p xs))` names two arrays that exist only to be
//! read once by the next stage: an argument of a call has no other use. Rather
//! than a loop and an allocation per stage, the consumer's loop runs over `xs`
//! and each element passes through the stages on its way:
//!
//! ```go
//! for _, x := range xs {
//!     if p(x) {
//!         accumulator = f(accumulator, g(x))
//!     }
//! }
//! ```
//!
//! A `map` stage binds its result, a `filter` stage guards the rest of the
//! body, and a `concatMap` stage opens a loop over the array its callback
//! returns. A `first .. last` range needs no array at all: with literal bounds
//! that count up the loop counts from `first` to `last`, and otherwise it
//! counts through the range's positions, which a support function works out
//! from the bounds, since the range descends when `first > last`:
//!
//! ```go
//! step, count := array.RangeSteps(first, last)
//! for index := range count {
//!     x := first + index*step
//!     ...
//! }
//! ```
//!
//! The callbacks are pure, so interleaving the stages is not observable. Each
//! callback still sees its elements in their order and is called for exactly
//! the elements it was before, except where nothing reads its result: a
//! `length` ignores what a `map` computes, and a consumer that stops early
//! leaves the remaining elements alone.

use std::collections::VecDeque;

use super::conditions::negated;
use super::iteration::{Callback, Found};
use super::{
    Emitter, Mode, Sink, binary, call, identifier_expression, is_simple, length, lines, uses_local,
};
use crate::error::GoResult;
use crate::foreign::{
    ARRAY_APPEND, ARRAY_REPLICATE, ARRAY_SCANL, Boundary, Foreign, GoFunction, GoPackage, Iteration,
};
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Guarded, Literal, Local, Pattern, PatternKind,
};
use crate::monotype::{Monotype, MonotypeId};
use crate::naming::VALUE;
use crate::syntax::{GoExpression, GoStatement, SourceLine};

/// The most elements of a literal prefix stored in one assignment.
const PREFIX_ON_ONE_LINE: usize = 4;

/// The stages between an array and the consumer that reads it.
pub(super) struct Pipeline<'e> {
    source: Source<'e>,
    /// Nearest the source first.
    stages: Vec<Stage<'e>>,
    order: Order,
}

enum Source<'e> {
    Array(GoExpression),
    /// `first .. last` counting up.
    Range {
        first: i64,
        last: i64,
    },
    /// `first .. last` with bounds known when the loop starts: `count`
    /// elements from `first`, `step` apart.
    Stepping(Steps),
    Replicate {
        count: GoExpression,
        value: GoExpression,
    },
    Zip(Box<Zip<'e>>),
    Guard {
        condition: GoExpression,
        value: GoExpression,
    },
}

struct Zip<'e> {
    operands: Vec<Pipeline<'e>>,
    callback: Callback<'e>,
    produces: MonotypeId,
    count: GoExpression,
}

struct Steps {
    first: GoExpression,
    step: GoExpression,
    count: GoExpression,
}

/// What lies between a consumer and its source, nearest the consumer first.
enum Step<'e> {
    Bindings(&'e [Binding]),
    Stage {
        kind: StageKind,
        callback: Found<'e>,
        initial: Option<&'e Expression>,
        produces: MonotypeId,
        runs: bool,
    },
}

struct Stage<'e> {
    kind: StageKind,
    callback: Callback<'e>,
    /// The type of the elements the stage produces.
    produces: MonotypeId,
    state: Option<String>,
}

struct StageParts<'e> {
    kind: StageKind,
    callback: Found<'e>,
    inner: &'e Expression,
    initial: Option<&'e Expression>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StageKind {
    Map,
    MapWithIndex,
    Scan,
    Filter,
    Bind,
}

impl StageKind {
    fn keeps_positions(self) -> bool {
        matches!(self, StageKind::Map | StageKind::MapWithIndex | StageKind::Scan)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Order {
    Forward,
    Backward,
}

/// What a consumer asks of the elements it is given.
#[derive(Debug, Clone, Copy)]
pub(super) struct Demand {
    pub order: Order,
    /// The consumer reads each element's position in the source.
    pub positions: bool,
    /// The consumer leaves the loop with `break`, which an inner loop would catch.
    pub breaks: bool,
    /// The pipeline runs inside another's loop, which counts positions only
    /// in its own source.
    pub nested: bool,
}

impl Demand {
    pub(super) const FORWARD: Demand =
        Demand { order: Order::Forward, positions: false, breaks: false, nested: false };
}

/// How a consumer reads the element its loop hands it.
#[derive(Clone, Copy)]
pub(super) enum Need<'c, 'e> {
    Nothing,
    /// As one argument of its callback.
    Argument {
        callback: &'c Callback<'e>,
        position: usize,
    },
    /// As its callback's argument and once more besides.
    Variable {
        callback: &'c Callback<'e>,
        position: usize,
    },
    /// As a value it stores, once.
    Value,
}

/// A loop being built: the source loop, then a frame for every stage that
/// guards or nests what follows it.
pub(super) struct Loop {
    frames: Vec<Frame>,
}

struct Frame {
    header: Header,
    body: Vec<GoStatement>,
}

enum Header {
    Range { index: Option<String>, element: String, iterable: GoExpression },
    Counting { variable: String, first: i64, last: i64 },
    Backward { index: Option<String>, element: String, array: GoExpression },
    Stepping { index: Option<String>, element: String, steps: Steps, order: Order },
    Positions { index: Option<String>, count: GoExpression },
    If(GoExpression, Option<SourceLine>),
}

pub(super) struct Opened {
    pub body: Loop,
    /// The consumer's element, or `_` when it needs none.
    pub element: GoExpression,
    /// The element's position in the source, when the consumer asked for it.
    pub index: Option<String>,
    /// `element` is an array whose elements are the consumer's, which a
    /// `concatMap` stage at the end of the pipeline hands over whole.
    pub spread: bool,
}

impl Need<'_, '_> {
    fn reads(self) -> bool {
        match self {
            Need::Nothing => false,
            Need::Argument { callback, position } => callback.reads(position),
            Need::Variable { .. } | Need::Value => true,
        }
    }
}

impl Loop {
    pub(super) fn body(&mut self) -> &mut Vec<GoStatement> {
        &mut self.frames.last_mut().expect("invariant violated: a loop has a frame").body
    }
}

impl<'e> Pipeline<'e> {
    /// The pipeline followed by a `concatMap` stage.
    pub(super) fn then_bind(mut self, callback: Callback<'e>, produces: MonotypeId) -> Self {
        self.stages.push(Stage { kind: StageKind::Bind, callback, produces, state: None });
        self
    }

    pub(super) fn keeps_positions(&self) -> bool {
        self.stages.iter().all(|stage| stage.kind.keeps_positions())
    }

    /// The number of elements, when no stage changes it.
    pub(super) fn known_length(&self) -> Option<GoExpression> {
        if !self.keeps_positions() {
            return None;
        }
        Some(match &self.source {
            Source::Array(array) => length(array.clone()),
            Source::Range { first, last } => GoExpression::Integer(last - first + 1),
            Source::Stepping(steps) => steps.count.clone(),
            Source::Replicate { count, .. } => count.clone(),
            Source::Zip(zip) => zip.count.clone(),
            Source::Guard { .. } => return None,
        })
    }

    fn count(&self) -> Option<GoExpression> {
        self.known_length()
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// Whether `array`, past any `let`, is a stage or a range that a
    /// consumer's loop can absorb.
    pub(super) fn is_fusible(&self, array: &Expression, demand: Demand) -> bool {
        let array = past_bindings(array);
        self.stage_parts(array, demand, false).is_some()
            || range_bounds(array).is_some()
            || (demand.order == Order::Forward && self.generated(array).is_some())
    }

    fn guarded<'e>(&self, array: &'e Expression) -> Option<(&'e Expression, &'e Expression, bool)> {
        let (condition, then, otherwise) = choice(array)?;
        let constant = |expression: &Expression| {
            matches!(
                expression.kind,
                ExpressionKind::Unit
                    | ExpressionKind::Literal(_)
                    | ExpressionKind::Foreign { foreign: Foreign::Unit, .. }
            )
        };
        let single = |expression: &'e Expression| match &expression.kind {
            ExpressionKind::Array(elements) => match elements.as_slice() {
                [element] if constant(element) => Some(element),
                _ => None,
            },
            _ => None,
        };
        if let Some(kept) = single(then)
            && self.is_empty_array(otherwise)
        {
            return Some((condition, kept, true));
        }
        if let Some(kept) = single(otherwise)
            && self.is_empty_array(then)
        {
            return Some((condition, kept, false));
        }
        None
    }

    fn is_empty_array(&self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Array(elements) => elements.is_empty(),
            ExpressionKind::Function(id) => {
                let function = self.program.function(*id);
                function.parameters.is_empty()
                    && !matches!(function.body.kind, ExpressionKind::Function(_))
                    && self.is_empty_array(&function.body)
            }
            _ => false,
        }
    }

    fn generated<'e>(&self, array: &'e Expression) -> Option<Generated<'e>> {
        let ExpressionKind::Foreign { foreign, arguments } = &array.kind else { return None };
        if foreign.calls(ARRAY_REPLICATE)
            && let [count, value] = arguments.as_slice()
        {
            return Some(Generated::Replicate { count, value });
        }
        let zips = self.zips(array);
        let (callback, operands) = zips.into_iter().find_map(|(function, operands)| {
            if self.effect_after(function.monotype, operands.len()) {
                return None;
            }
            Some((self.callback(function, operands.len())?, operands))
        })?;
        Some(Generated::Zip { callback, operands })
    }

    fn zips<'e>(&self, array: &'e Expression) -> Vec<(&'e Expression, Vec<&'e Expression>)> {
        let ExpressionKind::Foreign { foreign, arguments } = &array.kind else { return vec![] };
        let Foreign::Call {
            boundary: Boundary { iteration: Some(Iteration::ZipWith), .. }, ..
        } = foreign
        else {
            return vec![];
        };
        let [function, left, right] = arguments.as_slice() else { return vec![] };
        let mut zips = vec![];
        if self.is_application(function) {
            for (partial, mut operands) in self.zips(left) {
                operands.push(right);
                zips.push((partial, operands));
            }
        }
        zips.push((function, vec![left, right]));
        zips
    }

    fn is_application(&self, function: &Expression) -> bool {
        let applies = |parameters: &[&Local], body: &Expression| {
            let ExpressionKind::Apply { function, arguments } = &body.kind else { return false };
            let ([applied, argument], [given]) = (parameters, arguments.as_slice()) else {
                return false;
            };
            matches!(function.kind, ExpressionKind::Local(id) if id == applied.id)
                && matches!(given.kind, ExpressionKind::Local(id) if id == argument.id)
        };
        match self.callback(function, 2) {
            Some(Found::Inline { parameters, body }) => applies(&parameters, body),
            Some(Found::Direct { callee, leading: [], .. }) => {
                let callee = self.program.function(callee);
                let parameters: Vec<&Local> = callee.parameters.iter().collect();
                applies(&parameters, &callee.body)
            }
            _ => false,
        }
    }

    /// The pipeline a `concatMap` callback returns, which can run as a loop
    /// nested in the caller's instead of building the array it returns.
    pub(super) fn nested_pipeline<'e>(&self, callback: &Callback<'e>) -> Option<&'e Expression> {
        let Callback::Inline { body, .. } = callback else { return None };
        let nested = Demand { nested: true, ..Demand::FORWARD };
        self.is_fusible(body, nested).then_some(*body)
    }

    /// Evaluates what the stages and the source capture, in the order separate
    /// loops would have, and leaves the stages' callbacks to `open`. A `map`
    /// whose results nobody reads is dropped with its callback.
    pub(super) fn pipeline<'e>(
        &mut self,
        array: &'e Expression,
        demand: Demand,
        need: Need<'_, '_>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Pipeline<'e>> {
        self.pipeline_reading(array, demand, need.reads(), out)
    }

    fn pipeline_reading<'e>(
        &mut self,
        array: &'e Expression,
        demand: Demand,
        read: bool,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Pipeline<'e>> {
        let mut steps = vec![];
        let mut current = array;
        let mut positional = demand.positions || demand.order == Order::Backward;
        loop {
            if let ExpressionKind::Let { bindings, body } = &current.kind {
                steps.push(Step::Bindings(bindings));
                current = body;
                continue;
            }
            let Some(StageParts { kind, callback, inner, initial }) =
                self.stage_parts(current, demand, positional)
            else {
                break;
            };
            positional |= kind == StageKind::MapWithIndex;
            let produces = match self.monotypes.get(current.monotype) {
                Monotype::Array(element) => *element,
                _ => unreachable!("invariant violated: an array stage produces an array"),
            };
            steps.push(Step::Stage { kind, callback, initial, produces, runs: true });
            current = inner;
        }
        // Reads propagate from the consumer towards the source, the order of `steps`.
        let mut read = read;
        for step in &mut steps {
            let Step::Stage { kind, callback, runs, .. } = step else { continue };
            let reads = callback.reads(element_position(*kind));
            *runs = !kind.keeps_positions() || read;
            read = match kind {
                StageKind::Map | StageKind::MapWithIndex | StageKind::Scan => read && reads,
                StageKind::Filter => reads || read,
                StageKind::Bind => reads,
            };
        }
        let mut stages = vec![];
        for step in steps {
            match step {
                Step::Bindings(bindings) => self.bindings(bindings, out)?,
                Step::Stage { kind, callback, initial, produces, runs: true } => {
                    let callback = self.capture(callback, out)?;
                    let state = match initial {
                        Some(initial) => Some(self.scan_state(initial, produces, out)?),
                        None => None,
                    };
                    stages.push(Stage { kind, callback, produces, state });
                }
                Step::Stage { runs: false, .. } => {}
            }
        }
        stages.reverse();
        let source = match (literal_range(current), range_bounds(current)) {
            (Some((first, last)), _) if !positional => Source::Range { first, last },
            (_, Some(bounds)) => Source::Stepping(self.steps(bounds, read, out)?),
            (_, None) => {
                let demand = Demand { positions: positional, ..demand };
                self.source(current, demand, read, out)?
            }
        };
        Ok(Pipeline { source, stages, order: demand.order })
    }

    fn source<'e>(
        &mut self,
        array: &'e Expression,
        demand: Demand,
        read: bool,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Source<'e>> {
        let generated = (demand.order == Order::Forward).then(|| self.generated(array)).flatten();
        match generated {
            Some(Generated::Replicate { count, value }) => {
                let count = self.value(count, out)?;
                let count = match count {
                    GoExpression::Integer(count) => GoExpression::Integer(count.max(0)),
                    count if is_go_length(&count) => count,
                    count => {
                        let count = call(
                            identifier_expression("max"),
                            vec![count, GoExpression::Integer(0)],
                        );
                        self.hoist(count, "count", out)
                    }
                };
                let replicated = self.value(value, out)?;
                let replicated = self.typed_constant(replicated, value.monotype)?;
                let value = self.hoist(replicated, "value", out);
                Ok(Source::Replicate { count, value })
            }
            Some(Generated::Zip { callback, operands }) => {
                let callback = self.capture(callback, out)?;
                let produces = match self.monotypes.get(array.monotype) {
                    Monotype::Array(element) => *element,
                    _ => unreachable!("invariant violated: zipWith produces an array"),
                };
                let positional = Demand { positions: true, ..Demand::FORWARD };
                let mut pipelines = vec![];
                let mut lengths = vec![];
                for (position, operand) in operands.into_iter().enumerate() {
                    let reads = read && callback.reads(position);
                    let pipeline = self.pipeline_reading(operand, positional, reads, out)?;
                    let length = pipeline.count();
                    lengths.push(
                        length.expect("invariant violated: a positional pipeline has a length"),
                    );
                    pipelines.push(pipeline);
                }
                let shortest = lengths.iter().try_fold(i64::MAX, |shortest, length| match length {
                    GoExpression::Integer(length) => Some(shortest.min(*length)),
                    _ => None,
                });
                let count = match shortest {
                    Some(shortest) => GoExpression::Integer(shortest),
                    None => {
                        let count = call(identifier_expression("min"), lengths);
                        self.hoist(count, "count", out)
                    }
                };
                let operands = pipelines;
                Ok(Source::Zip(Box::new(Zip { operands, callback, produces, count })))
            }
            None => {
                if demand.order == Order::Forward
                    && !demand.positions
                    && let Some((condition, kept, holds)) = self.guarded(array)
                {
                    let condition = self.value(condition, out)?;
                    let condition = if holds { condition } else { negated(&condition) };
                    let mut ignored = vec![];
                    let value = self.value(kept, &mut ignored)?;
                    return Ok(Source::Guard { condition, value });
                }
                let value = self.value(array, out)?;
                Ok(Source::Array(self.hoist(value, "array", out)))
            }
        }
    }

    fn scan_state(
        &mut self,
        initial: &Expression,
        produces: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<String> {
        let value = self.value(initial, out)?;
        let state = self.temporary("scanned");
        out.push(self.define(state.clone(), value, produces)?);
        Ok(state)
    }

    /// Works out where a range's loop starts, which way it counts and how far.
    /// A loop that reads no element only needs to know how far.
    fn steps(
        &mut self,
        (first, last): (&Expression, &Expression),
        read: bool,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Steps> {
        if let Some((first, last)) = literal_bounds(first, last) {
            let step = GoExpression::Integer(if first > last { -1 } else { 1 });
            let count = GoExpression::Integer((last - first).abs() + 1);
            return Ok(Steps { first: GoExpression::Integer(first), step, count });
        }
        let start = self.value(first, out)?;
        let start = if is_simple(&start) {
            start
        } else {
            let start = self.typed_constant(start, first.monotype)?;
            self.hoist(start, "first", out)
        };
        let end = self.value(last, out)?;
        let range_steps =
            self.go_function(GoFunction { package: GoPackage::Array, name: "RangeSteps" });
        let step = if read { self.temporary("step") } else { "_".into() };
        let count = self.temporary("count");
        let steps = super::call(range_steps, vec![start.clone(), end]);
        out.push(GoStatement::Define {
            names: vec![step.clone(), count.clone()],
            values: vec![steps],
        });
        let step = identifier_expression(&step);
        Ok(Steps { first: start, step, count: identifier_expression(&count) })
    }

    fn stage_parts<'e>(
        &self,
        array: &'e Expression,
        demand: Demand,
        positional: bool,
    ) -> Option<StageParts<'e>> {
        let ExpressionKind::Foreign { foreign, arguments } = &array.kind else { return None };
        if foreign.calls(ARRAY_SCANL) {
            let [callback, initial, inner] = arguments.as_slice() else { return None };
            if demand.order == Order::Backward || self.effect_after(callback.monotype, 2) {
                return None;
            }
            let callback = self.callback(callback, 2)?;
            let initial = Some(initial);
            return Some(StageParts { kind: StageKind::Scan, callback, inner, initial });
        }
        let Foreign::Call { boundary: Boundary { iteration: Some(iteration), .. }, .. } = foreign
        else {
            return None;
        };
        let (kind, callback, inner, arity) = match iteration {
            Iteration::Map => (StageKind::Map, &arguments[0], &arguments[1], 1),
            Iteration::MapWithIndex => (StageKind::MapWithIndex, &arguments[0], &arguments[1], 2),
            Iteration::Filter => (StageKind::Filter, &arguments[0], &arguments[1], 1),
            Iteration::Bind => (StageKind::Bind, &arguments[1], &arguments[0], 1),
            _ => return None,
        };
        if positional && !kind.keeps_positions() {
            return None;
        }
        if demand.breaks && kind == StageKind::Bind {
            return None;
        }
        if demand.nested && kind == StageKind::MapWithIndex {
            return None;
        }
        if self.effect_after(callback.monotype, arity) {
            return None;
        }
        let callback = self.callback(callback, arity)?;
        Some(StageParts { kind, callback, inner, initial: None })
    }

    /// Starts the loop over a pipeline's source and runs every stage, leaving
    /// the consumer to add its part to the innermost body.
    pub(super) fn open(
        &mut self,
        pipeline: Pipeline<'_>,
        need: Need<'_, '_>,
        index_base: Option<&str>,
    ) -> GoResult<Opened> {
        let Pipeline { source, stages, order } = pipeline;
        let needed = needed_inputs(&stages, need);
        let element = if needed[0] { self.element_name(&stages, 0, need) } else { "_".into() };
        let stage_positions = stages.iter().enumerate().any(|(position, stage)| {
            stage.kind == StageKind::MapWithIndex && needed[position + 1] && stage.callback.reads(0)
        });
        let index = match index_base {
            Some(base) => Some(self.temporary(base)),
            None if stage_positions => Some(self.temporary("index")),
            None => None,
        };
        let (header, prefix) = self.header(source, order, index.clone(), element.clone())?;
        let mut body = Loop { frames: vec![Frame { header, body: prefix }] };
        let mut flow = identifier_expression(&element);
        let mut remaining = VecDeque::from(stages);
        while let Some(stage) = remaining.pop_front() {
            let downstream = needed_inputs(remaining.make_contiguous(), need)[0];
            flow = match stage.kind {
                StageKind::Map | StageKind::MapWithIndex if self.is_unit(stage.produces) => {
                    super::unit_value()
                }
                StageKind::Map | StageKind::MapWithIndex => {
                    let mut arguments = vec![];
                    if stage.kind == StageKind::MapWithIndex {
                        let index = index.as_deref().unwrap_or("_");
                        arguments.push(self.receive_index(&stage.callback, index, body.body()));
                    }
                    let position = arguments.len();
                    let argument =
                        self.receive(flow, &stage.callback, position, true, body.body())?;
                    arguments.push(argument);
                    if takes_expression(remaining.make_contiguous(), need) {
                        self.callback_value(&stage.callback, arguments, body.body())?
                    } else {
                        let name = self.element_name(remaining.make_contiguous(), 0, need);
                        let sink = Sink::Define(name.clone());
                        let callback = &stage.callback;
                        self.apply_callback(
                            callback,
                            arguments,
                            stage.produces,
                            sink,
                            body.body(),
                        )?;
                        identifier_expression(&name)
                    }
                }
                StageKind::Filter => {
                    let argument =
                        self.receive(flow, &stage.callback, 0, !downstream, body.body())?;
                    let condition =
                        self.callback_value(&stage.callback, vec![argument.clone()], body.body())?;
                    let line = match &stage.callback {
                        Callback::Inline { body, .. } => self.branch_line(body.position)?,
                        Callback::Direct { .. } => None,
                    };
                    let header = Header::If(condition, line);
                    body.frames.push(Frame { header, body: vec![] });
                    argument
                }
                StageKind::Bind => {
                    let argument = self.receive(flow, &stage.callback, 0, true, body.body())?;
                    let source = match self.nested_pipeline(&stage.callback) {
                        Some(inner) => {
                            let demand = Demand { nested: true, ..Demand::FORWARD };
                            let nested =
                                self.pipeline_reading(inner, demand, downstream, body.body())?;
                            for stage in nested.stages.into_iter().rev() {
                                remaining.push_front(stage);
                            }
                            nested.source
                        }
                        None => {
                            if let Callback::Inline { body: returned, .. } = &stage.callback
                                && let Some((bindings, single)) = singleton(returned)
                            {
                                for bound in bindings {
                                    self.bindings(bound, body.body())?;
                                }
                                flow = self.value(single, body.body())?;
                                continue;
                            }
                            let produced =
                                self.callback_value(&stage.callback, vec![argument], body.body())?;
                            if remaining.is_empty() && matches!(need, Need::Value) {
                                return Ok(Opened { body, element: produced, index, spread: true });
                            }
                            Source::Array(produced)
                        }
                    };
                    let element = if needed_inputs(remaining.make_contiguous(), need)[0] {
                        self.element_name(remaining.make_contiguous(), 0, need)
                    } else {
                        "_".into()
                    };
                    let (header, prefix) =
                        self.header(source, Order::Forward, None, element.clone())?;
                    body.frames.push(Frame { header, body: prefix });
                    identifier_expression(&element)
                }
                StageKind::Scan => self.scan_step(&stage, flow, body.body())?,
            };
        }
        let element = match need {
            Need::Nothing => identifier_expression("_"),
            Need::Argument { callback, position } => {
                self.receive(flow, callback, position, true, body.body())?
            }
            Need::Variable { callback, position } => {
                self.receive(flow, callback, position, false, body.body())?
            }
            Need::Value => flow,
        };
        Ok(Opened { body, element, index, spread: false })
    }

    /// The loop over a source, handing the consumer `element` and, when it
    /// asks for it, the element's position as `index`.
    fn header(
        &mut self,
        source: Source<'_>,
        order: Order,
        index: Option<String>,
        element: String,
    ) -> GoResult<(Header, Vec<GoStatement>)> {
        let header = match (source, order) {
            (Source::Array(iterable), Order::Forward) => Header::Range { index, element, iterable },
            (Source::Array(array), Order::Backward) => Header::Backward { index, element, array },
            // A consumer that stores each element at its position counts positions.
            (Source::Range { first, last }, order) if index.is_some() => {
                let steps = Steps {
                    first: GoExpression::Integer(first),
                    step: GoExpression::Integer(1),
                    count: GoExpression::Integer(last - first + 1),
                };
                Header::Stepping { index, element, steps, order }
            }
            (Source::Range { first, last }, _) => {
                let variable = if element == "_" { self.temporary(VALUE) } else { element };
                Header::Counting { variable, first, last }
            }
            (Source::Stepping(steps), order) => Header::Stepping { index, element, steps, order },
            (Source::Replicate { count, value }, Order::Forward) => {
                let mut prefix = vec![];
                if element != "_" {
                    prefix.push(GoStatement::Define { names: vec![element], values: vec![value] });
                }
                return Ok((Header::Positions { index, count }, prefix));
            }
            (Source::Zip(zip), Order::Forward) => {
                if element == "_" {
                    return Ok((Header::Positions { index, count: zip.count }, vec![]));
                }
                let index = index.unwrap_or_else(|| self.temporary("index"));
                let mut prefix = vec![];
                let count = zip.count.clone();
                self.zip_element(*zip, &index, &element, &mut prefix)?;
                return Ok((Header::Positions { index: Some(index), count }, prefix));
            }
            (Source::Guard { condition, value }, Order::Forward) => {
                let mut prefix = vec![];
                if let Some(index) = index {
                    prefix.push(GoStatement::Define {
                        names: vec![index],
                        values: vec![GoExpression::Integer(0)],
                    });
                }
                if element != "_" {
                    prefix.push(GoStatement::Define { names: vec![element], values: vec![value] });
                }
                return Ok((Header::If(condition, None), prefix));
            }
            (Source::Replicate { .. } | Source::Zip(_) | Source::Guard { .. }, Order::Backward) => {
                unreachable!("invariant violated: generated arrays are read forwards")
            }
        };
        Ok((header, vec![]))
    }

    fn zip_element(
        &mut self,
        zip: Zip<'_>,
        index: &str,
        element: &str,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let Zip { operands, callback, produces, .. } = zip;
        let mut arguments = vec![];
        for (position, operand) in operands.into_iter().enumerate() {
            let flow = self.element_at(operand, index, body)?;
            arguments.push(self.receive(flow, &callback, position, true, body)?);
        }
        let sink = Sink::Define(element.to_string());
        self.apply_callback(&callback, arguments, produces, sink, body)
    }

    fn element_at(
        &mut self,
        pipeline: Pipeline<'_>,
        index: &str,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let Pipeline { source, stages, .. } = pipeline;
        let mut flow = match source {
            Source::Array(array) => GoExpression::Index {
                value: Box::new(array),
                index: Box::new(identifier_expression(index)),
            },
            Source::Range { first, .. } => {
                let step = GoExpression::Integer(1);
                let count = GoExpression::Integer(0);
                stepped_value(&Steps { first: GoExpression::Integer(first), step, count }, index)
            }
            Source::Stepping(steps) => stepped_value(&steps, index),
            Source::Replicate { value, .. } => value,
            Source::Guard { .. } => {
                unreachable!("invariant violated: a guard is not read by position")
            }
            Source::Zip(zip) => {
                let element = self.temporary("element");
                self.zip_element(*zip, index, &element, body)?;
                identifier_expression(&element)
            }
        };
        for stage in stages {
            flow = match stage.kind {
                StageKind::Map | StageKind::MapWithIndex if self.is_unit(stage.produces) => {
                    super::unit_value()
                }
                StageKind::Map | StageKind::MapWithIndex => {
                    let mut arguments = vec![];
                    if stage.kind == StageKind::MapWithIndex {
                        arguments.push(self.receive_index(&stage.callback, index, body));
                    }
                    let position = arguments.len();
                    arguments.push(self.receive(flow, &stage.callback, position, true, body)?);
                    self.callback_value(&stage.callback, arguments, body)?
                }
                StageKind::Scan => self.scan_step(&stage, flow, body)?,
                StageKind::Filter | StageKind::Bind => {
                    unreachable!("invariant violated: a positional pipeline keeps positions")
                }
            };
        }
        Ok(flow)
    }

    fn scan_step(
        &mut self,
        stage: &Stage<'_>,
        flow: GoExpression,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let state = stage.state.clone().expect("invariant violated: a scan stage has a state");
        let accumulated = match &stage.callback {
            Callback::Inline { .. } => {
                let parameter = self.loop_variable(&stage.callback, 0, "accumulated");
                if parameter != "_" {
                    body.push(GoStatement::Define {
                        names: vec![parameter.clone()],
                        values: vec![identifier_expression(&state)],
                    });
                }
                identifier_expression(&parameter)
            }
            Callback::Direct { .. } => identifier_expression(&state),
        };
        let argument = self.receive(flow, &stage.callback, 1, true, body)?;
        let sink = Sink::Assign(state.clone());
        self.apply_callback(
            &stage.callback,
            vec![accumulated, argument],
            stage.produces,
            sink,
            body,
        )?;
        Ok(identifier_expression(&state))
    }

    /// Closes every frame of a loop into the statement that runs it.
    pub(super) fn close(&mut self, body: Loop) -> GoStatement {
        let mut inner: Vec<GoStatement> = vec![];
        for Frame { header, mut body } in body.frames.into_iter().rev() {
            body.append(&mut inner);
            let line = match &header {
                Header::If(_, line) => line.clone(),
                _ => None,
            };
            let statement = match header {
                Header::Range { index, element, iterable } => {
                    GoStatement::Range { index, element, iterable, body }
                }
                Header::Counting { variable, first, last } => GoStatement::Counting {
                    variable,
                    start: GoExpression::Integer(first),
                    end: GoExpression::Integer(last + 1),
                    body,
                },
                Header::Backward { index, element, array } => {
                    let index = index.unwrap_or_else(|| self.temporary("index"));
                    if element != "_" {
                        let indexed = GoExpression::Index {
                            value: Box::new(array.clone()),
                            index: Box::new(identifier_expression(&index)),
                        };
                        body.insert(
                            0,
                            GoStatement::Define { names: vec![element], values: vec![indexed] },
                        );
                    }
                    let last = binary("-", length(array), GoExpression::Integer(1));
                    GoStatement::CountingDown { variable: index, start: last, body }
                }
                Header::Stepping { index, element, steps, order } => {
                    let counted = element != "_" || order == Order::Backward;
                    let index = index.or_else(|| counted.then(|| self.temporary("index")));
                    if let Some(index) = index.as_deref().filter(|_| element != "_") {
                        let values = vec![stepped_value(&steps, index)];
                        body.insert(0, GoStatement::Define { names: vec![element], values });
                    }
                    match (order, index) {
                        (Order::Backward, Some(variable)) => {
                            let start = match steps.count {
                                GoExpression::Integer(count) => GoExpression::Integer(count - 1),
                                count => binary("-", count, GoExpression::Integer(1)),
                            };
                            GoStatement::CountingDown { variable, start, body }
                        }
                        (_, index) => {
                            let (element, iterable) = ("_".into(), steps.count);
                            GoStatement::Range { index, element, iterable, body }
                        }
                    }
                }
                Header::Positions { index, count } => {
                    GoStatement::Range { index, element: "_".into(), iterable: count, body }
                }
                Header::If(condition, _) => {
                    GoStatement::If { condition, then: body, otherwise: vec![] }
                }
            };
            lines::push_at(line, statement, &mut inner);
        }
        inner.pop().expect("invariant violated: a loop has a frame")
    }

    /// The argument a callback takes for the element in `flow`, bound to a
    /// variable unless it is already one or is read once, as an argument.
    fn receive(
        &mut self,
        flow: GoExpression,
        callback: &Callback<'_>,
        position: usize,
        once: bool,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let parameter = match callback {
            Callback::Inline { parameters, body: callback_body } => {
                let parameter = parameters[position];
                if !uses_local(callback_body, parameter.id) && once {
                    return Ok(flow);
                }
                Some(parameter)
            }
            Callback::Direct { .. } => None,
        };
        if is_simple(&flow) {
            if let Some(parameter) = parameter {
                self.locals.insert(parameter.id, flow.clone());
            }
            return Ok(flow);
        }
        let name = match parameter {
            Some(parameter) => self.bind_local(parameter),
            None if once => return Ok(flow),
            None => self.temporary("element"),
        };
        body.push(GoStatement::Define { names: vec![name.clone()], values: vec![flow] });
        Ok(identifier_expression(&name))
    }

    fn receive_index(
        &mut self,
        callback: &Callback<'_>,
        index: &str,
        body: &mut Vec<GoStatement>,
    ) -> GoExpression {
        let position = identifier_expression(index);
        match callback {
            Callback::Inline { parameters, body: callback_body } => {
                if !uses_local(callback_body, parameters[0].id) {
                    return identifier_expression("_");
                }
                let name = self.bind_local(parameters[0]);
                body.push(GoStatement::Define {
                    names: vec![name.clone()],
                    values: vec![position],
                });
                identifier_expression(&name)
            }
            Callback::Direct { .. } => position,
        }
    }

    /// A name for the elements entering stage `position`: the parameter of the
    /// first callback that reads them, or a fresh `element`.
    fn element_name(
        &mut self,
        stages: &[Stage<'_>],
        position: usize,
        need: Need<'_, '_>,
    ) -> String {
        for stage in &stages[position..] {
            let Callback::Inline { parameters, body } = &stage.callback else {
                return self.temporary("element");
            };
            let parameter = parameters[element_position(stage.kind)];
            if uses_local(body, parameter.id) {
                return self.bind_local(parameter);
            }
            if stage.kind != StageKind::Filter {
                return self.temporary("element");
            }
        }
        match need {
            Need::Argument { callback: Callback::Inline { parameters, body }, position }
                if uses_local(body, parameters[position].id) =>
            {
                self.bind_local(parameters[position])
            }
            Need::Variable { callback: Callback::Inline { parameters, .. }, position } => {
                self.bind_local(parameters[position])
            }
            _ => self.temporary("element"),
        }
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// A callback whose leading arguments are evaluated now, once.
    pub(super) fn capture<'e>(
        &mut self,
        found: Found<'e>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Callback<'e>> {
        Ok(match found {
            Found::Inline { parameters, body } => Callback::Inline { parameters, body },
            Found::Direct { function, callee, leading } => {
                let mut values = vec![];
                for argument in leading {
                    let base = self.value_base(argument.monotype);
                    let value = self.value(argument, out)?;
                    values.push(self.hoist(value, &base, out));
                }
                Callback::Direct { function, callee, leading: values }
            }
        })
    }

    pub(super) fn built(
        &mut self,
        array: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Option<GoExpression>> {
        self.built_with_spare(array, 0, out)
    }

    /// The array a zip, a scan or a literal prefix of a fused pipeline builds, with room for
    /// `spare` more elements when its length is known.
    pub(super) fn built_with_spare(
        &mut self,
        array: &Expression,
        spare: usize,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Option<GoExpression>> {
        let ExpressionKind::Foreign { foreign, arguments } = &array.kind else { return Ok(None) };
        if !matches!(self.monotypes.get(array.monotype), Monotype::Array(_)) {
            return Ok(None);
        }
        let zipped = matches!(self.generated(array), Some(Generated::Zip { .. }));
        if zipped
            && let Some(vectorised) =
                self.vectorised(Iteration::ZipWith, arguments, array.monotype, out)?
        {
            return Ok(Some(vectorised));
        }
        let scanned =
            foreign.calls(ARRAY_SCANL) && self.stage_parts(array, Demand::FORWARD, false).is_some();
        if zipped || scanned {
            let pipeline = self.pipeline(array, Demand::FORWARD, Need::Value, out)?;
            return self.materialized(pipeline, vec![], spare, array.monotype, out).map(Some);
        }
        if foreign.calls(ARRAY_APPEND)
            && let [prefix, rest] = arguments.as_slice()
            && let ExpressionKind::Array(elements) = &prefix.kind
            && !self.owned_snocs.contains(&std::ptr::from_ref(prefix))
            && self.is_fusible(rest, Demand::FORWARD)
        {
            let mut values = vec![];
            for element in elements {
                let value = self.value(element, out)?;
                // A slot of the built array gives a constant its type.
                let value = if is_settled(&value) {
                    value
                } else {
                    let value = self.typed_constant(value, element.monotype)?;
                    self.hoist(value, "first", out)
                };
                values.push(value);
            }
            let pipeline = self.pipeline(rest, Demand::FORWARD, Need::Value, out)?;
            return self.materialized(pipeline, values, spare, array.monotype, out).map(Some);
        }
        Ok(None)
    }

    fn materialized(
        &mut self,
        pipeline: Pipeline<'_>,
        prefix: Vec<GoExpression>,
        spare: usize,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let array_type = self.go_type(monotype)?;
        let built = self.temporary("built");
        let offset = prefix.len();
        let known = pipeline.count();
        let plus = |count: &GoExpression, more: usize| match (more, count) {
            (0, count) => count.clone(),
            (more, GoExpression::Integer(count)) => GoExpression::Integer(count + more as i64),
            (more, count) => binary("+", count.clone(), GoExpression::Integer(more as i64)),
        };
        let allocation = match &known {
            Some(count) => {
                let mut arguments = vec![GoExpression::Type(array_type), plus(count, offset)];
                if spare > 0 {
                    arguments.push(plus(count, offset + spare));
                }
                call(identifier_expression("make"), arguments)
            }
            None => {
                let fields = prefix.iter().map(|value| (None, value.clone())).collect();
                GoExpression::Composite { type_: array_type, fields }
            }
        };
        out.push(GoStatement::Define { names: vec![built.clone()], values: vec![allocation] });
        if known.is_some() {
            let slot = |position: usize| indexed(&built, GoExpression::Integer(position as i64));
            if prefix.len() <= PREFIX_ON_ONE_LINE {
                let targets = (0..prefix.len()).map(slot).collect();
                if !prefix.is_empty() {
                    out.push(GoStatement::Assign { targets, values: prefix });
                }
            } else {
                for (position, value) in prefix.into_iter().enumerate() {
                    out.push(GoStatement::Assign {
                        targets: vec![slot(position)],
                        values: vec![value],
                    });
                }
            }
        }
        let saved = self.tail_loop.take();
        let opened = self.open(pipeline, Need::Value, known.is_some().then_some("index"));
        self.tail_loop = saved;
        let mut opened = opened?;
        let stored = match &opened.index {
            Some(index) => {
                let slot = match offset {
                    0 => identifier_expression(index),
                    offset => binary(
                        "+",
                        identifier_expression(index),
                        GoExpression::Integer(offset as i64),
                    ),
                };
                GoStatement::Assign {
                    targets: vec![indexed(&built, slot)],
                    values: vec![opened.element],
                }
            }
            None => {
                let element = if opened.spread {
                    GoExpression::Spread(Box::new(opened.element))
                } else {
                    opened.element
                };
                let appended = call(
                    identifier_expression("append"),
                    vec![identifier_expression(&built), element],
                );
                GoStatement::Assign {
                    targets: vec![identifier_expression(&built)],
                    values: vec![appended],
                }
            }
        };
        opened.body.body().push(stored);
        let statement = self.close(opened.body);
        out.push(statement);
        Ok(identifier_expression(&built))
    }

    /// Performs an effect for every element of a pipeline, running its stages
    /// in the loop instead of building the arrays between them. The effects
    /// run in the pipeline's order, and the stages' callbacks are pure, so
    /// interleaving them with the effects is not observable.
    pub(super) fn each_fused(
        &mut self,
        array: &Expression,
        element: &Local,
        body: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let callback = Callback::Inline { parameters: vec![element], body };
        let need = Need::Argument { callback: &callback, position: 0 };
        let pipeline = self.pipeline(array, Demand::FORWARD, need, out)?;
        let saved = self.tail_loop.take();
        let opened = self.open(pipeline, need, None).and_then(|mut opened| {
            self.sink(body, Mode::Perform, Sink::Discard, opened.body.body())?;
            Ok(opened)
        });
        self.tail_loop = saved;
        let statement = self.close(opened?.body);
        out.push(statement);
        Ok(())
    }

    /// The number of elements a pipeline produces, counted without building them.
    pub(super) fn fused_length(
        &mut self,
        array: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let pipeline = self.pipeline(array, Demand::FORWARD, Need::Nothing, out)?;
        if let Some(known) = pipeline.known_length() {
            return Ok(known);
        }
        let count = self.temporary("count");
        out.push(self.define(count.clone(), GoExpression::Integer(0), monotype)?);
        let saved = self.tail_loop.take();
        let opened = self.open(pipeline, Need::Nothing, None);
        self.tail_loop = saved;
        let mut opened = opened?;
        opened.body.body().push(GoStatement::Assign {
            targets: vec![identifier_expression(&count)],
            values: vec![binary("+", identifier_expression(&count), GoExpression::Integer(1))],
        });
        let statement = self.close(opened.body);
        out.push(statement);
        Ok(identifier_expression(&count))
    }
}

/// Whether the elements entering each stage, and finally the consumer, are read.
fn needed_inputs(stages: &[Stage<'_>], need: Need<'_, '_>) -> Vec<bool> {
    let mut needed = vec![false; stages.len() + 1];
    needed[stages.len()] = need.reads();
    for (position, stage) in stages.iter().enumerate().rev() {
        let reads = stage.callback.reads(element_position(stage.kind));
        needed[position] = match stage.kind {
            StageKind::Map | StageKind::MapWithIndex | StageKind::Scan => {
                needed[position + 1] && reads
            }
            StageKind::Filter => reads || needed[position + 1],
            StageKind::Bind => reads,
        };
    }
    needed
}

/// Whether what a stage produces can be handed on as an expression: its only
/// reader takes it as one argument of a call.
fn takes_expression(downstream: &[Stage<'_>], need: Need<'_, '_>) -> bool {
    match downstream.first() {
        Some(stage) => {
            stage.kind != StageKind::Filter && matches!(stage.callback, Callback::Direct { .. })
        }
        None => {
            matches!(need, Need::Argument { callback: Callback::Direct { .. }, .. } | Need::Value)
        }
    }
}

fn element_position(kind: StageKind) -> usize {
    match kind {
        StageKind::MapWithIndex | StageKind::Scan => 1,
        _ => 0,
    }
}

enum Generated<'e> {
    Replicate { count: &'e Expression, value: &'e Expression },
    Zip { callback: Found<'e>, operands: Vec<&'e Expression> },
}

fn indexed(array: &str, slot: GoExpression) -> GoExpression {
    GoExpression::Index { value: Box::new(identifier_expression(array)), index: Box::new(slot) }
}

fn past_bindings(mut expression: &Expression) -> &Expression {
    while let ExpressionKind::Let { body, .. } = &expression.kind {
        expression = body;
    }
    expression
}

/// The element at `index` of a range: `first + index*step`, which wraps like the range's own
/// arithmetic.
fn stepped_value(steps: &Steps, index: &str) -> GoExpression {
    let position = identifier_expression(index);
    let offset = match steps.step {
        GoExpression::Integer(1) => position,
        GoExpression::Integer(-1) => return binary("-", steps.first.clone(), position),
        _ => binary("*", position, steps.step.clone()),
    };
    match steps.first {
        GoExpression::Integer(0) => offset,
        _ => binary("+", steps.first.clone(), offset),
    }
}

/// Whether the value is Go's `len` of something, converted or not, which is never negative.
fn is_go_length(value: &GoExpression) -> bool {
    match value {
        GoExpression::Conversion { value, .. } => is_go_length(value),
        GoExpression::Call { function, .. } => {
            matches!(&**function, GoExpression::Identifier(name) if name == "len")
        }
        _ => false,
    }
}

/// Whether the value is a constant, a local, or a composite of them, which reads the same
/// wherever it is written.
fn is_settled(value: &GoExpression) -> bool {
    match value {
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_) => true,
        GoExpression::Unary { operator: "-", operand } => is_settled(operand),
        GoExpression::Composite { fields, .. } => fields.iter().all(|(_, field)| is_settled(field)),
        _ => false,
    }
}

/// The bounds of `first .. last`.
fn range_bounds(array: &Expression) -> Option<(&Expression, &Expression)> {
    let ExpressionKind::Foreign { foreign: Foreign::Range, arguments } = &array.kind else {
        return None;
    };
    let [first, last] = arguments.as_slice() else { return None };
    Some((first, last))
}

/// `first .. last` with literal bounds that count up.
fn literal_range(array: &Expression) -> Option<(i64, i64)> {
    let (first, last) = range_bounds(array)?;
    let (first, last) = literal_bounds(first, last)?;
    (first <= last && last < i64::from(i32::MAX)).then_some((first, last))
}

fn literal_bounds(first: &Expression, last: &Expression) -> Option<(i64, i64)> {
    let (ExpressionKind::Literal(Literal::Int(first)), ExpressionKind::Literal(Literal::Int(last))) =
        (&first.kind, &last.kind)
    else {
        return None;
    };
    Some((*first, *last))
}

fn singleton(mut expression: &Expression) -> Option<(Vec<&[Binding]>, &Expression)> {
    let mut bindings = vec![];
    while let ExpressionKind::Let { bindings: bound, body } = &expression.kind {
        bindings.push(bound.as_slice());
        expression = body;
    }
    match &expression.kind {
        ExpressionKind::Array(elements) => match elements.as_slice() {
            [element] => Some((bindings, element)),
            _ => None,
        },
        _ => None,
    }
}

fn body(alternative: &Alternative) -> Option<&Expression> {
    match &alternative.body {
        Guarded::Unconditional(body) => Some(body),
        Guarded::Guards(_) => None,
    }
}

fn choice(expression: &Expression) -> Option<(&Expression, &Expression, &Expression)> {
    match &expression.kind {
        ExpressionKind::If { condition, then, otherwise } => Some((condition, then, otherwise)),
        ExpressionKind::Case { scrutinees, alternatives } => {
            let ([scrutinee], [first, second]) = (scrutinees.as_slice(), alternatives.as_slice())
            else {
                return None;
            };
            let truth = |alternative: &Alternative| match alternative.patterns.as_slice() {
                [Pattern { kind: PatternKind::Literal(Literal::Boolean(truth)), .. }] => {
                    Some(Some(*truth))
                }
                [Pattern { kind: PatternKind::Wildcard, .. }] => Some(None),
                _ => None,
            };
            match (truth(first)?, truth(second)?) {
                (Some(true), Some(false) | None) => Some((scrutinee, body(first)?, body(second)?)),
                (Some(false), Some(true) | None) => Some((scrutinee, body(second)?, body(first)?)),
                _ => None,
            }
        }
        _ => None,
    }
}
