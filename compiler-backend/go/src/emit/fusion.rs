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
//! returns. A `first .. last` range with literal bounds needs no array at all.
//!
//! The callbacks are pure, so interleaving the stages is not observable. Each
//! callback still sees its elements in their order and is called for exactly
//! the elements it was before, except where nothing reads its result: a
//! `length` ignores what a `map` computes, and a consumer that stops early
//! leaves the remaining elements alone.

use super::iteration::Callback;
use super::{Emitter, Sink, binary, call, identifier_expression, is_simple, uses_local};
use crate::error::GoResult;
use crate::foreign::{Boundary, Foreign, Iteration};
use crate::mono::{Expression, ExpressionKind, Literal};
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement, GoType};

/// The stages between an array and the consumer that reads it.
pub(super) struct Pipeline<'e> {
    source: Source,
    /// Nearest the source first.
    stages: Vec<Stage<'e>>,
    order: Order,
}

enum Source {
    Array(GoExpression),
    /// `first .. last` counting up.
    Range { first: i64, last: i64 },
}

struct Stage<'e> {
    kind: StageKind,
    callback: Callback<'e>,
    /// The type of the elements the stage produces.
    produces: MonotypeId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StageKind {
    Map,
    MapWithIndex,
    Filter,
    Bind,
}

impl StageKind {
    fn keeps_positions(self) -> bool {
        matches!(self, StageKind::Map | StageKind::MapWithIndex)
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
}

impl Demand {
    pub(super) const FORWARD: Demand =
        Demand { order: Order::Forward, positions: false, breaks: false };
}

/// How a consumer reads the element its loop hands it.
#[derive(Clone, Copy)]
pub(super) enum Need<'c, 'e> {
    Nothing,
    /// As one argument of its callback.
    Argument { callback: &'c Callback<'e>, position: usize },
    /// As its callback's argument and once more besides.
    Variable { callback: &'c Callback<'e>, position: usize },
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
    If(GoExpression),
}

pub(super) struct Opened {
    pub body: Loop,
    /// The consumer's element, or `_` when it needs none.
    pub element: GoExpression,
    /// The element's position in the source, when the consumer asked for it.
    pub index: Option<String>,
}

impl Need<'_, '_> {
    fn reads(self) -> bool {
        match self {
            Need::Nothing => false,
            Need::Argument { callback, position } => callback.reads(position),
            Need::Variable { .. } => true,
        }
    }
}

impl Loop {
    pub(super) fn body(&mut self) -> &mut Vec<GoStatement> {
        &mut self.frames.last_mut().expect("invariant violated: a loop has a frame").body
    }
}

impl Pipeline<'_> {
    /// The source array, when every stage keeps the elements where they are.
    pub(super) fn positional_source(&self) -> Option<&GoExpression> {
        match &self.source {
            Source::Array(array) if self.keeps_positions() => Some(array),
            _ => None,
        }
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
        })
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// Whether `array` is a stage or a range that a consumer's loop can absorb.
    pub(super) fn is_fusible(&self, array: &Expression) -> bool {
        self.stage_parts(array, Demand::FORWARD, false).is_some()
            || literal_range(array).is_some()
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
        let mut found = vec![];
        let mut current = array;
        let mut positional = demand.positions || demand.order == Order::Backward;
        while let Some((kind, callback, inner)) = self.stage_parts(current, demand, positional) {
            positional |= kind == StageKind::MapWithIndex;
            let produces = match self.monotypes.get(current.monotype) {
                Monotype::Array(element) => *element,
                _ => unreachable!("invariant violated: an array stage produces an array"),
            };
            found.push((kind, callback, produces));
            current = inner;
        }
        // `found` runs from the consumer towards the source, as reads propagate.
        let mut read = need.reads();
        let mut running = vec![];
        for (kind, callback, _) in &found {
            let reads = callback.reads(element_position(*kind));
            let runs = !kind.keeps_positions() || read;
            read = match kind {
                StageKind::Map | StageKind::MapWithIndex => read && reads,
                StageKind::Filter => reads || read,
                StageKind::Bind => reads,
            };
            running.push(runs);
        }
        let mut stages = vec![];
        for ((kind, callback, produces), runs) in found.into_iter().zip(running) {
            if runs {
                let callback = self.capture(callback, out)?;
                stages.push(Stage { kind, callback, produces });
            }
        }
        stages.reverse();
        let range = literal_range(current).filter(|_| !positional);
        let source = match range {
            Some((first, last)) => Source::Range { first, last },
            None => {
                let value = self.value(current, out)?;
                Source::Array(self.hoist(value, "array", out))
            }
        };
        Ok(Pipeline { source, stages, order: demand.order })
    }

    fn stage_parts<'e>(
        &self,
        array: &'e Expression,
        demand: Demand,
        positional: bool,
    ) -> Option<(StageKind, super::iteration::Found<'e>, &'e Expression)> {
        let ExpressionKind::Foreign {
            foreign: Foreign::Call { boundary: Boundary { iteration: Some(iteration), .. }, .. },
            arguments,
        } = &array.kind
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
        if self.effect_after(callback.monotype, arity) {
            return None;
        }
        let found = self.callback(callback, arity)?;
        Some((kind, found, inner))
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
            stage.kind == StageKind::MapWithIndex
                && needed[position + 1]
                && stage.callback.reads(0)
        });
        let index = match index_base {
            Some(base) => Some(self.temporary(base)),
            None if stage_positions => Some(self.temporary("index")),
            None => None,
        };
        let header = match (source, order) {
            (Source::Array(array), Order::Forward) => {
                Header::Range { index: index.clone(), element: element.clone(), iterable: array }
            }
            (Source::Array(array), Order::Backward) => {
                Header::Backward { index: index.clone(), element: element.clone(), array }
            }
            (Source::Range { first, last }, _) => {
                let variable =
                    if element == "_" { self.temporary("value") } else { element.clone() };
                Header::Counting { variable, first, last }
            }
        };
        let mut body = Loop { frames: vec![Frame { header, body: vec![] }] };
        let mut flow = identifier_expression(&element);
        for (position, stage) in stages.iter().enumerate() {
            let downstream = needed[position + 1];
            flow = match stage.kind {
                StageKind::Map | StageKind::MapWithIndex => {
                    if self.is_unit(stage.produces) {
                        super::unit_value()
                    } else {
                        let mut arguments = vec![];
                        if stage.kind == StageKind::MapWithIndex {
                            let index = index.as_deref().unwrap_or("_");
                            arguments.push(self.receive_index(&stage.callback, index, body.body()));
                        }
                        let element_position = arguments.len();
                        let argument = self.receive(
                            flow,
                            &stage.callback,
                            element_position,
                            true,
                            body.body(),
                        )?;
                        arguments.push(argument);
                        if takes_expression(&stages[position + 1..], need) {
                            self.callback_value(&stage.callback, arguments, body.body())?
                        } else {
                            let name = self.element_name(&stages, position + 1, need);
                            let sink = Sink::Define(name.clone());
                            let produces = stage.produces;
                            self.apply_callback(
                                &stage.callback,
                                arguments,
                                produces,
                                sink,
                                body.body(),
                            )?;
                            identifier_expression(&name)
                        }
                    }
                }
                StageKind::Filter => {
                    let argument = self.receive(flow, &stage.callback, 0, !downstream, body.body())?;
                    let condition =
                        self.callback_value(&stage.callback, vec![argument.clone()], body.body())?;
                    body.frames.push(Frame { header: Header::If(condition), body: vec![] });
                    argument
                }
                StageKind::Bind => {
                    let argument = self.receive(flow, &stage.callback, 0, true, body.body())?;
                    let produced =
                        self.callback_value(&stage.callback, vec![argument], body.body())?;
                    let element = if downstream {
                        self.element_name(&stages, position + 1, need)
                    } else {
                        "_".into()
                    };
                    let header = Header::Range {
                        index: None,
                        element: element.clone(),
                        iterable: produced,
                    };
                    body.frames.push(Frame { header, body: vec![] });
                    identifier_expression(&element)
                }
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
        };
        Ok(Opened { body, element, index })
    }

    /// Closes every frame of a loop into the statement that runs it.
    pub(super) fn close(&mut self, body: Loop) -> GoStatement {
        let mut inner: Option<GoStatement> = None;
        for Frame { header, mut body } in body.frames.into_iter().rev() {
            body.extend(inner.take());
            inner = Some(match header {
                Header::Range { index, element, iterable } => {
                    GoStatement::Range { index, element, iterable, body }
                }
                Header::Counting { variable, first, last } => GoStatement::Counting {
                    variable,
                    start: GoExpression::Conversion {
                        type_: GoType::Named("int32".into()),
                        value: Box::new(GoExpression::Integer(first)),
                    },
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
                Header::If(condition) => {
                    GoStatement::If { condition, then: body, otherwise: vec![] }
                }
            });
        }
        inner.expect("invariant violated: a loop has a frame")
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
        let position = GoExpression::Conversion {
            type_: GoType::Named("int32".into()),
            value: Box::new(identifier_expression(index)),
        };
        match callback {
            Callback::Inline { parameters, body: callback_body } => {
                if !uses_local(callback_body, parameters[0].id) {
                    return identifier_expression("_");
                }
                let name = self.bind_local(parameters[0]);
                body.push(GoStatement::Define { names: vec![name.clone()], values: vec![position] });
                identifier_expression(&name)
            }
            Callback::Direct { .. } => position,
        }
    }

    /// A name for the elements entering stage `position`: the parameter of the
    /// first callback that reads them, or a fresh `element`.
    fn element_name(&mut self, stages: &[Stage<'_>], position: usize, need: Need<'_, '_>) -> String {
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
        found: super::iteration::Found<'e>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Callback<'e>> {
        use super::iteration::Found;
        Ok(match found {
            Found::Inline { parameters, body } => Callback::Inline { parameters, body },
            Found::Direct { function, callee, leading } => {
                let mut values = vec![];
                for argument in leading {
                    let value = self.value(argument, out)?;
                    values.push(self.hoist(value, "argument", out));
                }
                Callback::Direct { function, callee, leading: values }
            }
        })
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
            return Ok(match known {
                GoExpression::Integer(count) => GoExpression::Integer(count),
                known => GoExpression::Conversion {
                    type_: GoType::Named("int32".into()),
                    value: Box::new(known),
                },
            });
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
            StageKind::Map | StageKind::MapWithIndex => needed[position + 1] && reads,
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
        None => matches!(need, Need::Argument { callback: Callback::Direct { .. }, .. }),
    }
}

fn element_position(kind: StageKind) -> usize {
    match kind {
        StageKind::MapWithIndex => 1,
        _ => 0,
    }
}

/// `first .. last` with literal bounds that count up.
fn literal_range(array: &Expression) -> Option<(i64, i64)> {
    let ExpressionKind::Foreign { foreign: Foreign::Range, arguments } = &array.kind else {
        return None;
    };
    let [first, last] = arguments.as_slice() else { return None };
    let (ExpressionKind::Literal(Literal::Int(first)), ExpressionKind::Literal(Literal::Int(last))) =
        (&first.kind, &last.kind)
    else {
        return None;
    };
    (first <= last && *last < i64::from(i32::MAX)).then_some((*first, *last))
}

fn length(array: GoExpression) -> GoExpression {
    call(identifier_expression("len"), vec![array])
}
