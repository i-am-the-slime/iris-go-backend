use rustc_hash::{FxHashMap, FxHashSet};

use crate::foreign::{Foreign, Spelled};
use crate::mono::{Expression, ExpressionKind, Function, FunctionId, Program};
use crate::monotype::{Monotype, MonotypeId, Monotypes};
use crate::simplify::{
    KnownFunctions, does_no_work, for_each_child, function_references,
    strongly_connected_components,
};

const ROUNDS: usize = 16;

#[derive(Debug, Default, Clone)]
pub struct Arities {
    widened: FxHashMap<MonotypeId, usize>,
}

impl Arities {
    pub fn of(&self, monotype: MonotypeId) -> usize {
        self.widened.get(&monotype).copied().unwrap_or(1)
    }
}

pub fn choose(program: &Program, monotypes: &Monotypes) -> Arities {
    let known = Known::new(program);
    let mut uses = Uses::default();
    for function in &program.functions {
        uses.collect(&function.body, &known, monotypes);
    }
    let mut arities = Arities::default();
    let mut previous = None;
    for _ in 0..ROUNDS {
        let demand = uses.demand(&arities, monotypes);
        let caps = uses.caps(&arities, &known, monotypes);
        let next = widened(&demand, &caps, monotypes);
        if previous.as_ref() == Some(&next) {
            break;
        }
        arities.widened = next.clone();
        previous = Some(next);
    }
    loop {
        let caps = uses.caps(&arities, &known, monotypes);
        let mut changed = false;
        for (monotype, cap) in caps {
            if let Some(arity) = arities.widened.get_mut(&monotype)
                && cap < *arity
            {
                *arity = cap;
                changed = true;
            }
        }
        arities.widened.retain(|_, arity| *arity > 1);
        if !changed {
            break;
        }
    }
    if std::env::var_os("IRIS_GO_ARITY_STATISTICS").is_some() {
        uses.report(&arities, &known, monotypes);
    }
    arities
}

pub fn arrows(monotypes: &Monotypes, mut monotype: MonotypeId) -> usize {
    let mut count = 0;
    while let Monotype::Function(_, result) = monotypes.get(monotype) {
        count += 1;
        monotype = *result;
    }
    count
}

fn keeps_representation(foreign: &Foreign) -> bool {
    matches!(
        foreign,
        Foreign::Operator(_)
            | Foreign::UnsafeCoerce
            | Foreign::Identity
            | Foreign::Unit
            | Foreign::EffectPure
            | Foreign::EffectBind
            | Foreign::EffectMap
            | Foreign::RunEffect
            | Foreign::RecordGet
            | Foreign::ReferenceNew
            | Foreign::ReferenceRead
            | Foreign::ReferenceWrite
            | Foreign::ReferenceWriteThrough
            | Foreign::ReferenceModify
            | Foreign::LazyDefer
            | Foreign::LazyForce
    )
}

fn widened(
    demand: &FxHashMap<MonotypeId, usize>,
    caps: &FxHashMap<MonotypeId, usize>,
    monotypes: &Monotypes,
) -> FxHashMap<MonotypeId, usize> {
    demand
        .iter()
        .filter_map(|(&monotype, &arguments)| {
            let cap = caps.get(&monotype).copied().unwrap_or(usize::MAX);
            let arity = arguments.min(cap).min(arrows(monotypes, monotype));
            (arity > 1).then_some((monotype, arity))
        })
        .collect()
}

struct Known<'p> {
    program: &'p Program,
    recursive: Vec<bool>,
}

impl<'p> Known<'p> {
    fn new(program: &'p Program) -> Known<'p> {
        let references: Vec<FxHashSet<FunctionId>> =
            program.functions.iter().map(|function| function_references(&function.body)).collect();
        let mut recursive = vec![false; program.functions.len()];
        for component in strongly_connected_components(&references) {
            let cyclic =
                component.len() > 1 || references[component[0].0 as usize].contains(&component[0]);
            for function in component {
                recursive[function.0 as usize] = cyclic;
            }
        }
        Known { program, recursive }
    }

    fn parameters(&self, id: FunctionId) -> usize {
        self.program.function(id).parameters.len()
    }
}

impl KnownFunctions for Known<'_> {
    fn known(&self, id: FunctionId) -> Option<&Function> {
        Some(self.program.function(id))
    }

    fn is_recursive(&self, id: FunctionId) -> bool {
        self.recursive[id.0 as usize]
    }
}

#[derive(Default)]
struct Uses<'p> {
    calls: Vec<(MonotypeId, usize)>,
    creations: Vec<&'p Expression>,
    foreign: FxHashSet<MonotypeId>,
}

impl<'p> Uses<'p> {
    fn collect(&mut self, expression: &'p Expression, known: &Known<'_>, monotypes: &Monotypes) {
        match &expression.kind {
            ExpressionKind::Apply { function, arguments } => {
                match function.kind {
                    ExpressionKind::Function(id) if known.parameters(id) > 0 => {
                        let parameters = known.parameters(id);
                        if arguments.len() > parameters {
                            let result = monotypes.result_after(function.monotype, parameters);
                            self.calls.push((result, arguments.len() - parameters));
                        } else if arguments.len() < parameters {
                            self.creations.push(expression);
                        }
                    }
                    _ => {
                        self.calls.push((function.monotype, arguments.len()));
                        self.creations.push(expression);
                    }
                }
                if !matches!(function.kind, ExpressionKind::Function(_)) {
                    self.collect(function, known, monotypes);
                }
                for argument in arguments {
                    self.collect(argument, known, monotypes);
                }
                return;
            }
            ExpressionKind::Lambda { .. } => self.creations.push(expression),
            ExpressionKind::Function(id) if known.parameters(*id) > 0 => {
                self.creations.push(expression)
            }
            ExpressionKind::Coerce(value) if value.monotype != expression.monotype => {
                self.received(expression.monotype, monotypes);
            }
            ExpressionKind::Foreign { foreign, arguments } => match foreign {
                Foreign::Call { boundary, .. } | Foreign::Perform { boundary, .. } => {
                    for &(position, arity) in boundary.uncurried {
                        self.calls.push((arguments[position].monotype, arity));
                    }
                    let declared = boundary
                        .signature
                        .filter(|signature| signature.parameters.len() >= arguments.len());
                    match declared {
                        Some(signature) => {
                            for (argument, spelled) in arguments.iter().zip(&signature.parameters) {
                                self.spelled_callback(spelled, argument.monotype, monotypes);
                            }
                            let rest = signature.parameters.get(arguments.len()..).unwrap_or(&[]);
                            let result = &signature.result;
                            self.spelled_result(rest, result, expression.monotype, monotypes);
                        }
                        None => self.exchanged(arguments, expression.monotype, monotypes),
                    }
                }
                foreign if keeps_representation(foreign) => {}
                _ => self.exchanged(arguments, expression.monotype, monotypes),
            },
            _ => {}
        }
        for_each_child(expression, &mut |child| self.collect(child, known, monotypes));
    }

    fn exchanged(&mut self, arguments: &[Expression], result: MonotypeId, monotypes: &Monotypes) {
        self.received(result, monotypes);
        for argument in arguments {
            self.sent(argument.monotype, monotypes);
        }
    }

    fn spelled_callback(&mut self, spelled: &Spelled, monotype: MonotypeId, monotypes: &Monotypes) {
        match (spelled, monotypes.get(monotype)) {
            (Spelled::Function(parameter, rest), Monotype::Function(argument, result)) => {
                self.spelled_received(parameter, *argument, monotypes);
                self.spelled_callback(rest, *result, monotypes);
            }
            _ => self.spelled_sent(spelled, monotype, monotypes),
        }
    }

    fn spelled_result(
        &mut self,
        parameters: &[Spelled],
        result: &Spelled,
        monotype: MonotypeId,
        monotypes: &Monotypes,
    ) {
        let Some((parameter, rest)) = parameters.split_first() else {
            return self.spelled_received(result, monotype, monotypes);
        };
        if let Monotype::Function(argument, inner) = monotypes.get(monotype) {
            self.foreign.insert(monotype);
            self.spelled_sent(parameter, *argument, monotypes);
            self.spelled_result(rest, result, *inner, monotypes);
        }
    }

    fn spelled_received(&mut self, spelled: &Spelled, monotype: MonotypeId, monotypes: &Monotypes) {
        match (spelled, monotypes.get(monotype)) {
            (Spelled::Function(parameter, rest), Monotype::Function(argument, result)) => {
                self.foreign.insert(monotype);
                self.spelled_sent(parameter, *argument, monotypes);
                self.spelled_received(rest, *result, monotypes);
            }
            (Spelled::Array(element), Monotype::Array(inner))
            | (Spelled::Effect(element), Monotype::Effect(inner)) => {
                self.spelled_received(element, *inner, monotypes)
            }
            _ => {}
        }
    }

    fn spelled_sent(&mut self, spelled: &Spelled, monotype: MonotypeId, monotypes: &Monotypes) {
        match (spelled, monotypes.get(monotype)) {
            (Spelled::Function(parameter, rest), Monotype::Function(argument, result)) => {
                self.foreign.insert(monotype);
                self.spelled_received(parameter, *argument, monotypes);
                self.spelled_sent(rest, *result, monotypes);
            }
            (Spelled::Array(element), Monotype::Array(inner))
            | (Spelled::Effect(element), Monotype::Effect(inner)) => {
                self.spelled_sent(element, *inner, monotypes)
            }
            _ => {}
        }
    }

    fn received(&mut self, monotype: MonotypeId, monotypes: &Monotypes) {
        match monotypes.get(monotype) {
            Monotype::Function(argument, result) => {
                if self.foreign.insert(monotype) {
                    self.sent(*argument, monotypes);
                    self.received(*result, monotypes);
                }
            }
            Monotype::Effect(inner)
            | Monotype::Array(inner)
            | Monotype::MutableArray(inner)
            | Monotype::Nullable(inner)
            | Monotype::Object(inner) => self.received(*inner, monotypes),
            Monotype::Record(fields) => {
                for field in fields.iter() {
                    self.received(field.monotype, monotypes);
                }
            }
            _ => {}
        }
    }

    fn sent(&mut self, monotype: MonotypeId, monotypes: &Monotypes) {
        match monotypes.get(monotype) {
            Monotype::Function(argument, result) => {
                self.received(*argument, monotypes);
                self.sent(*result, monotypes);
            }
            Monotype::Effect(inner)
            | Monotype::Array(inner)
            | Monotype::MutableArray(inner)
            | Monotype::Nullable(inner)
            | Monotype::Object(inner) => self.sent(*inner, monotypes),
            Monotype::Record(fields) => {
                for field in fields.iter() {
                    self.sent(field.monotype, monotypes);
                }
            }
            _ => {}
        }
    }

    fn demand(&self, arities: &Arities, monotypes: &Monotypes) -> FxHashMap<MonotypeId, usize> {
        let mut demand: FxHashMap<MonotypeId, usize> = FxHashMap::default();
        for &(monotype, arguments) in &self.calls {
            let mut monotype = monotype;
            let mut arguments = arguments;
            while arguments > 0 && monotypes.function_parts(monotype).is_some() {
                let wanted = demand.entry(monotype).or_insert(1);
                *wanted = (*wanted).max(arguments);
                let taken = arities.of(monotype).min(arguments);
                monotype = monotypes.result_after(monotype, taken);
                arguments -= taken;
            }
        }
        demand
    }

    fn caps(
        &self,
        arities: &Arities,
        known: &Known<'_>,
        monotypes: &Monotypes,
    ) -> FxHashMap<MonotypeId, usize> {
        let mut caps: FxHashMap<MonotypeId, usize> = FxHashMap::default();
        let mut limit = |monotype: MonotypeId, free: usize| {
            let cap = caps.entry(monotype).or_insert(usize::MAX);
            *cap = (*cap).min(free.max(1));
        };
        for &monotype in &self.foreign {
            limit(monotype, 1);
        }
        for creation in &self.creations {
            if monotypes.function_parts(creation.monotype).is_some()
                && let Some(free) = free(creation, arities, known, monotypes)
            {
                limit(creation.monotype, free);
            }
        }
        caps
    }

    fn report(&self, arities: &Arities, known: &Known<'_>, monotypes: &Monotypes) {
        let mut saturated = 0;
        let mut partial = 0;
        let mut chained = 0;
        let mut curried_calls = 0;
        for &(monotype, arguments) in &self.calls {
            let arity = arities.of(monotype);
            if arguments > 1 {
                curried_calls += 1;
            }
            match arguments.cmp(&arity) {
                std::cmp::Ordering::Equal => saturated += 1,
                std::cmp::Ordering::Less => partial += 1,
                std::cmp::Ordering::Greater => chained += 1,
            }
        }
        let widened = arities.widened.len();
        let demand = self.demand(arities, monotypes);
        let wanted = demand.values().filter(|&&n| n > 1).count();
        let mut narrowed: FxHashMap<&'static str, usize> = FxHashMap::default();
        for (&monotype, &arguments) in &demand {
            let possible = arguments.min(arrows(monotypes, monotype));
            if arities.of(monotype) >= possible {
                continue;
            }
            let reason = if self.foreign.contains(&monotype) {
                "received from foreign code or a coercion"
            } else {
                self.creations
                    .iter()
                    .filter(|creation| creation.monotype == monotype)
                    .filter_map(|creation| {
                        let free = free(creation, arities, known, monotypes)?;
                        let kind = match creation.kind {
                            ExpressionKind::Lambda { .. } => {
                                "a lambda that works between parameters"
                            }
                            ExpressionKind::Function(_) => "a known function with fewer parameters",
                            _ => "a partial application",
                        };
                        (free < possible).then_some(kind)
                    })
                    .next()
                    .unwrap_or("a narrower result type")
            };
            *narrowed.entry(reason).or_insert(0) += 1;
        }
        eprintln!("arity: narrowed {narrowed:?}");
        eprintln!(
            "arity: {} value call sites: {saturated} saturated, {partial} partial, {chained} \
             over-applied ({curried_calls} pass several arguments); {widened} of {wanted} \
             function types called with several arguments take them together",
            self.calls.len()
        );
    }
}

fn free(
    expression: &Expression,
    arities: &Arities,
    known: &Known<'_>,
    monotypes: &Monotypes,
) -> Option<usize> {
    match &expression.kind {
        ExpressionKind::Lambda { parameters, body } => {
            let rest = if monotypes.function_parts(body.monotype).is_none() {
                0
            } else if let ExpressionKind::Lambda { .. } = body.kind {
                free(body, arities, known, monotypes).unwrap_or(0)
            } else if does_no_work(known, body) {
                free(body, arities, known, monotypes).unwrap_or(0)
            } else {
                0
            };
            Some(parameters.len() + rest)
        }
        ExpressionKind::Function(id) if known.parameters(*id) > 0 => Some(known.parameters(*id)),
        ExpressionKind::Apply { function, arguments } => match function.kind {
            ExpressionKind::Function(id) if known.parameters(id) > 0 => {
                let parameters = known.parameters(id);
                if arguments.len() < parameters {
                    return Some(parameters - arguments.len());
                }
                let result = monotypes.result_after(function.monotype, parameters);
                unsaturated(result, arguments.len() - parameters, arities, monotypes)
            }
            _ => unsaturated(function.monotype, arguments.len(), arities, monotypes),
        },
        ExpressionKind::Local(_) | ExpressionKind::Function(_) | ExpressionKind::Access { .. } => {
            Some(arities.of(expression.monotype))
        }
        _ => None,
    }
}

fn unsaturated(
    mut monotype: MonotypeId,
    mut arguments: usize,
    arities: &Arities,
    monotypes: &Monotypes,
) -> Option<usize> {
    while arguments > 0 {
        let arity = arities.of(monotype);
        if arguments < arity {
            return Some(arity - arguments);
        }
        arguments -= arity;
        monotype = monotypes.result_after(monotype, arity);
    }
    None
}
