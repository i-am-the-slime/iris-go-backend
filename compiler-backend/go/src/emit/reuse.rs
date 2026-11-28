mod emission;
mod facts;
mod plan;
mod planner;

use rustc_hash::FxHashSet;
use smol_str::SmolStr;

use super::Emitter;
use super::field_reads::hoist_field_reads;
use super::inspection::{inspecting_functions, sequence_inspections};
use crate::monomorphic::traversal::visit;
use crate::monomorphic::{Expression, ExpressionKind, FunctionId, Local, LocalId, Program};
use crate::monotype::{DataType, Monotype, MonotypeId};
use emission::Emission;
use facts::Facts;

/// What the name of a variant that reuses its arguments' cells adds to its
/// function's name.
pub(super) const REUSING: &str = "Reusing";

pub(super) const CHECKED: &str = "Checked";

pub(super) trait Cells {
    fn cell(&mut self, monotype: MonotypeId) -> Option<DataType>;
    fn is_spine(&mut self, cell: &DataType, field: MonotypeId) -> bool;
    fn is_effect(&self, monotype: MonotypeId) -> bool;
    fn holds(&mut self, monotype: MonotypeId, cell: &DataType) -> bool;
    fn erases(&mut self, monotype: MonotypeId) -> bool;
    fn is_suspended(&self, monotype: MonotypeId) -> bool;
    fn function_type(&mut self, parameters: &[MonotypeId], result: MonotypeId) -> MonotypeId;
    fn is_tracked(&mut self, cell: &DataType) -> bool;
    fn tracks(&mut self, cell: &DataType, constructor: usize, field: usize) -> bool;
    fn boolean(&mut self) -> MonotypeId;
    fn is_record(&self, monotype: MonotypeId) -> bool;
    /// The labels of a record's fields that are cells, or records with such fields, each with
    /// the cells it holds that way.
    fn cell_fields(&mut self, monotype: MonotypeId) -> Vec<(SmolStr, Vec<DataType>)>;
}

pub(super) struct Reused {
    pub program: Program,
    pub materialized: FxHashSet<(FunctionId, LocalId)>,
    pub candidates: FxHashSet<DataType>,
}

pub(super) fn reuse_cells(program: &Program, cells: &mut impl Cells) -> Reused {
    let inspecting = inspecting_functions(program);
    let hoisted = hoist_field_reads(program, cells);
    let sequenced = sequence_inspections(&hoisted, &inspecting, cells);
    let program = &sequenced;
    let mut facts = Facts::new(program, cells, inspecting);
    facts.settle(program, cells);
    Emission::new(program, facts).finish(cells)
}

pub(super) fn first_unused_local(program: &Program) -> u32 {
    let mut next_local = 0;
    for function in &program.functions {
        for parameter in &function.parameters {
            next_local = next_local.max(parameter.id.0 + 1);
        }
        visit(&function.body, &mut |expression| {
            next_local = next_local.max(highest_local(expression) + 1);
        });
    }
    next_local
}

fn highest_local(expression: &Expression) -> u32 {
    let mut highest = 0;
    let mut bind = |local: &Local| highest = highest.max(local.id.0);
    match &expression.kind {
        ExpressionKind::Local(id) => highest = id.0,
        ExpressionKind::Lambda { parameters, .. } => parameters.iter().for_each(&mut bind),
        ExpressionKind::Let { bindings, .. } => {
            bindings.iter().for_each(|binding| bind(&binding.local))
        }
        ExpressionKind::EffectBind { local, .. }
        | ExpressionKind::EffectEach { element: local, .. } => bind(local),
        ExpressionKind::Case { alternatives, .. } => {
            alternatives.iter().for_each(|alternative| alternative.for_each_local(&mut bind))
        }
        _ => {}
    }
    highest
}

impl<Q> Cells for Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    fn cell(&mut self, monotype: MonotypeId) -> Option<DataType> {
        let Monotype::Data(data) = self.monotypes.get(monotype).clone() else { return None };
        if let Some(&cell) = self.cell_types.get(&data) {
            return cell.then_some(data);
        }
        let cell = self.is_cell(&data);
        self.cell_types.insert(data.clone(), cell);
        cell.then_some(data)
    }

    fn is_spine(&mut self, cell: &DataType, field: MonotypeId) -> bool {
        let Some(child) = Cells::cell(self, field) else { return false };
        let key = (child.clone(), cell.clone());
        if let Some(&reaches) = self.reaching.get(&key) {
            return reaches;
        }
        let reaches = self.reaches(&child, cell).unwrap_or(false);
        self.reaching.insert(key, reaches);
        reaches
    }

    fn is_effect(&self, monotype: MonotypeId) -> bool {
        self.monotypes.effect_result(monotype).is_some()
    }

    fn is_suspended(&self, monotype: MonotypeId) -> bool {
        matches!(self.monotypes.get(monotype), Monotype::Lazy(_) | Monotype::Effect(_))
    }

    fn erases(&mut self, monotype: MonotypeId) -> bool {
        if let Some(&erases) = self.erasing.get(&monotype) {
            return erases;
        }
        self.erasing.insert(monotype, false);
        let erases = match self.monotypes.get(monotype).clone() {
            Monotype::Erased(_) | Monotype::Recursive(_) => true,
            Monotype::Data(data) => self.erases_arguments(&data).unwrap_or(true),
            Monotype::Function(argument, result) => {
                Cells::erases(self, argument) || Cells::erases(self, result)
            }
            Monotype::Record(fields) => {
                fields.iter().any(|field| Cells::erases(self, field.monotype))
            }
            container => container.element().is_some_and(|element| Cells::erases(self, element)),
        };
        self.erasing.insert(monotype, erases);
        erases
    }

    fn holds(&mut self, monotype: MonotypeId, cell: &DataType) -> bool {
        let key = (monotype, cell.clone());
        if let Some(&holds) = self.holding.get(&key) {
            return holds;
        }
        let mut pending = vec![monotype];
        let mut visited = FxHashSet::default();
        let mut holds = false;
        while let Some(monotype) = pending.pop() {
            if !visited.insert(monotype) {
                continue;
            }
            match self.monotypes.get(monotype).clone() {
                Monotype::Int
                | Monotype::Number
                | Monotype::Boolean
                | Monotype::Char
                | Monotype::String
                | Monotype::Unit
                | Monotype::BigInt
                | Monotype::Int64
                | Monotype::UInt64
                | Monotype::Regex => {}
                Monotype::Array(element)
                | Monotype::MutableArray(element)
                | Monotype::Nullable(element)
                | Monotype::ConsList(element)
                | Monotype::Object(element) => pending.push(element),
                Monotype::Record(fields) => {
                    pending.extend(fields.iter().map(|field| field.monotype));
                }
                Monotype::HashMap(key, value) | Monotype::OrderedMap(key, value) => {
                    pending.extend([key, value])
                }
                Monotype::Data(data) | Monotype::Recursive(data) if data == *cell => {
                    holds = true;
                }
                Monotype::Data(data) | Monotype::Recursive(data) => {
                    match self.constructor_fields(&data) {
                        Ok(fields) => pending.extend(fields),
                        Err(_) => holds = true,
                    }
                }
                _ => holds = true,
            }
            if holds {
                break;
            }
        }
        self.holding.insert(key, holds);
        holds
    }

    fn function_type(&mut self, parameters: &[MonotypeId], result: MonotypeId) -> MonotypeId {
        parameters
            .iter()
            .rev()
            .fold(result, |result, &parameter| self.monotypes.function(parameter, result))
    }

    fn is_tracked(&mut self, cell: &DataType) -> bool {
        self.edge_bits(cell).ok().flatten().is_some()
    }

    fn tracks(&mut self, cell: &DataType, constructor: usize, field: usize) -> bool {
        let bits = self.edge_bits(cell).ok().flatten();
        bits.is_some_and(|bits| bits.bit(constructor, field).is_some())
    }

    fn boolean(&mut self) -> MonotypeId {
        self.monotypes.intern(Monotype::Boolean)
    }

    fn is_record(&self, monotype: MonotypeId) -> bool {
        matches!(self.monotypes.get(monotype), Monotype::Record(_))
            && !self.monotypes.is_instantiated_record(monotype)
    }

    fn cell_fields(&mut self, monotype: MonotypeId) -> Vec<(SmolStr, Vec<DataType>)> {
        if !Cells::is_record(self, monotype) {
            return vec![];
        }
        let Monotype::Record(fields) = self.monotypes.get(monotype).clone() else { return vec![] };
        let mut owning = vec![];
        for field in fields.iter() {
            let cells = match Cells::cell(self, field.monotype) {
                Some(cell) => vec![cell],
                None => Cells::cell_fields(self, field.monotype)
                    .into_iter()
                    .flat_map(|(_, cells)| cells)
                    .collect(),
            };
            if !cells.is_empty() {
                owning.push((field.label.clone(), cells));
            }
        }
        owning
    }
}
