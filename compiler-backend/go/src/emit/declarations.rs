use rustc_hash::FxHashSet;

use super::packages::Spelling;
use super::{
    Emitter, LoopTarget, Mode, Sink, TailLoop, buffers, call, captures_parameters, has_tail_call,
    identifier_expression, names, ownership, recycling, unit_value,
};
use crate::error::GoResult;
use crate::go_traversal::{self, Walk};
use crate::graph::{on_cycles, strongly_connected};
use crate::monomorphic::traversal::reference_graph;
use crate::monomorphic::{Expression, Function, FunctionId, Program};
use crate::monotype::{Monotype, Monotypes};
use crate::naming::identifier;
use crate::syntax::{GoDeclaration, GoExpression, GoPackage, GoQualifier, GoStatement};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn assign_function_names(&mut self) {
        let entry = self.program.entry;
        let entry_function = self.program.function(entry);
        let entry_is_procedure = entry_function.parameters.is_empty()
            && matches!(self.monotypes.get(entry_function.result), Monotype::Effect(result)
                if matches!(self.monotypes.get(*result), Monotype::Unit));
        for (index, function) in self.program.functions.iter().enumerate() {
            let name = if FunctionId(index as u32) == entry && entry_is_procedure {
                self.global_names.insert("main".into());
                "main".to_string()
            } else {
                let full = identifier(&function.name);
                match self.function_parts(&function.name) {
                    Ok(Some(parts)) => {
                        self.pending_global(full, names::PendingSpelling::Parts(parts))
                    }
                    Ok(None) | Err(_) => self.global_name(Spelling::Base(full)),
                }
            };
            self.function_names.push(name);
        }
    }

    pub(super) fn main(&mut self) -> GoResult<Option<GoDeclaration>> {
        let entry = self.program.entry;
        let name = self.function_names[entry.0 as usize].clone();
        if name == "main" {
            return Ok(None);
        }
        let function = self.program.function(entry);
        let status = self.monotypes.effect_result(function.result);
        let body = if function.parameters.is_empty()
            && let Some(status) = status
            && let Monotype::Int = self.monotypes.get(status)
        {
            // Like an embedded host running an `Effect Int`, the program's
            // result is its exit status.
            self.import(GoPackage::Os);
            self.effects.insert((GoQualifier::Package(GoPackage::Os), "Exit".into()));
            let exit = GoExpression::qualified(GoPackage::Os, "Exit");
            let status = call(identifier_expression(&name), vec![]);
            vec![GoStatement::Expression(call(exit, vec![status]))]
        } else if function.parameters.is_empty()
            && let Monotype::Effect(_) = self.monotypes.get(function.result)
        {
            vec![GoStatement::Expression(call(identifier_expression(&name), vec![]))]
        } else if let [parameter] = &function.parameters[..]
            && let Monotype::Unit = self.monotypes.get(parameter.monotype)
            && let Monotype::Unit = self.monotypes.get(function.result)
        {
            // A `Unit -> Unit` entry (the prelude tests' `AlmostEff`) runs, as JavaScript's
            // `main()` does, instead of printing a function's address.
            vec![GoStatement::Expression(call(identifier_expression(&name), vec![unit_value()]))]
        } else if !function.parameters.is_empty() {
            // Nothing runs a function that takes arguments, and printing it would print only
            // its address, so it is only kept.
            vec![GoStatement::Assign {
                targets: vec![identifier_expression("_")],
                values: vec![identifier_expression(&name)],
            }]
        } else if let Some(printing) = self.print_entry_value(&name, function.result) {
            printing
        } else {
            // A record, a data type or a function has no text to print, so it is only kept.
            let shown = self.purescript_type(function.result)?;
            self.notes.push(format!(
                "the entry's value of type {shown} is not printed; use an Effect entry or a \
                 value of a printable type (Int, Number, Boolean, Char, String or an Array of them)"
            ));
            vec![GoStatement::Assign {
                targets: vec![identifier_expression("_")],
                values: vec![identifier_expression(&name)],
            }]
        };
        let mut body = body;
        self.name_definition(self.program.function(entry).position, &mut body)?;
        Ok(Some(GoDeclaration::Function {
            name: "main".into(),
            parameters: vec![],
            result: None,
            body,
        }))
    }

    pub(super) fn pending_variants(
        &mut self,
        declarations: &mut Vec<GoDeclaration>,
    ) -> GoResult<()> {
        loop {
            let (id, emitted) = if let Some((id, position)) = self.pending_owning_variants.pop() {
                (id, self.owning_variant(id, position)?)
            } else if let Some(id) = self.pending_writers.pop() {
                (id, self.writer(id)?)
            } else if let Some(id) = self.pending_array_writers.pop() {
                (id, self.array_writer_declaration(id)?)
            } else if let Some(id) = self.pending_array_shows.pop() {
                (id, vec![self.array_show_declaration(id)?])
            } else {
                return Ok(());
            };
            self.note_homes(&emitted, self.program.function(id).origin);
            declarations.extend(emitted);
        }
    }

    pub(super) fn function(&mut self, id: FunctionId) -> GoResult<Vec<GoDeclaration>> {
        if let Some(&group) = self.tail_group_of.get(&id) {
            return self.tail_group_member(id, group);
        }
        let name = self.function_names[id.0 as usize].clone();
        self.function_named(id, name, vec![])
    }

    fn owning_variant(&mut self, id: FunctionId, position: usize) -> GoResult<Vec<GoDeclaration>> {
        let name = self.owning_variants[&(id, position)].clone();
        let function: &Function = self.program.function(id);
        let owned = self
            .owned_parameter_snocs(function, position)
            .into_iter()
            .flat_map(|(_, nodes)| nodes.into_iter().map(std::ptr::from_ref))
            .collect();
        self.function_named(id, name, owned)
    }

    fn function_named(
        &mut self,
        id: FunctionId,
        name: String,
        owned_parameters: Vec<*const Expression>,
    ) -> GoResult<Vec<GoDeclaration>> {
        let function: &Function = self.program.function(id);
        self.current = Some(id);
        self.locals.clear();
        self.local_names.clear();
        self.tail_loop = None;
        self.byte_buffers.clear();
        let mut parameters = vec![];
        for parameter in &function.parameters {
            let parameter_name = self.bind_local(parameter);
            let parameter_type = self.go_type(parameter.monotype)?;
            parameters.push((parameter_name, parameter_type));
        }
        let effect_result = self.monotypes.effect_result(function.result);
        let mode = if effect_result.is_some() { Mode::Perform } else { Mode::Value };
        if function.parameters.is_empty() && mode == Mode::Value {
            if self.lazy_constants.contains(&id) {
                return self.lazy_constant(&name, function);
            }
            return self.constant(&name, function);
        }
        let result = self.go_result(effect_result.unwrap_or(function.result))?;
        let loops = !function.parameters.is_empty()
            && has_tail_call(&function.body, id, function.parameters.len(), mode);
        let captured: Vec<usize> = if loops {
            (0..function.parameters.len())
                .filter(|&position| {
                    let parameter = std::slice::from_ref(&function.parameters[position]);
                    captures_parameters(&function.body, parameter, mode, self.monotypes)
                })
                .collect()
        } else {
            vec![]
        };
        // A string parameter that the loop only appends to grows in a `[]byte` of its own.
        let strings = if loops && mode == Mode::Value {
            self.owned_loop_strings(id, function, &captured)
        } else {
            vec![]
        };
        let mut buffers = vec![];
        for (position, _) in &strings {
            let parameter = &parameters[*position].0;
            let buffer = self.local_name(format!("{parameter}Bytes"));
            let local = function.parameters[*position].id;
            self.locals.insert(local, buffers::to_string(identifier_expression(&buffer)));
            self.byte_buffers.insert(local, buffer.clone());
            buffers.push((*position, buffer));
        }
        let mut iteration_copies = vec![];
        for &position in &captured {
            let copy = self.local_name(format!("{}Captured", parameters[position].0));
            self.locals.insert(function.parameters[position].id, identifier_expression(&copy));
            iteration_copies.push(GoStatement::Define {
                names: vec![copy],
                values: vec![identifier_expression(&parameters[position].0)],
            });
        }
        let owned = if loops {
            let mut owned = self.owned_loop_arrays(id, function, mode == Mode::Perform);
            owned.retain(|(position, _, _)| !captured.contains(position));
            owned
        } else {
            vec![]
        };
        let mut owned_nodes: Vec<*const Expression> =
            owned.iter().flat_map(|(_, _, nodes)| nodes.iter().copied()).collect();
        owned_nodes.extend(strings.into_iter().flat_map(|(_, nodes)| nodes));
        owned_nodes.extend(owned_parameters.iter().copied());
        self.owned_snocs.extend(owned_nodes.iter().copied());
        let mut owned_places: Vec<Vec<*const Expression>> =
            owned.iter().map(|(_, _, nodes)| nodes.clone()).collect();
        let flags = self.own_updates(&function.body, &owned_places);
        self.own_exclusive_updates(&function.body, &owned_parameters);
        owned_places.push(owned_parameters);
        let mut recycled_buffers = vec![];
        let mut recycled_positions = vec![];
        if loops && mode == Mode::Value {
            for (position, (parameter, type_)) in parameters.iter().enumerate() {
                if buffers.iter().any(|(buffered, _)| *buffered == position) {
                    continue;
                }
                let Some(maps) = self.recycled_maps(id, function, position) else { continue };
                recycled_positions.push(position);
                let recycled = recycling::Recycled {
                    owned: self.local_name(format!("{parameter}Owned")),
                    spare: self.local_name(format!("{parameter}Spare")),
                };
                recycled_buffers.extend(Self::recycled_declarations(&recycled, type_));
                for map in maps {
                    self.recycled_maps.insert(map, recycled.clone());
                }
            }
        }
        let mut state = None;
        if loops {
            let mut excluded = captured.clone();
            excluded.extend(buffers.iter().map(|(position, _)| *position));
            excluded.extend(owned.iter().map(|(position, _, _)| *position));
            excluded.extend(recycled_positions);
            state = self.loop_state(id, function, mode, &parameters, &excluded);
            let mut places: Vec<GoExpression> =
                parameters.iter().map(|(name, _)| identifier_expression(name)).collect();
            let mut reassigned: Vec<String> =
                parameters.iter().map(|(name, _)| name.clone()).collect();
            for (position, buffer) in &buffers {
                places[*position] = identifier_expression(buffer);
                reassigned[*position] = buffer.clone();
            }
            if let Some(state) = &state {
                for position in &state.positions {
                    places[*position] = state.place(&parameters[*position].0);
                }
                reassigned.push(state.name.clone());
            }
            let target = LoopTarget { function: id, parameters: places, step: None };
            self.tail_loop = Some(TailLoop {
                parameters: reassigned,
                targets: vec![target],
                current: id,
                step: None,
            });
        }
        let mut body = vec![];
        let emitted = self.sink(&function.body, mode, Sink::Return, &mut body);
        for node in &owned_nodes {
            self.owned_snocs.remove(node);
        }
        self.recycled_maps.clear();
        let mut flags = self.release_updates(&owned_places, flags);
        emitted?;
        if loops {
            if let Some(GoStatement::Continue) = body.last() {
                body.pop();
            }
            iteration_copies.append(&mut body);
            body = iteration_copies;
            let mut clipped: Vec<GoStatement> = owned
                .iter()
                .map(|(position, place, _)| {
                    let monotype = function.parameters[*position].monotype;
                    self.clip(&parameters[*position].0, place, monotype)
                })
                .collect();
            for (position, buffer) in &buffers {
                let parameter = identifier_expression(&parameters[*position].0);
                clipped.push(GoStatement::Define {
                    names: vec![buffer.clone()],
                    values: vec![buffers::to_bytes(parameter)],
                });
            }
            clipped.append(&mut recycled_buffers);
            clipped.append(&mut flags);
            clipped.extend(state.map(|state| state.definition));
            clipped.push(GoStatement::Loop(body));
            body = clipped;
        }
        if let Some(GoStatement::Return(None)) = body.last() {
            body.pop();
        }
        self.tail_loop = None;
        self.byte_buffers.clear();
        self.attribute(function.body.position, 0, &mut body)?;
        self.name_definition(function.position, &mut body)?;
        Ok(vec![GoDeclaration::Function { name, parameters, result, body }])
    }

    pub(super) fn owned_parameter_snocs<'e>(
        &mut self,
        function: &'e Function,
        position: usize,
    ) -> Vec<(ownership::Place, Vec<&'e Expression>)> {
        let parameter = &function.parameters[position];
        self.carried_places(parameter.monotype)
            .into_iter()
            .filter_map(|place| {
                let carried = ownership::Carried::updating(parameter.id, &place);
                let nodes = ownership::owned_snocs(carried, &function.body)?;
                (!nodes.is_empty()).then_some((place, nodes))
            })
            .collect()
    }

    pub(super) fn owning_variant_name(&mut self, id: FunctionId, position: usize) -> String {
        if let Some(name) = self.owning_variants.get(&(id, position)) {
            return name.clone();
        }
        let function_name = self.function_names[id.0 as usize].clone();
        let name = self.global_name(Spelling::derived("", function_name, "Owning"));
        self.owning_variants.insert((id, position), name.clone());
        self.pending_owning_variants.push((id, position));
        name
    }

    fn owned_loop_arrays(
        &mut self,
        id: FunctionId,
        function: &Function,
        performed: bool,
    ) -> Vec<(usize, ownership::Place, Vec<*const Expression>)> {
        let arity = function.parameters.len();
        let mut owned = vec![];
        for (position, parameter) in function.parameters.iter().enumerate() {
            let tail_call = ownership::TailCall { function: id, arity, position };
            for place in self.carried_places(parameter.monotype) {
                let carried =
                    ownership::Carried::updating(parameter.id, &place).performed(performed);
                let Some(nodes) = ownership::owned_loop_snocs(carried, &function.body, tail_call)
                else {
                    continue;
                };
                if nodes.is_empty() {
                    continue;
                }
                let nodes = nodes.into_iter().map(std::ptr::from_ref).collect();
                owned.push((position, place, nodes));
            }
        }
        owned
    }

    /// A recursive constant: `name()` computes the value once, on first use, as
    /// JavaScript's lazily initialised recursive bindings do, in a `lazy.Lazy` cell, so that
    /// goroutines that run pure code may share it.
    fn lazy_constant(&mut self, name: &str, function: &Function) -> GoResult<Vec<GoDeclaration>> {
        let type_ = self.go_type(function.result)?;
        let mut statements = vec![];
        let value = self.value(&function.body, &mut statements)?;
        statements.push(GoStatement::Return(Some(value)));
        let cell = self.global_name(Spelling::derived("", name.into(), "Cell"));
        let compute = self.global_name(Spelling::derived("compute", name.into(), ""));
        self.import(GoPackage::Lazy);
        let unevaluated = GoExpression::Instantiation {
            function: Box::new(GoExpression::qualified(GoPackage::Lazy, "Unevaluated")),
            arguments: vec![type_.clone()],
        };
        let force = GoExpression::Field {
            value: Box::new(identifier_expression(&cell)),
            name: "ForceWith".into(),
        };
        let force = call(force, vec![identifier_expression(&compute)]);
        let line = self.span_line(function.position)?;
        Ok(vec![
            GoDeclaration::Variable {
                name: cell,
                type_: None,
                value: call(unevaluated, vec![]),
                line,
            },
            GoDeclaration::Function {
                name: name.into(),
                parameters: vec![],
                result: Some(type_.clone()),
                body: vec![GoStatement::Return(Some(force))],
            },
            GoDeclaration::Function {
                name: compute,
                parameters: vec![],
                result: Some(type_),
                body: statements,
            },
        ])
    }

    /// A top-level value. One whose evaluation runs code is computed by an initializer, which
    /// Go runs before main; an exception escaping it ends the program as one escaping main does.
    fn constant(&mut self, name: &str, function: &Function) -> GoResult<Vec<GoDeclaration>> {
        let type_ = self.go_type(function.result)?;
        let mut statements = vec![];
        let value = self.value(&function.body, &mut statements)?;
        let line = self.span_line(function.position)?;
        if statements.is_empty() && !runs_code(&value) {
            return Ok(vec![GoDeclaration::Variable {
                name: name.into(),
                type_: Some(type_),
                value,
                line,
            }]);
        }
        let initializer = self.global_name(Spelling::derived("initialize", name.into(), ""));
        statements.push(GoStatement::Return(Some(value)));
        self.attribute(function.body.position, 0, &mut statements)?;
        self.name_definition(function.position, &mut statements)?;
        let result = self.go_result(function.result)?;
        Ok(vec![
            GoDeclaration::Variable {
                name: name.into(),
                type_: None,
                value: call(identifier_expression(&initializer), vec![]),
                line,
            },
            GoDeclaration::Function {
                name: initializer,
                parameters: vec![],
                result,
                body: statements,
            },
        ])
    }
}

/// The constants (parameterless, effect-free definitions) that belong to a
/// reference cycle, found as strongly connected components (Tarjan).
pub(super) fn recursive_constants(
    program: &Program,
    monotypes: &Monotypes,
) -> FxHashSet<FunctionId> {
    let edges = reference_graph(&program.functions);
    let recursive = on_cycles(&edges, &strongly_connected(&edges));
    let mut constants = FxHashSet::default();
    for (position, function) in program.functions.iter().enumerate() {
        let constant =
            function.parameters.is_empty() && monotypes.effect_result(function.result).is_none();
        if recursive[position] && constant {
            constants.insert(FunctionId(position as u32));
        }
    }
    constants
}

/// Whether evaluating an expression calls a function, which may throw; the bodies of function
/// literals do not run when the literal is evaluated.
fn runs_code(expression: &GoExpression) -> bool {
    struct Calls(bool);
    impl Walk for Calls {
        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Function { .. } => {}
                GoExpression::Call { .. } => self.0 = true,
                _ => go_traversal::expression(self, value),
            }
        }
    }
    let mut calls = Calls(false);
    calls.expression(&mut expression.clone());
    calls.0
}

pub(super) fn await_fibers(
    declarations: &mut [GoDeclaration],
    await_: GoExpression,
    every_line: bool,
) {
    for declaration in declarations {
        if let GoDeclaration::Function { name, body, .. } = declaration
            && name == "main"
        {
            let await_ = await_.clone();
            // os.Exit skips deferred calls, so an exiting main awaits first.
            if let Some(GoStatement::Expression(last)) = body.last()
                && last.is_call_to(GoPackage::Os, "Exit")
            {
                let at = body.len() - 1;
                body.insert(at, GoStatement::Expression(call(await_, vec![])));
                continue;
            }
            let named = every_line && matches!(body.first(), Some(GoStatement::Line(_)));
            body.insert(usize::from(named), GoStatement::Defer(call(await_, vec![])));
        }
    }
}
