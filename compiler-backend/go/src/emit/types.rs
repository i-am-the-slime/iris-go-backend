//! The Go types of monotypes, and the layouts of data types.

use super::packages::Spelling;
use super::{
    ARRAY_TREE_DATA_LIMIT, ConstructorLayout, Crossing, DataKind, DataLayout, Emitter,
    INLINE_DATA_LIMIT, TRANSIENT_DATA_LIMIT, layout, names, reference_type,
};
use crate::erasure::Erasure;
use crate::error::GoResult;
use crate::foreign::ForeignPackages;
use crate::monotype::{DataConstructor, DataType, Failure, Monotype, MonotypeId};
use crate::naming::identifier;
use crate::syntax::{GoDeclaration, GoPackage, GoType, SourceLine, StructField};
use rustc_hash::{FxHashMap, FxHashSet};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// The Go type of a monotype, with the function types that return two results doing so once
    /// the program has chosen them.
    pub(super) fn go_type(&mut self, monotype: MonotypeId) -> GoResult<GoType> {
        let mut type_ = self.spelled_go_type(monotype)?;
        if !self.lowered_function_types.is_empty() {
            super::fallible::lower_type(&mut type_, &self.lowered_function_types);
        }
        Ok(type_)
    }

    fn spelled_go_type(&mut self, monotype: MonotypeId) -> GoResult<GoType> {
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Int => GoType::Int,
            Monotype::Int64 => GoType::Named("int64".into()),
            Monotype::UInt64 => GoType::Named("uint64".into()),
            Monotype::Number => GoType::Float64,
            Monotype::Boolean => GoType::Bool,
            Monotype::Char => GoType::Rune,
            Monotype::String => GoType::String,
            Monotype::Unit => GoType::EmptyStruct,
            Monotype::Erased(erasure) => GoType::Erased(erasure),
            Monotype::Opaque => GoType::Erased(Erasure::Foreign),
            Monotype::Array(element) => GoType::Slice(Box::new(self.go_type(element)?)),
            Monotype::HashMap(key, value) => {
                GoType::Map(Box::new(self.go_type(key)?), Box::new(self.go_type(value)?))
            }
            Monotype::OrderedMap(key, value) => self.ordered_map_type(key, value)?,
            Monotype::Record(_) => self.record_go_type(monotype)?,
            Monotype::Function(..) if self.has_closure_set(monotype) => {
                self.closure_layout(monotype)?.go_type()
            }
            Monotype::Function(..) => {
                let arity = self.arity(monotype);
                let (arguments, result) = self.leading_arrows(monotype, arity);
                let mut parameters = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    parameters.push(self.go_type(argument)?);
                }
                let result = match self.monotypes.get(result) {
                    Monotype::Effect(inner) => self.go_result(*inner)?,
                    _ => self.go_result(result)?,
                };
                GoType::Function { parameters, result: result.map(Box::new) }
            }
            Monotype::Effect(result) => {
                let result = self.go_result(result)?;
                GoType::Function { parameters: vec![], result: result.map(Box::new) }
            }
            Monotype::Reference(value) => {
                self.declare_reference();
                let value = self.go_type(value)?;
                GoType::Pointer(Box::new(reference_type(value)))
            }
            Monotype::Recursive(data) => self.recursive_type(&data)?,
            Monotype::ForeignData(data) => self.foreign_data_type(&data)?,
            Monotype::MutableArray(element) => {
                GoType::Pointer(Box::new(GoType::Slice(Box::new(self.go_type(element)?))))
            }
            Monotype::Nullable(element) => GoType::Pointer(Box::new(self.go_type(element)?)),
            Monotype::Regex => {
                self.import(GoPackage::Regex);
                GoType::Pointer(Box::new(GoType::Named("regex.Regex".into())))
            }
            Monotype::Mutex => {
                self.import(GoPackage::Sync);
                GoType::Pointer(Box::new(GoType::Named("sync.Mutex".into())))
            }
            Monotype::BigInt => {
                self.import(GoPackage::MathBig);
                GoType::Pointer(Box::new(GoType::Named("big.Int".into())))
            }
            Monotype::Lazy(value) => {
                self.import(GoPackage::Lazy);
                let value = self.go_type(value)?;
                let lazy = GoType::Generic { name: "lazy.Lazy".into(), arguments: vec![value] };
                GoType::Pointer(Box::new(lazy))
            }
            Monotype::ConsList(element) => {
                self.import(GoPackage::Direct);
                let element = self.go_type(element)?;
                let name = "direct.ConsList".into();
                GoType::Pointer(Box::new(GoType::Generic { name, arguments: vec![element] }))
            }
            Monotype::Error => {
                self.import(GoPackage::Exception);
                GoType::Named("exception.Error".into())
            }
            Monotype::Object(element) => {
                let values = GoType::Slice(Box::new(self.go_type(element)?));
                GoType::Pointer(Box::new(GoType::Struct(vec![
                    StructField::new("Index", GoType::Named("map[string]int".into())),
                    StructField::new("Ints", GoType::Int),
                    StructField::new("Keys", GoType::Slice(Box::new(GoType::String))),
                    StructField::new("Vals", values),
                ])))
            }
            Monotype::Data(data) => {
                let layout = self.data_layout(&data)?;
                self.layout_type(&layout)?
            }
        })
    }

    pub(super) fn recursive_type(&mut self, data: &DataType) -> GoResult<GoType> {
        if let Some(name) = self.recursive_names.get(data) {
            return Ok(GoType::Named(name.clone()));
        }
        let unfolded = self.unfold(data)?;
        if let Monotype::Record(_) | Monotype::Data(_) = self.monotypes.get(unfolded) {
            return self.go_type(unfolded);
        }
        let name = self.data_type_global(data)?;
        self.homes.insert(name.clone(), data.file_id);
        self.recursive_names.insert(data.clone(), name.clone());
        if self.unfolds_only_to_newtypes(data, unfolded)? {
            let type_ = GoType::Any;
            let line = self.data_line(data)?;
            let member_lines = vec![];
            let declaration = GoDeclaration::Type { name: name.clone(), type_, line, member_lines };
            self.type_declarations.push(declaration);
            return Ok(GoType::Named(name));
        }
        let type_ = self.go_type(unfolded)?;
        // A defined type would be a second Go type for the unfolding, without
        // its methods (`Force` of a `Lazy`) and unassignable to it inside
        // function types, so the newtype is an alias whenever Go allows one.
        let line = self.data_line(data)?;
        let defined = self.unfolding_reaches_itself_unnamed(data, unfolded)?
            || (!is_generic_instantiation(&type_)
                && self.unfolding_reaches_itself_as_type_argument(data, unfolded)?);
        let declaration = if defined {
            GoDeclaration::Type { name: name.clone(), type_, line, member_lines: vec![] }
        } else {
            self.type_aliases.insert(name.clone(), type_.clone());
            GoDeclaration::Alias { name: name.clone(), type_, line }
        };
        self.type_declarations.push(declaration);
        Ok(GoType::Named(name))
    }

    /// Whether two monotypes are one Go type, as Go sees it through aliases.
    pub(super) fn has_closure_set(&mut self, monotype: MonotypeId) -> bool {
        let monotype = self.monotypes.without_causes(monotype);
        self.closure_sets.contains_key(&monotype)
    }

    pub(super) fn same_go_type(&mut self, left: MonotypeId, right: MonotypeId) -> GoResult<bool> {
        let mut left = self.go_type(left)?;
        let mut right = self.go_type(right)?;
        self.resolve_aliases(&mut left);
        self.resolve_aliases(&mut right);
        Ok(left == right)
    }

    /// Go cannot yet instantiate a generic type at an alias of a generic
    /// instantiation that is still being declared (go.dev/issue/78296, "an
    /// incomplete alias"): `type Cofree = *lazy.Lazy[*Cell]` while a struct
    /// that `Cell` reaches holds a `*lazy.Lazy[Cofree]`. Every type argument
    /// in a type declaration spells such an alias out, which is the same Go
    /// type and leaves the cycle to pass through the struct alone.
    pub(super) fn spell_out_generic_alias_arguments(&mut self) {
        let generic: FxHashSet<String> = self
            .type_aliases
            .iter()
            .filter(|(_, aliased)| is_generic_instantiation(aliased))
            .map(|(name, _)| name.clone())
            .collect();
        if generic.is_empty() {
            return;
        }
        for declaration in &mut self.type_declarations {
            if let GoDeclaration::Type { type_, .. } | GoDeclaration::Alias { type_, .. } =
                declaration
            {
                spell_out_arguments(type_, &self.type_aliases, &generic, false);
            }
        }
    }

    /// Replaces every alias in a Go type by the type it spells, and every
    /// erasure by the `any` it is whatever the census says caused it. An
    /// alias's cycle passes through a defined type, which stays named, so this ends.
    pub(super) fn resolve_aliases(&self, type_: &mut GoType) {
        match type_ {
            GoType::Erased(_) => *type_ = GoType::Any,
            GoType::Named(name) => {
                if let Some(aliased) = self.type_aliases.get(name) {
                    *type_ = aliased.clone();
                    self.resolve_aliases(type_);
                }
            }
            GoType::Generic { arguments, .. } | GoType::Results(arguments) => {
                arguments.iter_mut().for_each(|argument| self.resolve_aliases(argument));
            }
            GoType::Slice(element) | GoType::Pointer(element) => self.resolve_aliases(element),
            GoType::Map(key, value) => {
                self.resolve_aliases(key);
                self.resolve_aliases(value);
            }
            GoType::Function { parameters, result } => {
                parameters.iter_mut().for_each(|parameter| self.resolve_aliases(parameter));
                if let Some(result) = result {
                    self.resolve_aliases(result);
                }
            }
            GoType::Struct(fields) => {
                fields.iter_mut().for_each(|field| self.resolve_aliases(&mut field.type_));
            }
            GoType::Int
            | GoType::Float64
            | GoType::Bool
            | GoType::Rune
            | GoType::String
            | GoType::EmptyStruct
            | GoType::Any => {}
        }
    }

    /// Whether a recursive newtype unfolds through newtypes alone back to
    /// itself, as `newtype X = X X` and `Data.Void` do, so that it has no
    /// constructor that could build a value.
    pub(super) fn unfolds_only_to_newtypes(
        &mut self,
        data: &DataType,
        mut unfolded: MonotypeId,
    ) -> GoResult<bool> {
        let mut visited: FxHashSet<DataType> = FxHashSet::default();
        while let Monotype::Recursive(inner) = self.monotypes.get(unfolded).clone() {
            if inner == *data {
                return Ok(true);
            }
            if !visited.insert(inner.clone()) {
                return Ok(false);
            }
            unfolded = self.unfold(&inner)?;
        }
        Ok(false)
    }

    /// Whether a recursive newtype's unfolding refers back to the newtype
    /// without passing through a named Go type (a record or data struct). Go
    /// rejects such a cycle of aliases, so only then must the newtype be a
    /// defined type of its own.
    pub(super) fn unfolding_reaches_itself_unnamed(
        &mut self,
        data: &DataType,
        unfolded: MonotypeId,
    ) -> GoResult<bool> {
        let mut pending = vec![unfolded];
        let mut visited: FxHashSet<MonotypeId> = FxHashSet::default();
        while let Some(monotype) = pending.pop() {
            if !visited.insert(monotype) {
                continue;
            }
            match self.monotypes.get(monotype).clone() {
                Monotype::Recursive(inner) if inner == *data => return Ok(true),
                Monotype::Recursive(inner) => pending.push(self.unfold(&inner)?),
                Monotype::Data(maybe)
                    if let Some(payload) = self.maybe_pointer_payload(&maybe)? =>
                {
                    pending.push(payload)
                }
                Monotype::Function(..) if self.has_closure_set(monotype) => {}
                Monotype::Function(argument, result) => pending.extend([argument, result]),
                Monotype::Array(inner)
                | Monotype::Effect(inner)
                | Monotype::Reference(inner)
                | Monotype::MutableArray(inner)
                | Monotype::Object(inner)
                | Monotype::Nullable(inner)
                | Monotype::Lazy(inner)
                | Monotype::ConsList(inner) => pending.push(inner),
                Monotype::HashMap(key, value) | Monotype::OrderedMap(key, value) => {
                    pending.extend([key, value])
                }
                Monotype::ForeignData(foreign) => {
                    for &argument in foreign.arguments.iter() {
                        let argument = self.monotypes.monotype(&mut self.context, argument);
                        pending.push(argument.map_err(Failure::in_code_generation)?);
                    }
                }
                Monotype::Record(_)
                | Monotype::Data(_)
                | Monotype::Int
                | Monotype::Number
                | Monotype::Boolean
                | Monotype::Char
                | Monotype::String
                | Monotype::Unit
                | Monotype::Error
                | Monotype::Opaque
                | Monotype::Regex
                | Monotype::Mutex
                | Monotype::BigInt
                | Monotype::Int64
                | Monotype::UInt64
                | Monotype::Erased(_) => {}
            }
        }
        Ok(false)
    }

    pub(super) fn unfolding_reaches_itself_as_type_argument(
        &mut self,
        data: &DataType,
        unfolded: MonotypeId,
    ) -> GoResult<bool> {
        let mut pending = vec![(unfolded, false)];
        let mut visited: FxHashSet<(MonotypeId, bool)> = FxHashSet::default();
        while let Some((monotype, argument)) = pending.pop() {
            if !visited.insert((monotype, argument)) {
                continue;
            }
            match self.monotypes.get(monotype).clone() {
                Monotype::Recursive(inner) if inner == *data => {
                    if argument {
                        return Ok(true);
                    }
                }
                Monotype::Recursive(inner) => pending.push((self.unfold(&inner)?, argument)),
                Monotype::Record(fields) => {
                    pending.extend(fields.iter().map(|field| (field.monotype, argument)));
                }
                Monotype::Data(inner) => {
                    let constructors = self
                        .monotypes
                        .constructors(&mut self.context, &inner)
                        .map_err(Failure::in_code_generation)?;
                    for constructor in constructors.iter() {
                        pending.extend(constructor.fields.iter().map(|&field| (field, argument)));
                    }
                }
                Monotype::Function(argument_type, result) => {
                    pending.extend([(argument_type, argument), (result, argument)]);
                }
                Monotype::Array(inner)
                | Monotype::Effect(inner)
                | Monotype::MutableArray(inner)
                | Monotype::Object(inner)
                | Monotype::Nullable(inner) => pending.push((inner, argument)),
                Monotype::HashMap(key, value) | Monotype::OrderedMap(key, value) => {
                    pending.extend([(key, argument), (value, argument)]);
                }
                Monotype::Reference(inner) | Monotype::Lazy(inner) | Monotype::ConsList(inner) => {
                    pending.push((inner, true))
                }
                Monotype::ForeignData(foreign) => {
                    for &type_argument in foreign.arguments.iter() {
                        let type_argument =
                            self.monotypes.monotype(&mut self.context, type_argument);
                        pending.push((type_argument.map_err(Failure::in_code_generation)?, true));
                    }
                }
                Monotype::Int
                | Monotype::Number
                | Monotype::Boolean
                | Monotype::Char
                | Monotype::String
                | Monotype::Unit
                | Monotype::Error
                | Monotype::Opaque
                | Monotype::Regex
                | Monotype::Mutex
                | Monotype::BigInt
                | Monotype::Int64
                | Monotype::UInt64
                | Monotype::Erased(_) => {}
            }
        }
        Ok(false)
    }

    /// The named type a go-support package or a project's Go foreign package
    /// declares for one of its module's `foreign import data` types (or
    /// constructor-less data types), instantiated at the Go types of
    /// the arguments when the type takes any.
    pub(super) fn foreign_data_type(&mut self, data: &DataType) -> GoResult<GoType> {
        let module_name = self.context.module(data.file_id)?.name.clone();
        let type_name = self.context.type_name(data.file_id, data.item)?;
        let support = match crate::monotype::native_hash_map(&mut self.context, data)? {
            Some(true) => Some((GoPackage::HashMap, "Native")),
            _ => crate::foreign::support_data(&module_name, &type_name),
        };
        let name = match support {
            Some((package, support_name)) => {
                self.import(package);
                format!("{}.{support_name}", package.name())
            }
            None => {
                self.imports.insert(self.foreign_packages.import_path(&module_name));
                let package = ForeignPackages::package_name(&module_name);
                let module = self.context.module(data.file_id)?;
                format!("{package}.{}", module.foreign_type_name(&type_name))
            }
        };
        if data.arguments.is_empty() {
            return Ok(GoType::Named(name));
        }
        let native = self.monotypes.native_foreign_data.contains(&(data.file_id, data.item));
        let crossing = Crossing::native_when(native);
        let mut arguments = Vec::with_capacity(data.arguments.len());
        for &argument in data.arguments.iter() {
            let monotype = self
                .monotypes
                .monotype(&mut self.context, argument)
                .map_err(Failure::in_code_generation)?;
            // A project's foreign package sees its type arguments in the
            // convention its functions take them in.
            let argument = match support {
                Some(_) => self.go_type(monotype)?,
                None => self.convention_or_native(monotype, crossing)?,
            };
            arguments.push(argument);
        }
        Ok(GoType::Generic { name, arguments })
    }

    pub(super) fn unfold(&mut self, data: &DataType) -> GoResult<MonotypeId> {
        self.monotypes.unfold_in(&mut self.context, data, "code generation")
    }

    pub(super) fn go_result(&mut self, monotype: MonotypeId) -> GoResult<Option<GoType>> {
        if let Monotype::Unit = self.monotypes.get(monotype) {
            return Ok(None);
        }
        Ok(Some(self.go_type(monotype)?))
    }

    pub(super) fn is_unit(&self, monotype: MonotypeId) -> bool {
        matches!(self.monotypes.get(monotype), Monotype::Unit)
    }

    pub(super) fn declare_reference(&mut self) {
        if std::mem::replace(&mut self.reference_declared, true) {
            return;
        }
        self.spellings.insert("Ref".into(), Spelling::Base("Ref".into()));
        self.type_declarations.push(GoDeclaration::GenericType {
            name: "Ref".into(),
            parameter: "T".into(),
            type_: GoType::Struct(vec![StructField::new("Value", GoType::Named("T".into()))]),
        });
    }

    pub(super) fn record_name(&mut self, monotype: MonotypeId) -> GoResult<String> {
        if let Some((module_name, struct_name)) = self.monotypes.foreign_records.get(&monotype) {
            let package = ForeignPackages::package_name(module_name);
            self.imports.insert(self.foreign_packages.import_path(module_name));
            return Ok(format!("{package}.{struct_name}"));
        }
        let monotype = self.monotypes.without_causes(monotype);
        if let Some(name) = self.record_names.get(&monotype) {
            return Ok(name.clone());
        }
        let Monotype::Record(fields) = self.monotypes.get(monotype).clone() else {
            unreachable!("invariant violated: record name requested for a non-record")
        };
        let base: String = if fields.is_empty() {
            "Empty".into()
        } else {
            fields.iter().map(|field| crate::naming::go_field(&field.label)).collect()
        };
        let name = self.pending_global(base, names::PendingSpelling::Record(monotype));
        self.record_names.insert(monotype, name.clone());
        let type_ = self.record_declaration(monotype)?;
        self.type_declarations.push(GoDeclaration::Type {
            name: name.clone(),
            type_,
            line: None,
            member_lines: vec![],
        });
        Ok(name)
    }

    /// A data type's global: its name followed by its type arguments.
    pub(super) fn data_type_global(&mut self, data: &DataType) -> GoResult<String> {
        if let Some(labels) = self.variant_labels(data)? {
            let full = format!("Variant{labels}");
            let parts =
                vec![names::NamePart::Stutter("Variant".into()), names::NamePart::Text(labels)];
            return Ok(self.pending_global(identifier(&full), names::PendingSpelling::Parts(parts)));
        }
        let mut full = self.context.type_name(data.file_id, data.item)?.to_string();
        for &argument in data.arguments.iter() {
            self.context.type_suffix(argument, &mut full)?;
        }
        let parts = self.data_parts(data)?;
        Ok(self.pending_global(identifier(&full), names::PendingSpelling::Parts(parts)))
    }

    pub(super) fn variant_labels(&mut self, data: &DataType) -> GoResult<Option<String>> {
        if self.monotypes.variant_row(data).is_none() {
            return Ok(None);
        }
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(Failure::in_code_generation)?;
        let labels: String = constructors
            .iter()
            .map(|constructor| crate::naming::go_field(&constructor.name))
            .collect();
        Ok(Some(labels))
    }

    pub(super) fn data_layout(&mut self, data: &DataType) -> GoResult<DataLayout> {
        if let Some(layout) = self.data_layouts.get(data) {
            return Ok(layout.clone());
        }
        if let Some(payload) = self.maybe_payload(data)? {
            let constructors = self
                .monotypes
                .constructors(&mut self.context, data)
                .map_err(Failure::in_code_generation)?;
            return self.maybe_layout(data, payload, &constructors);
        }
        let name = self.data_type_global(data)?;
        self.homes.insert(name.clone(), data.file_id);
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&name))?;
        let edges = match self.candidates.contains(data) {
            true => self.edge_bits(data)?,
            false => None,
        };
        let (kind, plan) = self.slot_plan(data, &constructors, edges.is_some())?;
        let mut layouts = vec![];
        for (index, constructor) in constructors.iter().enumerate() {
            let tag = self.global_name(Spelling::derived(
                "",
                name.clone(),
                &crate::naming::go_field(&constructor.name),
            ));
            let fields = match &plan {
                Some(plan) => {
                    let slots = plan.constructors[index].iter().cloned();
                    slots.zip(constructor.fields.iter().copied()).collect()
                }
                None => vec![],
            };
            layouts.push(ConstructorLayout { tag, fields });
        }
        let erases_arguments = kind != DataKind::Enumeration && self.erases_arguments(data)?;
        let boxed = self.is_boxed(data)?;
        let layout = DataLayout {
            name: name.clone(),
            kind,
            constructors: layouts.clone(),
            erases_arguments,
            boxed,
            declaration: None,
            origin_position: plan.as_ref().map_or(0, |plan| plan.pointer_prefix),
            maybe: None,
            edges,
        };
        self.data_layouts.insert(data.clone(), layout.clone());
        let names: Vec<String> =
            layouts.iter().map(|constructor| constructor.tag.clone()).collect();
        let line = self.data_line(data)?;
        let mut constructor_lines = vec![];
        for constructor in constructors.iter() {
            constructor_lines.push(self.constructor_line(data, constructor)?);
        }
        let tag_lines: Vec<(String, SourceLine)> = names
            .iter()
            .zip(&constructor_lines)
            .filter_map(|(tag, line)| Some((tag.clone(), line.clone()?)))
            .collect();
        let Some(plan) = plan else {
            self.type_declarations.push(GoDeclaration::Type {
                name: name.clone(),
                type_: layout::tag_type(constructors.len()),
                line: line.clone(),
                member_lines: vec![],
            });
            if !names.is_empty() {
                let constants = GoDeclaration::Constants {
                    type_name: Some(name),
                    names,
                    line,
                    member_lines: tag_lines,
                };
                self.type_declarations.push(constants);
            }
            return Ok(layout);
        };
        let field_lines = slot_lines(&plan.constructors, &constructor_lines);
        let mut fields = vec![];
        for slot in plan.slots {
            fields.push(match slot {
                layout::Slot::Tag => StructField::new("Tag", layout::tag_type(constructors.len())),
                layout::Slot::Unique => StructField::new("Unique", layout::unique_type()),
                layout::Slot::Field { name, monotype } => {
                    StructField::new(name, self.go_type(monotype)?)
                }
            });
        }
        if let Some(layout) = self.data_layouts.get_mut(data) {
            layout.declaration = Some(self.type_declarations.len());
        }
        let type_ = GoType::Struct(fields);
        let declaration = GoDeclaration::Type {
            name: name.clone(),
            type_,
            line: line.clone(),
            member_lines: field_lines,
        };
        self.type_declarations.push(declaration);
        if kind == DataKind::Tagged {
            self.type_declarations.push(GoDeclaration::Constants {
                type_name: None,
                names,
                line,
                member_lines: tag_lines,
            });
        }
        if kind == DataKind::Sentinel {
            for (constructor, line) in layouts.iter().zip(&constructor_lines) {
                if constructor.fields.is_empty() {
                    self.shared_nullary(&name, &constructor.tag, false, line.clone());
                }
            }
        }
        Ok(self.data_layouts.get(data).cloned().unwrap_or(layout))
    }

    pub(super) fn slot_plan(
        &mut self,
        data: &DataType,
        constructors: &[DataConstructor],
        tracked: bool,
    ) -> GoResult<(DataKind, Option<layout::SlotPlan>)> {
        let mut kind = if constructors.iter().all(|constructor| constructor.fields.is_empty()) {
            DataKind::Enumeration
        } else if constructors.len() == 1 {
            DataKind::Product
        } else {
            DataKind::Tagged
        };
        let mut plan = match kind {
            DataKind::Enumeration => None,
            DataKind::Tagged | DataKind::Product | DataKind::Sentinel => {
                Some(self.plan_tracked_slots(constructors, tracked)?)
            }
        };
        if kind == DataKind::Tagged && self.tells_nullaries_apart_by_address(data, constructors)? {
            let untagged = self.plan_untagged_slots(constructors, tracked)?;
            // Go gives every allocation of nothing one address, so cells of an empty struct
            // could not be told apart.
            if untagged.shape.size() > 0 {
                kind = DataKind::Sentinel;
                plan = Some(untagged);
            }
        }
        Ok((kind, plan))
    }

    /// Whether a type of several constructors, only one of which has fields, can be a
    /// `Sentinel`: its cells are boxed, and its nullary constructors are always the shared cells,
    /// which a layout that erases arguments does not promise.
    fn tells_nullaries_apart_by_address(
        &mut self,
        data: &DataType,
        constructors: &[DataConstructor],
    ) -> GoResult<bool> {
        let with_fields =
            constructors.iter().filter(|constructor| !constructor.fields.is_empty()).count();
        Ok(with_fields == 1 && self.is_boxed(data)? && !self.erases_arguments(data)?)
    }

    pub(super) fn contains_itself(&mut self, data: &DataType) -> GoResult<bool> {
        self.reaches_itself(data, false)
    }

    /// Whether the data type holds itself through an array: a tree whose node keeps its children
    /// in an `Array`, which Go holds by value unless the node is boxed.
    pub(super) fn contains_itself_through_arrays(&mut self, data: &DataType) -> GoResult<bool> {
        self.reaches_itself(data, true)
    }

    fn reaches_itself(&mut self, data: &DataType, through_arrays: bool) -> GoResult<bool> {
        let mut pending: Vec<MonotypeId> = vec![];
        let mut visited: FxHashSet<DataType> = FxHashSet::default();
        let mut unfolded: FxHashSet<DataType> = FxHashSet::default();
        visited.insert(data.clone());
        pending.extend(self.constructor_fields(data)?);
        while let Some(monotype) = pending.pop() {
            match self.monotypes.get(monotype).clone() {
                Monotype::Data(inner) if inner == *data => return Ok(true),
                Monotype::Data(inner) => {
                    if visited.insert(inner.clone()) {
                        pending.extend(self.constructor_fields(&inner)?);
                    }
                }
                Monotype::Record(fields) => {
                    pending.extend(fields.iter().map(|field| field.monotype))
                }
                // A recursive newtype reaches the data type only if its unfolding does: a
                // `Maybe Trie`, where `Trie` recurses through a `Map` of its own, holds no
                // `Maybe Trie` and can be a value.
                Monotype::Recursive(inner) => {
                    if unfolded.insert(inner.clone()) {
                        pending.push(self.unfold(&inner)?);
                    }
                }
                Monotype::Array(element) | Monotype::MutableArray(element) if through_arrays => {
                    pending.push(element)
                }
                _ => {}
            }
        }
        Ok(false)
    }

    pub(super) fn is_cell(&mut self, data: &DataType) -> bool {
        let Ok(constructors) = self.monotypes.constructors(&mut self.context, data) else {
            return false;
        };
        let has_fields = constructors.iter().any(|constructor| !constructor.fields.is_empty());
        let erases_arguments = self.erases_arguments(data).unwrap_or(true);
        has_fields && !erases_arguments && self.is_boxed(data).unwrap_or(false)
    }

    pub(super) fn reaches(&mut self, from: &DataType, target: &DataType) -> GoResult<bool> {
        let mut pending: Vec<MonotypeId> = vec![];
        let mut visited: FxHashSet<DataType> = FxHashSet::default();
        visited.insert(from.clone());
        pending.extend(self.constructor_fields(from)?);
        while let Some(monotype) = pending.pop() {
            match self.monotypes.get(monotype).clone() {
                Monotype::Data(inner) | Monotype::Recursive(inner) if inner == *target => {
                    return Ok(true);
                }
                Monotype::Data(inner) => {
                    if visited.insert(inner.clone()) {
                        pending.extend(self.constructor_fields(&inner)?);
                    }
                }
                Monotype::Record(fields) => {
                    pending.extend(fields.iter().map(|field| field.monotype))
                }
                _ => {}
            }
        }
        Ok(false)
    }

    pub(super) fn constructor_fields(&mut self, data: &DataType) -> GoResult<Vec<MonotypeId>> {
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(Failure::in_code_generation)?;
        Ok(constructors.iter().flat_map(|constructor| constructor.fields.iter().copied()).collect())
    }

    pub(super) fn erases_arguments(&mut self, data: &DataType) -> GoResult<bool> {
        if let Some(&erases) = self.erasing_layouts.get(data) {
            return Ok(erases);
        }
        let used = self.monotypes.used_parameters(&mut self.context, data.file_id, data.item)?;
        let erases = data
            .arguments
            .iter()
            .zip(used.iter())
            .any(|(&argument, &used)| used && self.context.types.contains_erased(argument));
        self.erasing_layouts.insert(data.clone(), erases);
        Ok(erases)
    }

    pub(super) fn is_boxed(&mut self, data: &DataType) -> GoResult<bool> {
        let Some(shape) = self.inline_shape(data)? else { return Ok(true) };
        if self.is_map_key(data)? {
            return Ok(false);
        }
        let limit = if !self.copied_by_containers.contains(data) {
            TRANSIENT_DATA_LIMIT
        } else if self.contains_itself_through_arrays(data)? {
            ARRAY_TREE_DATA_LIMIT
        } else {
            INLINE_DATA_LIMIT
        };
        Ok(shape.size() > limit)
    }

    fn is_map_key(&mut self, data: &DataType) -> GoResult<bool> {
        if self.map_keys.is_none() {
            let mut pending: Vec<MonotypeId> = self
                .monotypes
                .ids()
                .filter_map(|id| match self.monotypes.get(id) {
                    Monotype::HashMap(key, _) | Monotype::OrderedMap(key, _) => Some(*key),
                    _ => None,
                })
                .collect();
            let mut keys = FxHashSet::default();
            while let Some(monotype) = pending.pop() {
                match self.monotypes.get(monotype).clone() {
                    Monotype::Data(data) if keys.insert(data.clone()) => {
                        pending.extend(self.constructor_fields(&data)?)
                    }
                    Monotype::Record(fields) => {
                        pending.extend(fields.iter().map(|field| field.monotype))
                    }
                    _ => {}
                }
            }
            self.map_keys = Some(keys);
        }
        Ok(self.map_keys.as_ref().is_some_and(|keys| keys.contains(data)))
    }

    /// Adds the `Origin` field to an erased layout's struct, once.
    pub(super) fn remember_origin(&mut self, data: &DataType) -> GoResult<bool> {
        let layout = self.data_layout(data)?;
        if !layout.erases_arguments {
            return Ok(false);
        }
        if let Some(position) = layout.declaration
            && let GoDeclaration::Type { type_: GoType::Struct(fields), .. } =
                &mut self.type_declarations[position]
            && !fields.iter().any(|field| field.name == "Origin")
        {
            fields.insert(layout.origin_position, StructField::new("Origin", GoType::Any));
        }
        Ok(true)
    }
}

/// `*lazy.Lazy[T]` and the like: a generic instantiation, behind pointers.
fn slot_lines(
    slots: &[Vec<String>],
    constructor_lines: &[Option<SourceLine>],
) -> Vec<(String, SourceLine)> {
    let mut lines = vec![];
    for (constructor, line) in slots.iter().zip(constructor_lines) {
        let Some(line) = line else { continue };
        for slot in constructor {
            let shared = slots.iter().filter(|other| other.contains(slot)).count() > 1;
            if !shared {
                lines.push((slot.clone(), line.clone()));
            }
        }
    }
    lines
}

fn is_generic_instantiation(type_: &GoType) -> bool {
    match type_ {
        GoType::Generic { .. } => true,
        GoType::Pointer(inner) => is_generic_instantiation(inner),
        _ => false,
    }
}

/// Spells out each alias in `generic` where it is, or is inside, a type argument.
fn spell_out_arguments(
    type_: &mut GoType,
    aliases: &FxHashMap<String, GoType>,
    generic: &FxHashSet<String>,
    in_argument: bool,
) {
    if let GoType::Named(name) = type_
        && in_argument
        && generic.contains(name.as_str())
    {
        *type_ = aliases[name.as_str()].clone();
    }
    let in_argument = in_argument || matches!(type_, GoType::Generic { .. });
    let inner: Vec<&mut GoType> = match type_ {
        GoType::Generic { arguments, .. } => arguments.iter_mut().collect(),
        GoType::Slice(element) | GoType::Pointer(element) => vec![element],
        GoType::Function { parameters, result } => {
            parameters.iter_mut().chain(result.as_deref_mut()).collect()
        }
        GoType::Struct(fields) => fields.iter_mut().map(|field| &mut field.type_).collect(),
        _ => vec![],
    };
    for type_ in inner {
        spell_out_arguments(type_, aliases, generic, in_argument);
    }
}
