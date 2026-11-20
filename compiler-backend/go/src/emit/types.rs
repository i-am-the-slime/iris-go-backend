//! The Go types of monotypes, and the layouts of data types.

use super::packages::Spelling;
use super::{
    ConstructorLayout, DataKind, DataLayout, Emitter, INLINE_DATA_LIMIT, TRANSIENT_DATA_LIMIT,
    layout, names, reference_type,
};
use crate::erasure::Erasure;
use crate::error::GoResult;
use crate::foreign::{ForeignPackages, GoPackage};
use crate::monotype::{DataType, Failure, Monotype, MonotypeId};
use crate::naming::{capitalise, identifier};
use crate::syntax::{GoDeclaration, GoType};
use files::FileId;
use rustc_hash::{FxHashMap, FxHashSet};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn go_type(&mut self, monotype: MonotypeId) -> GoResult<GoType> {
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Int => GoType::Named("int32".into()),
            Monotype::Number => GoType::Float64,
            Monotype::Boolean => GoType::Bool,
            Monotype::Char => GoType::Rune,
            Monotype::String => GoType::String,
            Monotype::Unit => GoType::EmptyStruct,
            Monotype::Erased(erasure) => GoType::Erased(erasure),
            Monotype::Opaque => GoType::Erased(Erasure::Foreign),
            Monotype::Array(element) => GoType::Slice(Box::new(self.go_type(element)?)),
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
                self.imports.insert(GoPackage::Regex.path().into());
                GoType::Pointer(Box::new(GoType::Named("regex.Regex".into())))
            }
            Monotype::Mutex => {
                self.imports.insert("sync".into());
                GoType::Pointer(Box::new(GoType::Named("sync.Mutex".into())))
            }
            Monotype::BigInt => {
                self.imports.insert("math/big".into());
                GoType::Pointer(Box::new(GoType::Named("big.Int".into())))
            }
            Monotype::Lazy(value) => {
                self.imports.insert(GoPackage::Lazy.path().into());
                let value = self.go_type(value)?;
                let lazy = GoType::Generic { name: "lazy.Lazy".into(), arguments: vec![value] };
                GoType::Pointer(Box::new(lazy))
            }
            Monotype::ConsList(element) => {
                self.imports.insert(GoPackage::Direct.path().into());
                let element = self.go_type(element)?;
                let name = "direct.ConsList".into();
                GoType::Pointer(Box::new(GoType::Generic { name, arguments: vec![element] }))
            }
            Monotype::Error => {
                self.imports.insert(GoPackage::Exception.path().into());
                GoType::Named("exception.Error".into())
            }
            Monotype::Object(element) => {
                let values = GoType::Slice(Box::new(self.go_type(element)?));
                GoType::Pointer(Box::new(GoType::Struct(vec![
                    ("Index".into(), GoType::Named("map[string]int".into())),
                    ("Ints".into(), GoType::Int),
                    ("Keys".into(), GoType::Slice(Box::new(GoType::String))),
                    ("Vals".into(), values),
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
            // `newtype X = X X` has no values; nothing reads the empty struct.
            let type_ = GoType::EmptyStruct;
            self.type_declarations.push(GoDeclaration::Type { name: name.clone(), type_ });
            return Ok(GoType::Named(name));
        }
        let type_ = self.go_type(unfolded)?;
        // A defined type would be a second Go type for the unfolding, without
        // its methods (`Force` of a `Lazy`) and unassignable to it inside
        // function types, so the newtype is an alias whenever Go allows one.
        let declaration = if self.unfolding_reaches_itself_unnamed(data, unfolded)? {
            GoDeclaration::Type { name: name.clone(), type_ }
        } else {
            self.type_aliases.insert(name.clone(), type_.clone());
            GoDeclaration::Alias { name: name.clone(), type_ }
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
            GoType::Generic { arguments, .. } => {
                arguments.iter_mut().for_each(|argument| self.resolve_aliases(argument));
            }
            GoType::Slice(element) | GoType::Pointer(element) => self.resolve_aliases(element),
            GoType::Function { parameters, result } => {
                parameters.iter_mut().for_each(|parameter| self.resolve_aliases(parameter));
                if let Some(result) = result {
                    self.resolve_aliases(result);
                }
            }
            GoType::Struct(fields) => {
                fields.iter_mut().for_each(|(_, field)| self.resolve_aliases(field));
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
                Monotype::Data(maybe) if let Some(payload) = self.maybe_pointer_payload(&maybe)? => {
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
        let support = crate::foreign::support_data(&module_name, &type_name);
        let name = match support {
            Some((package, support_name)) => {
                self.imports.insert(package.path().into());
                format!("{}.{support_name}", package.name())
            }
            None => {
                self.imports.insert(self.foreign_packages.import_path(&module_name));
                let package = ForeignPackages::package_name(&module_name);
                format!("{package}.{}", self.foreign_type_name(data.file_id, &type_name)?)
            }
        };
        if data.arguments.is_empty() {
            return Ok(GoType::Named(name));
        }
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
                None => self.convention_or_native(monotype)?,
            };
            arguments.push(argument);
        }
        Ok(GoType::Generic { name, arguments })
    }

    /// The Go name of a type a project's foreign package declares: the
    /// type's own name, capitalised, unless one of the module's values
    /// capitalises to it too (hyrule's `objHack` builds an `ObjHack`), in which
    /// case the type's name ends in `Type`.
    pub(super) fn foreign_type_name(
        &mut self,
        file_id: FileId,
        type_name: &str,
    ) -> GoResult<String> {
        let name = capitalise(type_name);
        let module = self.context.module(file_id)?;
        let taken = module.indexed.items.iter_terms().any(|(_, term)| {
            term.name.as_deref().is_some_and(|term_name| capitalise(term_name) == name)
        });
        Ok(if taken { format!("{name}Type") } else { name })
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
            type_: GoType::Struct(vec![("Value".into(), GoType::Named("T".into()))]),
        });
    }

    pub(super) fn record_name(&mut self, monotype: MonotypeId) -> GoResult<String> {
        if let Some((module_name, struct_name)) = self.monotypes.foreign_records.get(&monotype) {
            let package = ForeignPackages::package_name(module_name);
            self.imports.insert(self.foreign_packages.import_path(module_name));
            return Ok(format!("{package}.{struct_name}"));
        }
        if let Some(name) = self.record_names.get(&monotype) {
            return Ok(name.clone());
        }
        let Monotype::Record(fields) = self.monotypes.get(monotype).clone() else {
            unreachable!("invariant violated: record name requested for a non-record")
        };
        let base: String = if fields.is_empty() {
            "Empty".into()
        } else {
            fields.iter().map(|field| capitalise(&identifier(&field.label))).collect()
        };
        let name = self.pending_global(base, names::PendingSpelling::Record(monotype));
        self.record_names.insert(monotype, name.clone());
        let type_ = self.record_declaration(monotype)?;
        self.type_declarations.push(GoDeclaration::Type { name: name.clone(), type_ });
        Ok(name)
    }

    /// A data type's global: its name followed by its type arguments.
    pub(super) fn data_type_global(&mut self, data: &DataType) -> GoResult<String> {
        if let Some(labels) = self.variant_labels(data)? {
            let full = format!("Variant{labels}");
            let parts = vec![
                names::NamePart::Stutter("Variant".into()),
                names::NamePart::Text(labels),
            ];
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
        let labels: String =
            constructors.iter().map(|constructor| capitalise(&identifier(&constructor.name))).collect();
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
        let kind = if constructors.iter().all(|constructor| constructor.fields.is_empty()) {
            DataKind::Enumeration
        } else if constructors.len() == 1 {
            DataKind::Product
        } else {
            DataKind::Tagged
        };
        let plan = match kind {
            DataKind::Enumeration => None,
            DataKind::Tagged | DataKind::Product => Some(self.plan_slots(&constructors)?),
        };
        let mut layouts = vec![];
        for (index, constructor) in constructors.iter().enumerate() {
            let tag = self.global_name(Spelling::derived(
                "",
                name.clone(),
                &capitalise(&identifier(&constructor.name)),
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
        };
        self.data_layouts.insert(data.clone(), layout.clone());
        let names: Vec<String> =
            layouts.iter().map(|constructor| constructor.tag.clone()).collect();
        let Some(plan) = plan else {
            self.type_declarations.push(GoDeclaration::Type {
                name: name.clone(),
                type_: layout::tag_type(constructors.len()),
            });
            if !names.is_empty() {
                let constants = GoDeclaration::Constants { type_name: Some(name), names };
                self.type_declarations.push(constants);
            }
            return Ok(layout);
        };
        let mut fields = vec![];
        for slot in plan.slots {
            fields.push(match slot {
                layout::Slot::Tag => ("Tag".to_string(), layout::tag_type(constructors.len())),
                layout::Slot::Field { name, monotype } => (name, self.go_type(monotype)?),
            });
        }
        if let Some(layout) = self.data_layouts.get_mut(data) {
            layout.declaration = Some(self.type_declarations.len());
        }
        self.type_declarations
            .push(GoDeclaration::Type { name: name.clone(), type_: GoType::Struct(fields) });
        if kind == DataKind::Tagged {
            self.type_declarations.push(GoDeclaration::Constants { type_name: None, names });
        }
        Ok(self.data_layouts.get(data).cloned().unwrap_or(layout))
    }

    pub(super) fn contains_itself(&mut self, data: &DataType) -> GoResult<bool> {
        let mut pending: Vec<MonotypeId> = vec![];
        let mut visited: FxHashSet<DataType> = FxHashSet::default();
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
                Monotype::Recursive(_) => return Ok(true),
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
        let limit = if self.copied_by_containers.contains(data) {
            INLINE_DATA_LIMIT
        } else {
            TRANSIENT_DATA_LIMIT
        };
        Ok(shape.size() > limit)
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
            && !fields.iter().any(|(name, _)| name == "Origin")
        {
            fields.insert(layout.origin_position, ("Origin".to_string(), GoType::Any));
        }
        Ok(true)
    }
}

/// `*lazy.Lazy[T]` and the like: a generic instantiation, behind pointers.
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
        GoType::Struct(fields) => fields.iter_mut().map(|(_, field)| field).collect(),
        _ => vec![],
    };
    for type_ in inner {
        spell_out_arguments(type_, aliases, generic, in_argument);
    }
}
