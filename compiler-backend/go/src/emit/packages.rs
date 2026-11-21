//! Splits the program's Go declarations into one package per PureScript
//! module, so that the output reads like the source.
//!
//! A declaration needs its home module (a function's origin, a data type's
//! defining module) and every module that what it refers to needs. It lives
//! in the needed module that sees all the others: a specialization of
//! `Data.Map.insert` at a type of the program's own modules lives with that
//! type, since its module imports `Data.Map` and Go forbids import cycles.
//! Without such a module, a declaration that one package alone uses lives
//! there; any other lives in the shared package when it needs no module (a
//! record type of primitive fields), or else in a package of its own where
//! the modules it needs meet. Placement never copies a declaration, so every
//! type keeps one identity.

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::error::{GoError, GoResult};
use crate::graph::strongly_connected;
use crate::modules::{ModuleIndex, ModuleSet, Modules};
use crate::naming::{RESERVED, capitalise, exported, go_safe, lower_camel, numbered, resolve};
use crate::syntax::{GoDeclaration, GoExpression, GoFile, GoImport, Reference};

/// How a global name was formed, so that each package can spell it anew.
#[derive(Debug, Clone)]
pub(crate) enum Spelling {
    Base(String),
    /// Candidates from shortest to longest, the longer ones for collisions.
    Ladder(Vec<String>),
    /// A name that spells records, such as a data type's applied to one, by
    /// the names those records end up with; else by `full`.
    Composed {
        parts: Vec<SpelledPart>,
        full: String,
    },
    /// A name formed from another, such as a constructor's tag from its type.
    Derived {
        prefix: &'static str,
        parent: String,
        suffix: String,
    },
}

#[derive(Debug, Clone)]
pub(crate) enum SpelledPart {
    Text(String),
    /// A record, by its global if it is declared, else by `name`.
    Record {
        global: Option<String>,
        name: String,
    },
    Stutter(String),
}

impl Spelling {
    pub(crate) fn derived(prefix: &'static str, parent: String, suffix: &str) -> Spelling {
        Spelling::Derived { prefix, parent, suffix: suffix.to_string() }
    }

    /// The name as the whole program spells it.
    pub(crate) fn text(&self) -> String {
        match self {
            Spelling::Base(base) => base.clone(),
            Spelling::Ladder(ladder) => ladder[0].clone(),
            Spelling::Composed { full, .. } => full.clone(),
            Spelling::Derived { prefix: "", parent, suffix } => format!("{parent}{suffix}"),
            Spelling::Derived { prefix, parent, suffix } => {
                format!("{prefix}{}{suffix}", capitalise(parent))
            }
        }
    }
}

/// One generated Go source file, at a path relative to the output directory.
pub struct GoSourceFile {
    pub path: String,
    pub file: GoFile,
}

pub(super) struct Packaging<'a> {
    pub modules: &'a Modules,
    /// The Go module path that package import paths start with.
    pub module_path: &'a str,
    pub spellings: &'a FxHashMap<String, Spelling>,
    /// The paths of the standard and support packages the program imports.
    pub imports: &'a BTreeSet<String>,
    /// The records whose Go names name values, by their tokens' indices.
    pub typed_records: &'a [Option<String>],
}

/// Declarations that move together: a type and its constructors' tags.
struct Unit {
    declarations: Vec<GoDeclaration>,
    names: Vec<String>,
    home: Option<ModuleIndex>,
}

/// A package declarations can live in. Each module has one; declarations
/// that need no module share one; and declarations that need several modules
/// none of which sees the others meet in a package of their own.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Place(u32);

struct Places<'a> {
    modules: &'a Modules,
    /// The modules each place stands for, none of which sees another: its
    /// module, none for the shared place, or the modules that meet in it.
    meeting: Vec<Vec<ModuleIndex>>,
    /// The modules each place's code may refer to.
    sees: Vec<ModuleSet>,
    index: FxHashMap<Vec<ModuleIndex>, Place>,
}

impl Places<'_> {
    fn new(modules: &Modules) -> Places<'_> {
        let mut places =
            Places { modules, meeting: vec![], sees: vec![], index: FxHashMap::default() };
        for module in 0..modules.len() {
            places.intern(vec![ModuleIndex(module as u32)]);
        }
        places
    }

    fn module(&self, module: ModuleIndex) -> Place {
        Place(module.0)
    }

    fn intern(&mut self, meeting: Vec<ModuleIndex>) -> Place {
        if let Some(&place) = self.index.get(&meeting) {
            return place;
        }
        let place = Place(self.meeting.len() as u32);
        let mut sees = ModuleSet::new(self.modules.len());
        for &module in &meeting {
            sees.union(self.modules.seen_by(module));
        }
        self.meeting.push(meeting.clone());
        self.sees.push(sees);
        self.index.insert(meeting, place);
        place
    }

    /// The place for code that needs exactly these modules: the needed module
    /// that sees all the others, or else where the needed modules that no
    /// other needed module sees meet.
    fn needing(&mut self, need: &ModuleSet) -> Place {
        let upstream: Vec<ModuleIndex> = need
            .iter()
            .filter(|&module| {
                !need.iter().any(|other| other != module && self.modules.sees(other, module))
            })
            .collect();
        self.intern(upstream)
    }

    /// Whether code in one place may refer to code in another.
    fn sees(&self, from: Place, to: Place) -> bool {
        let sees = &self.sees[from.0 as usize];
        self.meeting[to.0 as usize].iter().all(|&module| sees.contains(module))
    }

    fn meeting(&self, place: Place) -> &[ModuleIndex] {
        &self.meeting[place.0 as usize]
    }
}

#[derive(Default, Debug)]
pub(super) struct PlacementCensus {
    pub in_a_module: usize,
    pub with_their_user: usize,
    pub shared: usize,
    pub meeting: usize,
}

impl Packaging<'_> {
    pub(super) fn split(
        &self,
        declarations: Vec<(GoDeclaration, Option<ModuleIndex>)>,
    ) -> GoResult<Vec<GoSourceFile>> {
        let mut units = units(declarations);
        let mut unit_of: FxHashMap<String, usize> = FxHashMap::default();
        for (index, unit) in units.iter().enumerate() {
            for name in &unit.names {
                unit_of.insert(name.clone(), index);
            }
        }
        let references = self.references(&mut units, &unit_of);
        let mut places = Places::new(self.modules);
        let placements = self.place(&units, &references, &mut places);
        let packages = self.packages(&placements, &places)?;
        self.render(units, &unit_of, &placements, &places, &packages)
    }

    /// The units each unit refers to.
    fn references(
        &self,
        units: &mut [Unit],
        unit_of: &FxHashMap<String, usize>,
    ) -> Vec<Vec<usize>> {
        units
            .iter_mut()
            .enumerate()
            .map(|(index, unit)| {
                let mut targets = BTreeSet::new();
                for declaration in &mut unit.declarations {
                    declaration.for_each_reference_mut(&mut |reference| {
                        let name = match reference {
                            Reference::Value(GoExpression::Identifier(name)) => name,
                            Reference::Type(name) => name,
                            _ => return,
                        };
                        if let Some(&target) = unit_of.get(name.as_str())
                            && target != index
                        {
                            targets.insert(target);
                        }
                    });
                }
                targets.into_iter().collect()
            })
            .collect()
    }

    /// The place of each unit. A unit needs its home and whatever the units
    /// it refers to need; mutually recursive units need the same.
    fn place(&self, units: &[Unit], references: &[Vec<usize>], places: &mut Places) -> Vec<Place> {
        let components = strongly_connected(references);
        let mut component_of = vec![0; units.len()];
        for (index, component) in components.iter().enumerate() {
            for &unit in component {
                component_of[unit] = index;
            }
        }
        // Components come callees first, so what a component refers to is
        // already known.
        let mut needs: Vec<ModuleSet> = Vec::with_capacity(components.len());
        for (index, component) in components.iter().enumerate() {
            let mut need = ModuleSet::new(self.modules.len());
            for &unit in component {
                if let Some(home) = units[unit].home {
                    need.insert(home);
                }
                for &target in &references[unit] {
                    let target = component_of[target];
                    if target != index {
                        need.union(&needs[target]);
                    }
                }
            }
            needs.push(need);
        }
        let mut users: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); components.len()];
        for (unit, targets) in references.iter().enumerate() {
            for &target in targets {
                if component_of[target] != component_of[unit] {
                    users[component_of[target]].insert(component_of[unit]);
                }
            }
        }
        let mut census = PlacementCensus::default();
        let mut placements: Vec<Option<Place>> = vec![None; components.len()];
        let entry = places.module(self.modules.entry());
        // Users come before what they use.
        for index in (0..components.len()).rev() {
            let natural = places.needing(&needs[index]);
            let user_places: BTreeSet<Place> = users[index]
                .iter()
                .map(|&user| {
                    placements[user]
                        .expect("invariant violated: a user is placed after what it uses")
                })
                .collect();
            let only_user = match user_places.len() {
                1 => user_places.first().copied(),
                _ => None,
            };
            let natural_needs_entry = places.sees(natural, entry);
            let only_user = only_user.filter(|&user| user != entry || natural_needs_entry);
            let homeless = components[index].iter().all(|&unit| units[unit].home.is_none());
            let place = match (places.meeting(natural), only_user) {
                // Code of a module's own lives there.
                ([_], _) if !homeless => {
                    census.in_a_module += 1;
                    natural
                }
                // Code of no module's own, or of modules that do not see each
                // other, that one package alone uses lives there, like a
                // private helper.
                (_, Some(user)) => {
                    census.with_their_user += 1;
                    user
                }
                ([_], None) => {
                    census.in_a_module += 1;
                    natural
                }
                ([], None) => {
                    census.shared += 1;
                    natural
                }
                (_, None) => {
                    census.meeting += 1;
                    natural
                }
            };
            placements[index] = Some(place);
        }
        if std::env::var_os("IRIS_GO_PLACEMENT_CENSUS").is_some() {
            eprintln!("{census:?}");
        }
        (0..units.len())
            .map(|unit| {
                placements[component_of[unit]].expect("invariant violated: unit left unplaced")
            })
            .collect()
    }

    /// The Go package of each place that holds declarations.
    fn packages(
        &self,
        placements: &[Place],
        places: &Places,
    ) -> GoResult<FxHashMap<Place, Package>> {
        let entry = places.module(self.modules.entry());
        let shared_directory = self.shared_directory();
        let mut packages: FxHashMap<Place, Package> = FxHashMap::default();
        for &place in placements {
            if packages.contains_key(&place) {
                continue;
            }
            if place != entry && places.sees(place, entry) {
                return Err(GoError::EntryImported {
                    entry: self.modules.name(self.modules.entry()).to_string(),
                    importer: places
                        .meeting(place)
                        .iter()
                        .map(|&module| self.modules.name(module))
                        .collect::<Vec<_>>()
                        .join(", "),
                });
            }
            let package = match places.meeting(place) {
                _ if place == entry => Package::root(),
                [module] => Package::module(self.modules.name(*module)),
                [] => Package::shared(&shared_directory),
                meeting => {
                    let names: Vec<&str> =
                        meeting.iter().map(|&module| self.modules.name(module)).collect();
                    Package::meeting(&shared_directory, &names)
                }
            };
            packages.insert(place, package);
        }
        Ok(packages)
    }

    /// The directory of the shared package, which no module's may be.
    fn shared_directory(&self) -> String {
        let mut directory = "shared".to_string();
        let taken = |directory: &str| {
            (0..self.modules.len()).any(|module| {
                let name = self.modules.name(ModuleIndex(module as u32));
                let first = name.split('.').next().unwrap_or(name);
                directory_segment(first).eq_ignore_ascii_case(directory)
            })
        };
        while taken(&directory) {
            directory.push('_');
        }
        directory
    }

    fn render(
        &self,
        mut units: Vec<Unit>,
        unit_of: &FxHashMap<String, usize>,
        placements: &[Place],
        places: &Places,
        packages: &FxHashMap<Place, Package>,
    ) -> GoResult<Vec<GoSourceFile>> {
        let mut contents: FxHashMap<Place, Vec<usize>> = FxHashMap::default();
        for (unit, &place) in placements.iter().enumerate() {
            contents.entry(place).or_default().push(unit);
        }
        let root = packages
            .iter()
            .find(|(_, package)| package.directory.is_empty())
            .map(|(&place, _)| place);
        let mut members: FxHashMap<Place, Vec<String>> = FxHashMap::default();
        let mut binders: FxHashMap<Place, FxHashSet<String>> = FxHashMap::default();
        for (&place, place_units) in &contents {
            let place_binders = binders.entry(place).or_default();
            for &unit in place_units {
                members.entry(place).or_default().extend(units[unit].names.iter().cloned());
                for declaration in &mut units[unit].declarations {
                    declaration.for_each_reference_mut(&mut |reference| {
                        if let Reference::Binder(name) = reference
                            && !super::locals::is_marked(name)
                        {
                            place_binders.insert(name.clone());
                        }
                    });
                }
            }
        }
        let homes: Vec<Option<ModuleIndex>> = units.iter().map(|unit| unit.home).collect();
        let mut naming = Naming {
            unit_of,
            placements,
            homes: &homes,
            spellings: self.spellings,
            root,
            members,
            binders,
            names: FxHashMap::default(),
            taken: FxHashMap::default(),
            named: FxHashSet::default(),
        };
        let mut ordered: Vec<Place> = contents.keys().copied().collect();
        ordered.sort_by(|left, right| packages[left].directory.cmp(&packages[right].directory));
        for &place in &ordered {
            for &unit in &contents[&place] {
                for name in &units[unit].names {
                    naming.name(name, place);
                }
            }
        }
        let record_values: Vec<String> = self
            .typed_records
            .iter()
            .map(|global| {
                let name = global.as_ref().and_then(|global| {
                    let &unit = unit_of.get(global.as_str())?;
                    Some(naming.name(global, placements[unit]))
                });
                let name = name.unwrap_or_else(|| "record".into());
                go_safe(&lower_camel(&name)).to_string()
            })
            .collect();
        let support = self.support_aliases();
        let mut files = vec![];
        for &place in &ordered {
            let package = &packages[&place];
            let mut declarations: Vec<GoDeclaration> = contents[&place]
                .iter()
                .flat_map(|&unit| std::mem::take(&mut units[unit].declarations))
                .collect();
            let mut support_imports = BTreeSet::new();
            let mut referenced: BTreeSet<Place> = BTreeSet::new();
            let mut avoided: FxHashSet<String> = FxHashSet::default();
            for declaration in &mut declarations {
                for name in declared_names(declaration) {
                    avoided.insert(naming.name(&name, place));
                }
                collect_support(declaration, &support, &mut support_imports);
                declaration.for_each_reference_mut(&mut |reference| match reference {
                    Reference::Binder(name) => {
                        if !super::locals::is_marked(name) {
                            avoided.insert(name.clone());
                        }
                    }
                    Reference::Value(GoExpression::Identifier(name)) | Reference::Type(name) => {
                        if let Some(&target) = unit_of.get(name.as_str())
                            && placements[target] != place
                        {
                            referenced.insert(placements[target]);
                        }
                    }
                    Reference::Value(_) => {}
                });
            }
            let qualifiers: FxHashMap<Place, String> = match places.meeting(place) {
                [module] => referenced
                    .iter()
                    .filter_map(|&target| {
                        let [imported] = places.meeting(target) else { return None };
                        let qualifier = self.modules.qualifier(*module, *imported)?;
                        Some((target, lowercase(qualifier)))
                    })
                    .collect(),
                _ => FxHashMap::default(),
            };
            let support_aliases = alias_shadowed_support(&support_imports, &support, &mut avoided);
            let aliases = choose_aliases(&referenced, packages, &qualifiers, &avoided, &support);
            for declaration in &mut declarations {
                rename_declared(declaration, &mut |name| naming.name(name, place));
                declaration.for_each_reference_mut(&mut |reference| match reference {
                    Reference::Value(expression) => {
                        let GoExpression::Identifier(name) = expression else { return };
                        let Some(&target) = unit_of.get(name.as_str()) else { return };
                        let home = placements[target];
                        let renamed = naming.name(name, home);
                        *expression = if home == place {
                            GoExpression::Identifier(renamed)
                        } else {
                            GoExpression::Qualified {
                                package: aliases[&home].clone(),
                                name: renamed,
                            }
                        };
                    }
                    Reference::Type(name) => {
                        let Some(&target) = unit_of.get(name.as_str()) else { return };
                        let home = placements[target];
                        let renamed = naming.name(name, home);
                        *name = if home == place {
                            renamed
                        } else {
                            format!("{}.{renamed}", aliases[&home])
                        };
                    }
                    Reference::Binder(_) => {}
                });
                super::locals::settle(declaration, &record_values);
                requalify_support(declaration, &support_aliases);
            }
            let mut imports: Vec<GoImport> = support_imports
                .into_iter()
                .map(|path| {
                    let alias = support_aliases
                        .iter()
                        .find(|(name, _)| support.get(*name) == Some(&path))
                        .map(|(_, alias)| alias.clone());
                    GoImport { path, alias }
                })
                .collect();
            for home in &referenced {
                let target = &packages[home];
                let alias = &aliases[home];
                let path = format!("{}/{}", self.module_path, target.directory);
                let alias = (*alias != target.name).then(|| alias.clone());
                imports.push(GoImport { path, alias });
            }
            imports.sort();
            let file =
                GoFile { constraint: None, package: package.name.clone(), imports, declarations };
            files.push(GoSourceFile { path: package.file_path(), file });
        }
        Ok(files)
    }

    /// The name each standard or support package is imported as.
    fn support_aliases(&self) -> FxHashMap<String, String> {
        self.imports
            .iter()
            .map(|path| {
                let alias = path.rsplit('/').next().unwrap_or(path).to_string();
                (alias, path.clone())
            })
            .collect()
    }
}

struct Package {
    /// The package's directory relative to the output, empty for the root.
    directory: String,
    /// The name its `package` clause declares.
    name: String,
    /// The file it is written to, relative to its directory.
    file: String,
    /// Names a file importing the package may call it by, best first.
    aliases: Vec<String>,
}

impl Package {
    fn root() -> Package {
        Package {
            directory: String::new(),
            name: "main".into(),
            file: "main.go".into(),
            aliases: vec![],
        }
    }

    /// A module's package, in a directory per segment of its name and named
    /// after its last segment.
    fn module(module_name: &str) -> Package {
        let segments: Vec<&str> = module_name.split('.').collect();
        let directory: Vec<String> =
            segments.iter().map(|segment| directory_segment(segment)).collect();
        let aliases = suffix_names(&segments);
        let name = aliases.first().cloned().unwrap_or_else(|| "module".into());
        let file = format!("{}.go", lowercase(segments.last().unwrap_or(&module_name)));
        Package { directory: directory.join("/"), name, file, aliases }
    }

    fn shared(directory: &str) -> Package {
        Package {
            directory: directory.into(),
            name: "shared".into(),
            file: "shared.go".into(),
            aliases: vec!["shared".into()],
        }
    }

    /// The package where code needing modules that do not see each other
    /// meets, named after them.
    fn meeting(shared: &str, modules: &[&str]) -> Package {
        let lasts: Vec<String> = modules
            .iter()
            .map(|module| lowercase(module.rsplit('.').next().unwrap_or(module)))
            .collect();
        let name = lasts.join("_");
        let name = if is_package_name(&name) { name } else { format!("{name}_") };
        Package {
            directory: format!("{shared}/{}", modules.join("+")),
            file: format!("{name}.go"),
            aliases: vec![name.clone()],
            name,
        }
    }

    fn file_path(&self) -> String {
        if self.directory.is_empty() {
            return self.file.clone();
        }
        format!("{}/{}", self.directory, self.file)
    }
}

fn lowercase(segment: &str) -> String {
    segment
        .chars()
        .filter(|character| character.is_alphanumeric())
        .flat_map(char::to_lowercase)
        .collect()
}

/// The module's last segment, then it joined with each earlier one, in
/// lower case, leaving out those that are reserved words.
fn suffix_names(segments: &[&str]) -> Vec<String> {
    let mut names = vec![];
    let mut joined = String::new();
    for segment in segments.iter().rev() {
        joined.insert_str(0, &lowercase(segment));
        if is_package_name(&joined) && !names.contains(&joined) {
            names.push(joined.clone());
        }
    }
    names
}

/// A module name segment as a directory: Go ignores directories starting
/// with `.` or `_`, and gives `internal`, `vendor` and `testdata` meaning.
fn directory_segment(segment: &str) -> String {
    let mut directory: String = segment
        .chars()
        .map(|character| if character.is_alphanumeric() { character } else { '_' })
        .collect();
    if directory.is_empty() || directory.starts_with('_') {
        directory.insert(0, 'X');
    }
    if matches!(directory.as_str(), "internal" | "vendor" | "testdata") {
        directory.push('_');
    }
    directory
}

/// Whether a package may be called this: an identifier that is no Go
/// reserved word, nor the name of a package with special meaning.
fn is_package_name(name: &str) -> bool {
    !name.is_empty()
        && !name.starts_with(|character: char| character.is_ascii_digit())
        && !RESERVED.contains(&name)
        && !matches!(name, "unsafe" | "reflect" | "builtin" | "C")
}

/// Aliases for the packages a file imports: the qualifier the PureScript
/// module imports it under, else the package's name, else a longer name from
/// its module's, whichever nothing else in the file uses.
fn choose_aliases(
    referenced: &BTreeSet<Place>,
    packages: &FxHashMap<Place, Package>,
    qualifiers: &FxHashMap<Place, String>,
    avoided: &FxHashSet<String>,
    support: &FxHashMap<String, String>,
) -> FxHashMap<Place, String> {
    let mut taken: FxHashSet<String> = avoided.clone();
    taken.extend(support.keys().cloned());
    let mut aliases = FxHashMap::default();
    for &place in referenced {
        let package = &packages[&place];
        let qualifier = qualifiers.get(&place).filter(|qualifier| is_package_name(qualifier));
        let mut candidates = qualifier.into_iter().chain(&package.aliases);
        let alias = match candidates.find(|alias| !taken.contains(*alias)) {
            Some(alias) => alias.clone(),
            None => {
                let base = package.aliases.last().cloned().unwrap_or_else(|| package.name.clone());
                (2..)
                    .map(|counter| format!("{base}{counter}"))
                    .find(|candidate| !taken.contains(candidate))
                    .expect("invariant violated: no free alias")
            }
        };
        taken.insert(alias.clone());
        aliases.insert(place, alias);
    }
    aliases
}

/// Aliases for the standard and support packages a file imports whose names a local of the
/// file has: the local keeps its name, and the package is imported as `avarpkg`.
fn alias_shadowed_support(
    imports: &BTreeSet<String>,
    support: &FxHashMap<String, String>,
    avoided: &mut FxHashSet<String>,
) -> FxHashMap<String, String> {
    let mut aliases = FxHashMap::default();
    let mut shadowed: Vec<&String> = support
        .iter()
        .filter(|(name, path)| imports.contains(*path) && avoided.contains(*name))
        .map(|(name, _)| name)
        .collect();
    shadowed.sort();
    for name in shadowed {
        let base = format!("{name}pkg");
        let alias = crate::naming::numbered(&base, |candidate| {
            avoided.contains(candidate) || support.contains_key(candidate)
        });
        avoided.insert(alias.clone());
        aliases.insert(name.clone(), alias);
    }
    aliases
}

/// The declaration with its references to shadowed support packages under their aliases.
fn requalify_support(declaration: &mut GoDeclaration, aliases: &FxHashMap<String, String>) {
    if aliases.is_empty() {
        return;
    }
    declaration.for_each_reference_mut(&mut |reference| match reference {
        Reference::Value(GoExpression::Qualified { package, .. }) => {
            if let Some(alias) = aliases.get(package.as_str()) {
                *package = alias.clone();
            }
        }
        Reference::Type(name) => *name = requalified(name, aliases),
        Reference::Value(_) | Reference::Binder(_) => {}
    });
}

/// A type's spelling with each qualifier in `aliases` replaced by its alias.
fn requalified(text: &str, aliases: &FxHashMap<String, String>) -> String {
    let mut spelled = String::with_capacity(text.len());
    let mut word = String::new();
    for character in text.chars() {
        if character.is_alphanumeric() || character == '_' {
            word.push(character);
            continue;
        }
        match aliases.get(&word) {
            Some(alias) if character == '.' => spelled.push_str(alias),
            _ => spelled.push_str(&word),
        }
        word.clear();
        spelled.push(character);
    }
    spelled.push_str(&word);
    spelled
}

/// The standard and support packages a declaration refers to.
fn collect_support(
    declaration: &mut GoDeclaration,
    support: &FxHashMap<String, String>,
    imports: &mut BTreeSet<String>,
) {
    let mut packages: Vec<String> = vec![];
    declaration.for_each_reference_mut(&mut |reference| match reference {
        Reference::Type(name) => packages.extend(qualifiers(name)),
        Reference::Value(GoExpression::Qualified { package, .. }) => packages.push(package.clone()),
        Reference::Value(_) | Reference::Binder(_) => {}
    });
    for package in packages {
        if let Some(path) = support.get(&package) {
            imports.insert(path.clone());
        }
    }
}

/// The package qualifiers in a type's spelling, such as `regex` in `regex.Regex`.
fn qualifiers(text: &str) -> Vec<String> {
    let mut qualifiers = vec![];
    let mut start = 0;
    for (at, character) in text.char_indices() {
        if character == '.' {
            qualifiers.push(text[start..at].to_string());
        }
        if !(character.is_alphanumeric() || character == '_') {
            start = at + character.len_utf8();
        }
    }
    qualifiers
}

fn declared_names(declaration: &GoDeclaration) -> Vec<String> {
    match declaration {
        GoDeclaration::Constants { names, .. } => names.clone(),
        declaration => declaration.name().map(str::to_string).into_iter().collect(),
    }
}

fn rename_declared(declaration: &mut GoDeclaration, rename: &mut impl FnMut(&str) -> String) {
    match declaration {
        GoDeclaration::Constants { names, .. } => {
            for name in names {
                *name = rename(name);
            }
        }
        GoDeclaration::Type { name, .. }
        | GoDeclaration::Alias { name, .. }
        | GoDeclaration::GenericType { name, .. }
        | GoDeclaration::Source { name, .. }
        | GoDeclaration::Written { name, .. }
        | GoDeclaration::Constant { name, .. }
        | GoDeclaration::Variable { name, .. }
        | GoDeclaration::Function { name, .. } => *name = rename(name),
    }
}

/// Groups declarations into units: each type keeps its tags' constants.
fn units(declarations: Vec<(GoDeclaration, Option<ModuleIndex>)>) -> Vec<Unit> {
    let mut units: Vec<Unit> = vec![];
    for (declaration, home) in declarations {
        if let GoDeclaration::Constants { names, .. } = &declaration
            && let Some(unit) = units.last_mut()
            && let Some(GoDeclaration::Type { .. }) = unit.declarations.first()
        {
            unit.names.extend(names.iter().cloned());
            unit.declarations.push(declaration);
            continue;
        }
        let names = declared_names(&declaration);
        units.push(Unit { declarations: vec![declaration], names, home });
    }
    units
}

/// Names declarations per package: exported in every package but the root,
/// whose declarations no other package imports. A package's own names are
/// chosen together, so that names that collide grow along their ladders;
/// names formed from another's follow, in the order they are asked for.
struct Naming<'a> {
    unit_of: &'a FxHashMap<String, usize>,
    placements: &'a [Place],
    homes: &'a [Option<ModuleIndex>],
    spellings: &'a FxHashMap<String, Spelling>,
    root: Option<Place>,
    /// The globals each place declares, in declaration order.
    members: FxHashMap<Place, Vec<String>>,
    /// The local names in each place's code, which no global may shadow.
    binders: FxHashMap<Place, FxHashSet<String>>,
    names: FxHashMap<String, String>,
    taken: FxHashMap<Place, FxHashSet<String>>,
    named: FxHashSet<Place>,
}

impl Naming<'_> {
    /// The name of a global, which lives in `place`, there.
    fn name(&mut self, global: &str, place: Place) -> String {
        if let Some(name) = self.names.get(global) {
            return name.clone();
        }
        self.name_place(place);
        if let Some(name) = self.names.get(global) {
            return name.clone();
        }
        let spelled = match self.spellings.get(global) {
            Some(Spelling::Derived { prefix, parent, suffix }) => {
                let parent_place = match self.unit_of.get(parent.as_str()) {
                    Some(&unit) => self.placements[unit],
                    None => place,
                };
                let parent = self.name(parent, parent_place);
                let parent = if prefix.is_empty() { parent } else { capitalise(&parent) };
                self.spelled(&format!("{prefix}{parent}{suffix}"), place)
            }
            _ => self.spelled(global, place),
        };
        let binders = self.binders.get(&place);
        let taken = self.taken.entry(place).or_default();
        let name = numbered(&spelled, |name| {
            binders.is_some_and(|binders| binders.contains(name)) || !taken.insert(name.to_string())
        });
        self.names.insert(global.to_string(), name.clone());
        name
    }

    /// Names the globals of a place that are not formed from another's: first
    /// those spelled on their own, then those that spell records, by the names
    /// the records got.
    fn name_place(&mut self, place: Place) {
        if !self.named.insert(place) {
            return;
        }
        let members = self.members.get(&place).cloned().unwrap_or_default();
        let (composed, simple): (Vec<String>, Vec<String>) = members
            .into_iter()
            .filter(|global| !matches!(self.spellings.get(global), Some(Spelling::Derived { .. })))
            .partition(|global| {
                matches!(self.spellings.get(global), Some(Spelling::Composed { .. }))
            });
        let simple_ladders: Vec<Vec<String>> = simple
            .iter()
            .map(|global| match self.spellings.get(global) {
                Some(Spelling::Base(base)) => vec![base.clone()],
                Some(Spelling::Ladder(ladder)) => ladder.clone(),
                _ => vec![global.clone()],
            })
            .collect();
        self.choose(place, simple, simple_ladders);
        let composed_ladders: Vec<Vec<String>> = composed
            .iter()
            .map(|global| {
                let Some(Spelling::Composed { parts, full }) = self.spellings.get(global) else {
                    unreachable!("invariant violated: a composed name lost its parts")
                };
                let (parts, full) = (parts.clone(), full.clone());
                let at_home = self.is_home(global, place);
                let mut spelled: Vec<String> = vec![];
                for part in &parts {
                    spelled.push(match part {
                        SpelledPart::Text(text) | SpelledPart::Stutter(text) => text.clone(),
                        SpelledPart::Record { global: Some(global), name } => {
                            self.record_name(global, place).unwrap_or_else(|| name.clone())
                        }
                        SpelledPart::Record { global: None, name } => name.clone(),
                    });
                }
                let stuttering = |keep_stutter: bool| -> Option<String> {
                    let kept =
                        parts.iter().zip(&spelled).enumerate().filter(|(index, (part, _))| {
                            !matches!(part, SpelledPart::Stutter(_))
                                || keep_stutter
                                || (*index == 0 && !at_home)
                        });
                    let text: String = kept.map(|(_, (_, text))| text.as_str()).collect();
                    (!text.is_empty()).then(|| super::identifier(&text))
                };
                let mut ladder: Vec<String> = [stuttering(false), stuttering(true), Some(full)]
                    .into_iter()
                    .flatten()
                    .collect();
                ladder.dedup();
                ladder
            })
            .collect();
        self.choose(place, composed, composed_ladders);
    }

    fn is_home(&self, global: &str, place: Place) -> bool {
        let Some(&unit) = self.unit_of.get(global) else { return false };
        self.homes[unit].is_some_and(|home| Place(home.0) == place)
    }

    /// The name a record's global got, as spelled in a name: unexported.
    fn record_name(&mut self, global: &str, place: Place) -> Option<String> {
        let home = self.unit_of.get(global).map(|&unit| self.placements[unit]).unwrap_or(place);
        if home != place && !self.named.contains(&home) {
            self.name_place(home);
        }
        let name = self.names.get(global)?;
        let ladder = match self.spellings.get(global) {
            Some(Spelling::Ladder(ladder)) => ladder,
            _ => return Some(name.clone()),
        };
        // Records are spelled in names as their ladder spells them, unexported.
        let spelled = ladder.iter().find(|candidate| self.spelled(candidate, home) == *name);
        Some(spelled.cloned().unwrap_or_else(|| name.clone()))
    }

    /// Gives globals of a place the names their ladders resolve to, beside
    /// the names already taken there.
    fn choose(&mut self, place: Place, globals: Vec<String>, ladders: Vec<Vec<String>>) {
        let ladders: Vec<Vec<String>> = ladders
            .iter()
            .map(|ladder| ladder.iter().map(|candidate| self.spelled(candidate, place)).collect())
            .collect();
        let empty = FxHashSet::default();
        let binders = self.binders.get(&place).unwrap_or(&empty);
        let taken = self.taken.get(&place).unwrap_or(&empty);
        let names = resolve(&ladders, &|name| binders.contains(name) || taken.contains(name));
        let taken = self.taken.entry(place).or_default();
        for (global, name) in globals.into_iter().zip(names) {
            taken.insert(name.clone());
            self.names.insert(global, name);
        }
    }

    /// A name as a place spells it: exported in every package but the root.
    fn spelled(&self, name: &str, place: Place) -> String {
        if Some(place) == self.root { name.to_string() } else { exported(name) }
    }
}
