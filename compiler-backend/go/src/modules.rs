//! The program's module import graph, which decides where generated Go may
//! live: a Go package can only refer to the packages of modules its module
//! imports, directly or not, or Go would see an import cycle.

use files::FileId;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::context::Context;
use crate::error::GoResult;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleIndex(pub u32);

pub struct Modules {
    files: Vec<FileId>,
    names: Vec<SmolStr>,
    index: FxHashMap<FileId, ModuleIndex>,
    /// Each module's transitive imports, the module itself included.
    sees: Vec<ModuleSet>,
    /// The qualifier each module imports other modules under, directly or
    /// through a module that re-exports them.
    qualifiers: Vec<FxHashMap<ModuleIndex, SmolStr>>,
    entry: ModuleIndex,
}

impl Modules {
    /// The modules the entry module imports, directly or not, and itself.
    pub fn collect<Q>(context: &mut Context<'_, Q>, entry: FileId) -> GoResult<Modules>
    where
        Q: checking::ExternalQueries,
    {
        let mut files = vec![];
        let mut index = FxHashMap::default();
        let mut imports: Vec<Vec<ModuleIndex>> = vec![];
        let mut qualified: Vec<Vec<(SmolStr, FileId)>> = vec![];
        let mut reexports: Vec<Vec<FileId>> = vec![];
        let mut pending = vec![entry];
        index.insert(entry, ModuleIndex(0));
        files.push(entry);
        imports.push(vec![]);
        qualified.push(vec![]);
        reexports.push(vec![]);
        while let Some(file) = pending.pop() {
            let at = index[&file];
            let resolved = context.queries.resolved(file)?;
            for (qualifier, qualified_imports) in &resolved.qualified {
                for import in qualified_imports {
                    qualified[at.0 as usize].push((qualifier.clone(), import.file));
                }
            }
            reexports[at.0 as usize] = resolved
                .unqualified
                .values()
                .chain(resolved.qualified.values())
                .flatten()
                .filter(|import| import.exported)
                .map(|import| import.file)
                .collect();
            let mut imported: Vec<FileId> = resolved
                .unqualified
                .values()
                .chain(resolved.qualified.values())
                .flatten()
                .map(|import| import.file)
                .filter(|&imported| imported != file)
                .collect();
            imported.sort_unstable();
            imported.dedup();
            for imported in imported {
                let target = *index.entry(imported).or_insert_with(|| {
                    files.push(imported);
                    imports.push(vec![]);
                    qualified.push(vec![]);
                    reexports.push(vec![]);
                    pending.push(imported);
                    ModuleIndex(files.len() as u32 - 1)
                });
                imports[at.0 as usize].push(target);
            }
        }
        let mut names = Vec::with_capacity(files.len());
        for &file in &files {
            names.push(context.module(file)?.name.clone());
        }
        let sees = transitive_closure(&imports);
        let qualifiers = qualified
            .into_iter()
            .map(|qualified| {
                let mut qualifiers: FxHashMap<ModuleIndex, SmolStr> = FxHashMap::default();
                for (qualifier, file) in &qualified {
                    qualifiers.insert(index[file], qualifier.clone());
                }
                for (qualifier, file) in &qualified {
                    for reexported in &reexports[index[file].0 as usize] {
                        qualifiers.entry(index[reexported]).or_insert_with(|| qualifier.clone());
                    }
                }
                qualifiers
            })
            .collect();
        Ok(Modules { files, names, index, sees, qualifiers, entry: ModuleIndex(0) })
    }

    /// The qualifier code in `module` refers to `imported` by, if any.
    pub fn qualifier(&self, module: ModuleIndex, imported: ModuleIndex) -> Option<&str> {
        self.qualifiers[module.0 as usize].get(&imported).map(SmolStr::as_str)
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn entry(&self) -> ModuleIndex {
        self.entry
    }

    pub fn index(&self, file: FileId) -> Option<ModuleIndex> {
        self.index.get(&file).copied()
    }

    pub fn file(&self, module: ModuleIndex) -> FileId {
        self.files[module.0 as usize]
    }

    pub fn name(&self, module: ModuleIndex) -> &str {
        &self.names[module.0 as usize]
    }

    /// Whether code in `from` may refer to code in `to`.
    pub fn sees(&self, from: ModuleIndex, to: ModuleIndex) -> bool {
        self.sees[from.0 as usize].contains(to)
    }

    pub fn seen_by(&self, from: ModuleIndex) -> &ModuleSet {
        &self.sees[from.0 as usize]
    }

    /// The home of a declaration that stands for declarations of these homes:
    /// the one every other sees, so that all their users still see it, if any.
    pub fn common_home(&self, homes: &[Option<ModuleIndex>]) -> Option<ModuleIndex> {
        let homes: Vec<ModuleIndex> = homes.iter().copied().collect::<Option<_>>()?;
        homes.iter().copied().find(|&home| homes.iter().all(|&other| self.sees(other, home)))
    }
}

fn transitive_closure(imports: &[Vec<ModuleIndex>]) -> Vec<ModuleSet> {
    let count = imports.len();
    let mut sees: Vec<Option<ModuleSet>> = vec![None; count];
    // Imports are acyclic, so a depth-first post-order visits every module
    // after the modules it imports.
    let mut work: Vec<(usize, usize)> = vec![];
    for root in 0..count {
        if sees[root].is_some() {
            continue;
        }
        work.push((root, 0));
        while let Some(&mut (module, ref mut next)) = work.last_mut() {
            if let Some(&target) = imports[module].get(*next) {
                *next += 1;
                if sees[target.0 as usize].is_none() {
                    work.push((target.0 as usize, 0));
                }
                continue;
            }
            work.pop();
            let mut set = ModuleSet::new(count);
            set.insert(ModuleIndex(module as u32));
            for target in &imports[module] {
                if let Some(seen) = &sees[target.0 as usize] {
                    set.union(seen);
                }
            }
            sees[module] = Some(set);
        }
    }
    sees.into_iter().map(|set| set.expect("invariant violated: module not visited")).collect()
}

/// A set of modules, as a bit set over their indices.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModuleSet {
    words: Vec<u64>,
}

impl ModuleSet {
    pub fn new(count: usize) -> ModuleSet {
        ModuleSet { words: vec![0; count.div_ceil(64)] }
    }

    pub fn insert(&mut self, module: ModuleIndex) {
        self.words[module.0 as usize / 64] |= 1 << (module.0 % 64);
    }

    pub fn contains(&self, module: ModuleIndex) -> bool {
        self.words[module.0 as usize / 64] & (1 << (module.0 % 64)) != 0
    }

    pub fn union(&mut self, other: &ModuleSet) {
        for (word, other) in self.words.iter_mut().zip(&other.words) {
            *word |= other;
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = ModuleIndex> + '_ {
        self.words.iter().enumerate().flat_map(|(position, &word)| {
            (0..64)
                .filter(move |bit| word & (1 << bit) != 0)
                .map(move |bit| ModuleIndex((position * 64 + bit) as u32))
        })
    }
}
