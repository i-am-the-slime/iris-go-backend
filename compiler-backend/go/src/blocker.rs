use std::collections::BTreeMap;
use std::fmt;

use crate::error::UnsupportedState;

#[derive(Debug)]
pub struct Blocker {
    pub definition: String,
    pub state: UnsupportedState,
    pub requesters: Vec<String>,
    pub occurrences: usize,
}

#[derive(Debug)]
pub struct Blockers {
    pub blockers: Vec<Blocker>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BlockerKind {
    MissingForeign,
    ForeignData,
    Construct,
    SpecializationLimit,
    OpenType,
    UninstantiatedVariable,
    Evidence,
    Declaration,
    CheckerError,
}

impl BlockerKind {
    fn title(self) -> &'static str {
        match self {
            BlockerKind::MissingForeign => "missing foreign implementations",
            BlockerKind::ForeignData => "foreign data types without a representation",
            BlockerKind::Construct => "unsupported constructs",
            BlockerKind::SpecializationLimit => "specialization limits",
            BlockerKind::OpenType => "types without a closed representation",
            BlockerKind::UninstantiatedVariable => "uninstantiated type variables",
            BlockerKind::Evidence => "unresolved type class evidence",
            BlockerKind::Declaration => "missing declarations",
            BlockerKind::CheckerError => "checker errors",
        }
    }
}

impl UnsupportedState {
    pub fn kind(&self) -> BlockerKind {
        match self {
            UnsupportedState::UnknownForeign { .. } => BlockerKind::MissingForeign,
            UnsupportedState::ForeignData { .. } => BlockerKind::ForeignData,
            UnsupportedState::Construct { .. }
            | UnsupportedState::ReferenceEqualityAcrossTypes { .. } => BlockerKind::Construct,
            UnsupportedState::SpecializationLimit { .. } | UnsupportedState::GrowingEvidence => {
                BlockerKind::SpecializationLimit
            }
            UnsupportedState::OpenType { .. } | UnsupportedState::UnsaturatedType { .. } => {
                BlockerKind::OpenType
            }
            UnsupportedState::UninstantiatedVariable { .. } => BlockerKind::UninstantiatedVariable,
            UnsupportedState::UnsolvedEvidence
            | UnsupportedState::UnboundEvidence
            | UnsupportedState::UnabstractedEvidence
            | UnsupportedState::InstanceMismatch { .. }
            | UnsupportedState::MissingInstanceMember { .. }
            | UnsupportedState::MissingSuperclass { .. } => BlockerKind::Evidence,
            UnsupportedState::MissingDeclaration
            | UnsupportedState::MissingLocalDeclaration
            | UnsupportedState::MissingEquation => BlockerKind::Declaration,
            UnsupportedState::ExpressionError | UnsupportedState::BinderError => {
                BlockerKind::CheckerError
            }
        }
    }

    fn group(&self) -> String {
        match self {
            UnsupportedState::UnknownForeign { name } => match name.rsplit_once('.') {
                Some((module, _)) => module.to_string(),
                None => name.clone(),
            },
            UnsupportedState::ForeignData { name } => name.clone(),
            UnsupportedState::Construct { construct } => construct.to_string(),
            _ => self.to_string(),
        }
    }

    fn entry(&self, definition: &str) -> String {
        match self {
            UnsupportedState::UnknownForeign { name } => match name.rsplit_once('.') {
                Some((_, name)) => name.to_string(),
                None => name.clone(),
            },
            _ => definition.to_string(),
        }
    }
}

impl fmt::Display for Blockers {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for blocker in &self.blockers {
            writeln!(formatter, "cannot specialize {}: {}", blocker.definition, blocker.state)?;
            if !blocker.requesters.is_empty() {
                writeln!(formatter, "  requested by: {}", blocker.requesters.join(" <- "))?;
            }
            if blocker.occurrences > 1 {
                writeln!(formatter, "  reached {} times", blocker.occurrences)?;
            }
        }
        let mut kinds: BTreeMap<BlockerKind, BTreeMap<String, Vec<String>>> = BTreeMap::new();
        for blocker in &self.blockers {
            let entries = kinds
                .entry(blocker.state.kind())
                .or_default()
                .entry(blocker.state.group())
                .or_default();
            let entry = blocker.state.entry(&blocker.definition);
            if !entries.contains(&entry) {
                entries.push(entry);
            }
        }
        writeln!(formatter)?;
        writeln!(formatter, "{} blockers; no Go was written", self.blockers.len())?;
        for (kind, groups) in &kinds {
            let count: usize = groups.values().map(Vec::len).sum();
            writeln!(formatter, "  {} ({count}):", kind.title())?;
            for (group, entries) in groups {
                writeln!(formatter, "    {group} ({}): {}", entries.len(), entries.join(", "))?;
            }
        }
        Ok(())
    }
}
