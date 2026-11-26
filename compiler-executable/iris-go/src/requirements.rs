use std::cmp::Ordering;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Requirement {
    pub module: String,
    pub version: String,
    pub indirect: bool,
}

pub(crate) fn requirements(go_mod: &str) -> Vec<Requirement> {
    let mut requirements = vec![];
    let mut in_block = false;
    for line in go_mod.lines() {
        let line = line.trim();
        if in_block {
            if line.starts_with(')') {
                in_block = false;
            } else {
                requirements.extend(requirement(line));
            }
            continue;
        }
        let Some(rest) = require_directive_rest(line) else { continue };
        if rest.starts_with('(') {
            in_block = true;
        } else {
            requirements.extend(requirement(rest));
        }
    }
    requirements
}

pub(crate) fn with_requirements(go_mod: &str, added: &[Requirement]) -> Option<String> {
    let mut merged = requirements(go_mod);
    let mut changed = false;
    for requirement in added {
        let Some(existing) =
            merged.iter_mut().find(|existing| existing.module == requirement.module)
        else {
            merged.push(requirement.clone());
            changed = true;
            continue;
        };
        if is_newer(&requirement.version, &existing.version) {
            existing.version = requirement.version.clone();
            changed = true;
        }
        if existing.indirect && !requirement.indirect {
            existing.indirect = false;
            changed = true;
        }
    }
    if !changed {
        return None;
    }
    merged.sort_by(|first, second| first.module.cmp(&second.module));
    Some(replace_requirements(go_mod, &merged))
}

pub(crate) fn with_sums(go_sum: &str, added: &str) -> Option<String> {
    let mut lines: Vec<&str> = go_sum.lines().filter(|line| !line.trim().is_empty()).collect();
    let known = lines.len();
    for line in added.lines().filter(|line| !line.trim().is_empty()) {
        if !lines.contains(&line) {
            lines.push(line);
        }
    }
    if lines.len() == known {
        return None;
    }
    Some(lines.iter().map(|line| format!("{line}\n")).collect())
}

fn requirement(line: &str) -> Option<Requirement> {
    let (directive, comment) = match line.split_once("//") {
        Some((directive, comment)) => (directive, Some(comment)),
        None => (line, None),
    };
    let mut words = directive.split_whitespace();
    let (Some(module), Some(version), None) = (words.next(), words.next(), words.next()) else {
        return None;
    };
    let indirect = comment.is_some_and(|comment| {
        comment.split(';').next().is_some_and(|first| first.trim() == "indirect")
    });
    let module = module.trim_matches('"').to_string();
    Some(Requirement { module, version: version.to_string(), indirect })
}

fn require_directive_rest(line: &str) -> Option<&str> {
    let rest = line.strip_prefix("require")?;
    let separated = rest.starts_with([' ', '\t', '(']);
    separated.then(|| rest.trim_start())
}

fn is_newer(candidate: &str, current: &str) -> bool {
    let parse = |version: &str| semver::Version::parse(version.strip_prefix('v')?).ok();
    match (parse(candidate), parse(current)) {
        (Some(candidate), Some(current)) => candidate.cmp(&current) == Ordering::Greater,
        _ => false,
    }
}

fn replace_requirements(go_mod: &str, requirements: &[Requirement]) -> String {
    let mut kept = vec![];
    let mut position = None;
    let mut in_block = false;
    for line in go_mod.lines() {
        let trimmed = line.trim();
        if in_block {
            in_block = !trimmed.starts_with(')');
            continue;
        }
        if let Some(rest) = require_directive_rest(trimmed) {
            in_block = rest.starts_with('(');
            position.get_or_insert(kept.len());
            continue;
        }
        kept.push(line.to_string());
    }
    let (indirect, direct): (Vec<&Requirement>, Vec<&Requirement>) =
        requirements.iter().partition(|requirement| requirement.indirect);
    let blocks: Vec<String> = [direct, indirect]
        .iter()
        .filter(|group| !group.is_empty())
        .map(|group| require_directive(group))
        .collect();
    let blocks = blocks.join("\n\n");
    let mut lines = kept;
    match position {
        Some(position) => lines.insert(position, blocks),
        None => {
            if lines.last().is_some_and(|line| !line.trim().is_empty()) {
                lines.push(String::new());
            }
            lines.push(blocks);
        }
    }
    let mut text = lines.join("\n");
    text.push('\n');
    text
}

fn require_directive(requirements: &[&Requirement]) -> String {
    let line = |requirement: &Requirement| {
        let comment = if requirement.indirect { " // indirect" } else { "" };
        format!("{} {}{comment}", requirement.module, requirement.version)
    };
    match requirements {
        [requirement] => format!("require {}", line(requirement)),
        requirements => {
            let lines: Vec<String> = requirements
                .iter()
                .map(|requirement| format!("\t{}\n", line(requirement)))
                .collect();
            format!("require (\n{})", lines.concat())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn required(module: &str, version: &str, indirect: bool) -> Requirement {
        Requirement { module: module.to_string(), version: version.to_string(), indirect }
    }

    const ITERATION: &str = "module iris.local/ticker\n\ngo 1.27.0\n\nrequire \
                             github.com/i-am-the-slime/iris-go v0.6.0\n\nreplace \
                             github.com/i-am-the-slime/iris-go => /iris-go\n";

    #[test]
    fn reads_single_line_and_block_requirements() {
        let go_mod = "module example.com/library\n\ngo 1.27.0\n\nrequire (\n\tconnectrpc.com/connect \
                      v1.21.1\n\t\"example.com/quoted\" v0.1.0 // indirect\n)\n\nrequire \
                      google.golang.org/protobuf v1.36.11 // indirect\n";
        assert_eq!(
            requirements(go_mod),
            vec![
                required("connectrpc.com/connect", "v1.21.1", false),
                required("example.com/quoted", "v0.1.0", true),
                required("google.golang.org/protobuf", "v1.36.11", true),
            ]
        );
    }

    #[test]
    fn adds_requirements_beside_the_existing_ones_and_keeps_other_directives() {
        let added = [
            required("connectrpc.com/connect", "v1.21.1", false),
            required("google.golang.org/protobuf", "v1.36.11", true),
        ];
        let updated = with_requirements(ITERATION, &added).unwrap();
        assert_eq!(
            updated,
            "module iris.local/ticker\n\ngo 1.27.0\n\nrequire (\n\tconnectrpc.com/connect \
             v1.21.1\n\tgithub.com/i-am-the-slime/iris-go v0.6.0\n)\n\nrequire \
             google.golang.org/protobuf v1.36.11 // indirect\n\nreplace \
             github.com/i-am-the-slime/iris-go => /iris-go\n"
        );
        assert_eq!(requirements(&updated).len(), 3);
    }

    #[test]
    fn leaves_a_go_mod_that_already_requires_as_much_untouched() {
        let go_mod = "module m\n\nrequire (\n\ta.example/x v1.2.0\n\tb.example/y v0.3.0\n)\n";
        let added =
            [required("a.example/x", "v1.1.9", false), required("b.example/y", "v0.3.0", true)];
        assert_eq!(with_requirements(go_mod, &added), None);
    }

    #[test]
    fn keeps_the_newest_version_of_a_module_required_twice() {
        let go_mod = "module m\n\nrequire a.example/x v1.2.0\n";
        let newer = [required("a.example/x", "v1.10.0", false)];
        let updated = with_requirements(go_mod, &newer).unwrap();
        assert_eq!(requirements(&updated), vec![required("a.example/x", "v1.10.0", false)]);
        let pseudo = [required("a.example/x", "v1.2.1-0.20260101000000-abcdefabcdef", false)];
        let updated = with_requirements(&updated, &pseudo);
        assert_eq!(updated, None);
    }

    #[test]
    fn a_direct_requirement_makes_an_indirect_one_direct() {
        let go_mod = "module m\n\nrequire a.example/x v1.2.0 // indirect\n";
        let updated = with_requirements(go_mod, &[required("a.example/x", "v1.2.0", false)]);
        assert_eq!(updated.as_deref(), Some("module m\n\nrequire a.example/x v1.2.0\n"));
    }

    #[test]
    fn appends_requirements_to_a_go_mod_without_any() {
        let go_mod = "module example.com/application\n\ngo 1.27.0\n";
        let updated = with_requirements(go_mod, &[required("a.example/x", "v1.0.0", false)]);
        assert_eq!(
            updated.as_deref(),
            Some("module example.com/application\n\ngo 1.27.0\n\nrequire a.example/x v1.0.0\n")
        );
    }

    #[test]
    fn adds_only_the_checksums_go_sum_lacks() {
        let go_sum = "a.example/x v1.0.0 h1:one=\na.example/x v1.0.0/go.mod h1:two=\n";
        let added = "a.example/x v1.0.0/go.mod h1:two=\nb.example/y v0.1.0 h1:three=\n";
        assert_eq!(
            with_sums(go_sum, added).as_deref(),
            Some(
                "a.example/x v1.0.0 h1:one=\na.example/x v1.0.0/go.mod h1:two=\nb.example/y \
                 v0.1.0 h1:three=\n"
            )
        );
        assert_eq!(with_sums(go_sum, "a.example/x v1.0.0 h1:one=\n"), None);
    }
}
