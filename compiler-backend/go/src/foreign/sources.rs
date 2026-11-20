//! Go files next to a PureScript source implement its module's foreign imports, as `.js` files
//! do for the JavaScript backend: `Foo.go`, and further `Foo.<part>.go` files, beside
//! `Foo.purs`.

use std::io;
use std::path::{Path, PathBuf};

use super::ForeignPackages;

/// The Go files next to a source file, in order of name. Go test files are left out.
pub fn foreign_files(source: &Path) -> io::Result<Vec<PathBuf>> {
    let (Some(directory), Some(stem)) =
        (source.parent(), source.file_stem().and_then(|stem| stem.to_str()))
    else {
        return Ok(vec![]);
    };
    let Ok(entries) = std::fs::read_dir(directory) else {
        return Ok(vec![]);
    };
    let mut names = vec![];
    for entry in entries {
        let entry = entry?;
        if entry.file_type()?.is_file()
            && let Ok(name) = entry.file_name().into_string()
        {
            names.push(name);
        }
    }
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    Ok(owned_files(stem, &names).into_iter().map(|name| directory.join(name)).collect())
}

/// A foreign file's Go source, with its package clause naming the package the generated code
/// imports. Authors may write any package name, such as `package ffi`.
pub fn foreign_source(module_name: &str, source: &str) -> String {
    let package = ForeignPackages::package_name(module_name);
    let mut renamed = false;
    let lines = source.split_inclusive('\n').map(|line| {
        if !renamed && line.starts_with("package ") {
            renamed = true;
            let ending = &line[line.trim_end().len()..];
            format!("package {package}{ending}")
        } else {
            line.to_string()
        }
    });
    lines.collect()
}

/// Of a directory's files, those that belong to the source `<stem>.purs`, in order of name:
/// `<stem>.go`, and `<stem>.<part>.go` unless `<stem>.<part>.purs`, a module of its own, owns it.
/// Go test files belong to no source.
fn owned_files<'n>(stem: &str, names: &[&'n str]) -> Vec<&'n str> {
    let mut owned: Vec<&str> = names
        .iter()
        .copied()
        .filter(|name| {
            let Some(part) = name.strip_prefix(stem).and_then(|rest| rest.strip_suffix(".go"))
            else {
                return false;
            };
            let is_test = name.ends_with("_test.go");
            let is_own_part = part.len() > 1
                && part.starts_with('.')
                && !names.contains(&format!("{stem}{part}.purs").as_str());
            (part.is_empty() || is_own_part) && !is_test
        })
        .collect();
    owned.sort();
    owned
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_source_owns_its_go_file_and_its_parts() {
        let names = [
            "Parser.purs",
            "Parser.go",
            "Parser.grammar.go",
            "Parser_test.go",
            "Parser.grammar_test.go",
            "ParserState.go",
            "Parser.js",
        ];
        assert_eq!(owned_files("Parser", &names), ["Parser.go", "Parser.grammar.go"]);
    }

    #[test]
    fn a_dotted_module_owns_its_own_go_file() {
        let names = ["OrderPricing.purs", "OrderPricing.Input.purs", "OrderPricing.Input.go"];
        assert!(owned_files("OrderPricing", &names).is_empty());
        assert_eq!(owned_files("OrderPricing.Input", &names), ["OrderPricing.Input.go"]);
    }

    #[test]
    fn the_package_clause_names_the_imported_package() {
        let source = "// Event's foreigns.\npackage ffi\r\n\nimport \"sort\"\n";
        assert_eq!(
            foreign_source("FRP.Event", source),
            "// Event's foreigns.\npackage FRP_Event_ffi\r\n\nimport \"sort\"\n"
        );
    }
}
