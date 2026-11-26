use std::collections::BTreeSet;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::path::{Path, PathBuf};
use std::{fs, io};

use iris_spago::MANIFEST_FILE;

use super::workspace::Workspace;

const SPAGO_DIRECTORY: &str = ".spago";
const LOCK_FILE: &str = "spago.lock";
const STAMP_FILE: &str = "iris-fetch-stamp";
const INSTALLED_DIRECTORIES: [&str; 2] = ["p", "g"];

pub(crate) struct FetchStamp {
    path: PathBuf,
    content: String,
}

impl FetchStamp {
    pub(crate) fn of(workspace: &Workspace) -> io::Result<FetchStamp> {
        let spago = workspace.root.join(SPAGO_DIRECTORY);
        let mut lines = vec![format!("selected {}", workspace.selected.as_deref().unwrap_or(""))];
        for manifest in manifests(workspace) {
            lines.push(format!("manifest {} {}", manifest.display(), content_hash(&manifest)?));
        }
        lines.push(format!("lock {}", content_hash(&workspace.root.join(LOCK_FILE))?));
        for directory in INSTALLED_DIRECTORIES {
            let installed = installed(&spago.join(directory))?;
            lines.push(format!("installed {directory} {}", installed.join(" ")));
        }
        Ok(FetchStamp { path: spago.join(STAMP_FILE), content: lines.join("\n") })
    }

    pub(crate) fn is_current(&self) -> bool {
        fs::read_to_string(&self.path).is_ok_and(|recorded| recorded == self.content)
    }

    pub(crate) fn record(&self) -> io::Result<()> {
        if !self.path.parent().is_some_and(Path::is_dir) {
            return Ok(());
        }
        fs::write(&self.path, &self.content)
    }
}

pub(crate) struct ManifestContents {
    manifests: Vec<(PathBuf, Option<Vec<u8>>)>,
}

impl ManifestContents {
    pub(crate) fn of(workspace: &Workspace) -> io::Result<ManifestContents> {
        let manifests = manifests(workspace).into_iter().map(|manifest| {
            let content = read_if_present(&manifest)?;
            Ok((manifest, content))
        });
        let manifests = manifests.collect::<io::Result<_>>()?;
        Ok(ManifestContents { manifests })
    }

    pub(crate) fn restore(&self) -> io::Result<()> {
        for (manifest, recorded) in &self.manifests {
            let Some(recorded) = recorded else { continue };
            if read_if_present(manifest)?.as_ref() != Some(recorded) {
                fs::write(manifest, recorded)?;
            }
        }
        Ok(())
    }
}

fn read_if_present(path: &Path) -> io::Result<Option<Vec<u8>>> {
    match fs::read(path) {
        Ok(content) => Ok(Some(content)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(error),
    }
}

fn manifests(workspace: &Workspace) -> BTreeSet<PathBuf> {
    let packages = workspace.packages.values();
    let package_manifests = packages.map(|package| package.root.join(MANIFEST_FILE));
    let workspace_manifest = workspace.root.join(MANIFEST_FILE);
    package_manifests.chain(std::iter::once(workspace_manifest)).collect()
}

fn content_hash(path: &Path) -> io::Result<String> {
    let content = match fs::read(path) {
        Ok(content) => content,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok("absent".to_owned()),
        Err(error) => return Err(error),
    };
    let mut hasher = DefaultHasher::new();
    content.hash(&mut hasher);
    Ok(format!("{:016x}", hasher.finish()))
}

fn installed(directory: &Path) -> io::Result<Vec<String>> {
    let entries = match fs::read_dir(directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(vec![]),
        Err(error) => return Err(error),
    };
    let mut names = BTreeSet::new();
    for entry in entries {
        names.insert(entry?.file_name().to_string_lossy().into_owned());
    }
    Ok(names.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    use super::{FetchStamp, ManifestContents};
    use crate::workspace::Workspace;

    fn write_file(path: &Path, contents: &str) {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn write_package(root: &Path, name: &str, dependencies: &str) {
        let manifest = format!("package:\n  name: {name}\n  dependencies: [{dependencies}]\n");
        write_file(&root.join("spago.yaml"), &manifest);
        write_file(&root.join("src/Main.purs"), "module Main where\n");
    }

    fn stamp(workspace: &Workspace) -> FetchStamp {
        FetchStamp::of(workspace).unwrap()
    }

    #[test]
    fn a_fetch_stays_current_until_its_inputs_change() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        write_file(&root.join("spago.yaml"), "workspace: {}\n");
        write_package(&root.join("packages/application"), "application", "prelude");
        let workspace = Workspace::discover(root, None).unwrap();
        assert!(!stamp(&workspace).is_current());

        fs::create_dir_all(root.join(".spago/p/prelude-6.0.1")).unwrap();
        stamp(&workspace).record().unwrap();
        assert!(stamp(&workspace).is_current());

        fs::create_dir_all(root.join(".spago/p/effect-4.0.0")).unwrap();
        assert!(!stamp(&workspace).is_current());
        stamp(&workspace).record().unwrap();
        assert!(stamp(&workspace).is_current());

        write_package(&root.join("packages/application"), "application", "prelude, effect");
        let workspace = Workspace::discover(root, None).unwrap();
        assert!(!stamp(&workspace).is_current());
        stamp(&workspace).record().unwrap();
        assert!(stamp(&workspace).is_current());

        write_file(&root.join("spago.lock"), "workspace: {}\n");
        assert!(!stamp(&workspace).is_current());
    }

    #[test]
    fn a_fetch_for_one_package_is_not_current_for_another() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        write_file(&root.join("spago.yaml"), "workspace: {}\n");
        write_package(&root.join("packages/application"), "application", "library");
        write_package(&root.join("packages/library"), "library", "prelude");
        fs::create_dir_all(root.join(".spago/p/prelude-6.0.1")).unwrap();

        let application = Workspace::discover(root, Some("application")).unwrap();
        stamp(&application).record().unwrap();
        assert!(stamp(&application).is_current());

        let library = Workspace::discover(root, Some("library")).unwrap();
        assert!(!stamp(&library).is_current());
        let every_package = Workspace::discover(root, None).unwrap();
        assert!(!stamp(&every_package).is_current());
    }

    #[test]
    fn manifests_are_restored_after_spago_rewrote_their_bounds() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        write_file(&root.join("spago.yaml"), "workspace: {}\n");
        write_package(
            &root.join("packages/application"),
            "application",
            "\"prelude: >=6.0.0 <7.0.0\"",
        );
        let workspace = Workspace::discover(root, None).unwrap();
        let manifest = root.join("packages/application/spago.yaml");
        let written = fs::read_to_string(&manifest).unwrap();

        let manifests = ManifestContents::of(&workspace).unwrap();
        write_package(
            &root.join("packages/application"),
            "application",
            "\"prelude: >=6.0.3 <7.0.0\"",
        );
        manifests.restore().unwrap();

        assert_eq!(fs::read_to_string(&manifest).unwrap(), written);
    }

    #[test]
    fn nothing_is_recorded_before_spago_installed_anything() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        write_file(&root.join("spago.yaml"), "workspace: {}\n");
        write_package(&root.join("packages/application"), "application", "");
        let workspace = Workspace::discover(root, None).unwrap();

        stamp(&workspace).record().unwrap();
        assert!(!stamp(&workspace).is_current());
        assert!(!root.join(".spago").exists());
    }
}
