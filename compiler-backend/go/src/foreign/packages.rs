use std::collections::BTreeSet;

use files::FileId;
use rustc_hash::FxHashMap;

/// The Go packages that implement foreign imports. A module's Go files next to its source
/// (`Foo.go` beside `Foo.purs`) are copied into a package of the program's own Go module;
/// libraries that ship no Go files of their own take theirs from iris-go's `ffi` packages,
/// listed in [`LIBRARY_FOREIGNS`]. Either package is named after its module: `FRP_Event_ffi`.
#[derive(Debug, Clone, Default)]
pub struct ForeignPackages {
    /// The Go module the program's `go.mod` declares.
    pub module_path: String,
    /// The modules with Go files next to their source, copied into the program.
    pub modules: Vec<String>,
    /// The structs those Go files declare, by module: `(module, struct)`. A struct named like a
    /// record synonym of its module represents that record, as
    /// [`sources::foreign_structs`](super::sources::foreign_structs) says.
    pub structs: Vec<(String, String)>,
    /// What the Go files next to each module's source declare.
    pub sources: Vec<ForeignSource>,
    /// The paths of the project's source files, as messages that point into them show them.
    pub source_paths: Vec<(FileId, String)>,
    /// Where the Go and the PureScript are, to have `//line` directives attribute the Go to the
    /// PureScript it comes from; none leaves them out.
    pub line_directives: Option<LineDirectives>,
}

/// The paths `//line` directives are made from. A directive names its file relative to the
/// directory of the Go file it is in, which is where Go looks for it, so that the Go still points
/// at the PureScript when the project moves.
#[derive(Debug, Clone, Default)]
pub struct LineDirectives {
    /// The directory the Go files are written to.
    pub go_directory: String,
    /// The source files, absolute or relative to the same directory as `go_directory`.
    pub sources: Vec<(FileId, String)>,
    /// Which Go lines get a directive.
    pub coverage: LineCoverage,
}

/// Which Go lines `//line` directives name the source of.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum LineCoverage {
    /// The statements that call a function or can fail, which is what a stack trace, a debugger
    /// or a profile shows, and only where Go would not count to the line anyway.
    #[default]
    Sparse,
    /// Every statement and declaration, by the most specific PureScript position known, and the
    /// Go file itself for those from no PureScript: for tools that map each Go line to its
    /// source, such as a side-by-side viewer.
    Every,
}

/// The Go files next to a module's source and the names they declare at their top level, which
/// tell a foreign import its Go function is missing before Go does.
#[derive(Debug, Clone, Default)]
pub struct ForeignSource {
    pub module: String,
    /// The files, as the message about a missing name shows them.
    pub files: Vec<String>,
    pub values: Vec<String>,
    pub types: Vec<String>,
    pub forwarders: Vec<(String, super::Forward)>,
    pub uses_event_loop: bool,
    pub recovers: bool,
    pub opacity: super::Opacity,
}

/// The iris-go runtime's Go module.
const RUNTIME_MODULE: &str = "github.com/i-am-the-slime/iris-go";

/// The modules whose foreign imports iris-go implements in a package `ffi/<Module_ffi>`, for
/// libraries without Go files of their own. Go files next to a module's source take precedence.
const LIBRARY_FOREIGNS: &[&str] =
    &["Data.Int64.Internal", "Dhall.Parser", "FRP.Event", "Test.Assert", "Test.QuickCheck.Gen"];

impl ForeignPackages {
    pub fn provides(&self, module_name: &str) -> bool {
        self.copied(module_name) || LIBRARY_FOREIGNS.contains(&module_name)
    }

    /// Every module with a Go foreign package, copied or from iris-go.
    pub fn provided(&self) -> Vec<String> {
        let library = LIBRARY_FOREIGNS.iter().map(|module| module.to_string());
        self.modules.iter().cloned().chain(library).collect()
    }

    pub fn package_name(module_name: &str) -> String {
        format!("{}_ffi", module_name.replace('.', "_"))
    }

    pub fn import_path(&self, module_name: &str) -> String {
        if self.copied(module_name) {
            format!("{}/{}", self.module_path, ForeignPackages::package_name(module_name))
        } else {
            format!("{RUNTIME_MODULE}/ffi/{}", ForeignPackages::package_name(module_name))
        }
    }

    /// What the Go files next to the module's source declare, unless iris-go provides its package.
    pub fn source(&self, module_name: &str) -> Option<&ForeignSource> {
        self.sources.iter().find(|source| source.module == module_name)
    }

    pub fn imports_event_loop(&self, imports: &BTreeSet<String>) -> bool {
        self.sources
            .iter()
            .filter(|source| source.uses_event_loop)
            .any(|source| imports.contains(&self.import_path(&source.module)))
    }

    pub fn packages_that_never_recover(&self) -> BTreeSet<String> {
        self.sources
            .iter()
            .filter(|source| !source.recovers)
            .map(|source| ForeignPackages::package_name(&source.module))
            .collect()
    }

    /// The arguments each foreign function only calls on the goroutine that calls it, before it
    /// returns, by package and function.
    pub fn arguments_called_in_place(&self) -> FxHashMap<(String, String), Vec<usize>> {
        let mut called = FxHashMap::default();
        for source in &self.sources {
            let package = ForeignPackages::package_name(&source.module);
            for (function, positions) in &source.opacity.called_in_place {
                called.insert((package.clone(), function.clone()), positions.clone());
            }
        }
        called
    }

    fn copied(&self, module_name: &str) -> bool {
        self.modules.iter().any(|module| module == module_name)
    }
}
