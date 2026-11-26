//! Vector loops for pure numeric array code.
//!
//! `foldl (+) 0.0 xs`, `sum (zipWith (*) xs ys)` and `map (\x -> a * x + b) xs`
//! over `Array Number`, or `Array Int64` and `Array UInt64`
//! (purescript-int64's, Go's `[]int64` and `[]uint64`) do the same arithmetic on every element,
//! with no effects and no aliasing. Such a loop runs as a kernel: a function
//! with a vector loop, written with `simd/archsimd`'s NEON vectors in a file
//! that builds with `GOEXPERIMENT=simd` on arm64 and with the portable `simd`
//! package in one that builds with it on wasm, and a plain scalar twin of it
//! in a file that builds everywhere else:
//!
//! ```go
//! func foldLanes(xs []float64, initial float64) float64 {
//!     acc0 := simd.BroadcastFloat64s(math.Copysign(0, -1))
//!     ...
//!     for ; i < len(xs)-4*step+1; i += 4 * step {
//!         x0 := simd.LoadFloat64s(xs[i : i+step])
//!         acc0 = acc0.Add(x0)
//!         ...
//!     }
//!     ...
//! }
//! ```
//!
//! A kernel's callbacks are arithmetic (`+`, `-`, `*`, `/`, negation),
//! comparisons choosing between values (`if`, `min`, `max`, `clamp`),
//! constants and captured scalars of the element type, through `let` and calls
//! of small functions, which inline. A source is an array, a `map` of a source
//! or a `zipWith` of two. A fold reduces with `+`, `*`, `max` or `min` (`min`
//! only for integers): each vector lane folds its own share of the elements, so a
//! `Number` sum is reassociated and may differ from the scalar loop in its
//! last digits. Vectors of 64-bit integers cannot multiply, nor negate unsigned
//! ones, so code that does keeps its scalar loop. Anything else keeps the
//! scalar loop it had. `Array Int`, Go's `[]int`, keeps its scalar loop too: the vector
//! packages load lanes from `[]int64`, never from `[]int`.

use std::fmt::Write;

use rustc_hash::{FxHashMap, FxHashSet};

use super::fusion::Demand;
use super::iteration::Found;
use super::{Emitter, GoSourceFile, call, identifier_expression, unique};
use crate::error::GoResult;
use crate::foreign::{Boundary, Comparison, Foreign, GoFunction, GoPackage, Iteration, Operator};
use crate::monomorphic::traversal::visit;
use crate::monomorphic::{
    Expression, ExpressionKind, FunctionId, Literal, Local, LocalId, Program,
};
use crate::monotype::{Monotype, MonotypeId};
use crate::naming::GO_PREDECLARED;
use crate::primitives::{Int64Operation, Signedness};
use crate::syntax::{
    GoDeclaration, GoExpression, GoFile, GoImport, GoStatement, Reference, SourceLine,
};

const NEON_CONSTRAINT: &str = "goexperiment.simd && arm64";
const PORTABLE_CONSTRAINT: &str = "goexperiment.simd && wasm";
const SCALAR_CONSTRAINT: &str = "!(goexperiment.simd && (arm64 || wasm))";

/// What the kernel files beside a package file `<stem>.go` add to its stem.
pub const KERNEL_FILE_SUFFIXES: [&str; 3] = ["_neon.go", "_vector.go", "_scalar.go"];

/// Whether the Go source is a kernel file, by the build constraint it starts with.
pub fn is_kernel_file(source: &str) -> bool {
    let first_line = source.lines().next().unwrap_or_default();
    [NEON_CONSTRAINT, PORTABLE_CONSTRAINT, SCALAR_CONSTRAINT]
        .iter()
        .any(|constraint| first_line.strip_prefix("//go:build ") == Some(*constraint))
}

/// Arrays known to be shorter than this keep their scalar loops: their vector loops would
/// barely run, and cost three build variants of code.
const SHORT_ARRAY: usize = 32;

/// How far a callback may call into other functions.
const INLINE_DEPTH: usize = 6;

/// The kernels a program calls, each once however many loops share its code.
#[derive(Default)]
pub(super) struct Kernels {
    names: FxHashMap<String, String>,
    sources: Vec<KernelSource>,
    /// The locals bound to arrays known to be short. How often a loop runs is not known, nor
    /// how long an array read from the program's input is, so only a short length keeps a
    /// loop scalar.
    short_locals: FxHashSet<LocalId>,
}

impl Kernels {
    pub(super) fn new(program: &Program) -> Kernels {
        let mut short_locals = FxHashSet::default();
        for function in &program.functions {
            visit(&function.body, &mut |expression| {
                let ExpressionKind::Let { bindings, .. } = &expression.kind else { return };
                for binding in bindings {
                    if is_short(&binding.value, &short_locals) {
                        short_locals.insert(binding.local.id);
                    }
                }
            });
        }
        Kernels { short_locals, ..Kernels::default() }
    }
}

/// Whether the array is known to be shorter than `SHORT_ARRAY`: a literal, a range between
/// literals, or a `map`, `filter`, `zipWith`, slice or tail of such.
fn is_short(array: &Expression, short_locals: &FxHashSet<LocalId>) -> bool {
    match &array.kind {
        ExpressionKind::Array(elements) => elements.len() < SHORT_ARRAY,
        ExpressionKind::Local(local) => short_locals.contains(local),
        ExpressionKind::Coerce(inner) => is_short(inner, short_locals),
        ExpressionKind::Foreign {
            foreign: Foreign::Call { function: GoFunction { package: GoPackage::Array, name }, .. },
            arguments,
        } if matches!(*name, "Slice" | "Tail") => {
            let short_bounds = match arguments.as_slice() {
                [start, end, _] => match (&start.kind, &end.kind) {
                    (
                        ExpressionKind::Literal(Literal::Int(start)),
                        ExpressionKind::Literal(Literal::Int(end)),
                    ) => *start >= 0 && *end - *start < SHORT_ARRAY as i64,
                    _ => false,
                },
                _ => false,
            };
            short_bounds || arguments.last().is_some_and(|sliced| is_short(sliced, short_locals))
        }
        ExpressionKind::Foreign { foreign: Foreign::Range, arguments } => {
            let [first, last] = arguments.as_slice() else { return false };
            let (
                ExpressionKind::Literal(Literal::Int(first)),
                ExpressionKind::Literal(Literal::Int(last)),
            ) = (&first.kind, &last.kind)
            else {
                return false;
            };
            first.abs_diff(*last) < SHORT_ARRAY as u64
        }
        ExpressionKind::Foreign {
            foreign: Foreign::Call { boundary: Boundary { iteration: Some(iteration), .. }, .. },
            arguments,
        } => match iteration {
            Iteration::Map | Iteration::MapWithIndex | Iteration::Filter => {
                is_short(&arguments[1], short_locals)
            }
            Iteration::ZipWith => {
                is_short(&arguments[1], short_locals) || is_short(&arguments[2], short_locals)
            }
            _ => false,
        },
        _ => false,
    }
}

struct KernelSource {
    name: String,
    neon: String,
    portable: String,
    scalar: String,
    imports_math: bool,
    line: Option<SourceLine>,
}

impl<'p, 'q, Q> Emitter<'p, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// A call of the kernel that runs a fold, map or zipWith as a vector loop,
    /// when its element type and every callback it runs allow one.
    pub(super) fn vectorised(
        &mut self,
        iteration: Iteration,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Option<GoExpression>> {
        let Some(plan) = self.vector_plan(iteration, arguments, monotype) else {
            return Ok(None);
        };
        let Plan { kernel, inputs, captures, initial } = plan;
        let line = self.spans.enclosing().cloned();
        let name = self.kernel_name(&kernel, line);
        let mut values = vec![];
        for input in inputs {
            values.push(self.value(input, out)?);
        }
        for capture in captures {
            values.push(self.value(capture.expression, out)?);
        }
        if let Some(initial) = initial {
            values.push(self.value(initial, out)?);
        }
        Ok(Some(call(identifier_expression(&name), values)))
    }

    fn vector_plan<'e>(
        &self,
        iteration: Iteration,
        arguments: &'e [Expression],
        monotype: MonotypeId,
    ) -> Option<Plan<'e>>
    where
        'p: 'e,
    {
        let (arity, result_element) = match iteration {
            Iteration::FoldLeft => (2, self.element(monotype)?),
            Iteration::Map => {
                if self.recycled_maps.contains_key(&std::ptr::from_ref(&arguments[0])) {
                    return None;
                }
                (1, self.array_element(monotype)?)
            }
            Iteration::ZipWith => (2, self.array_element(monotype)?),
            _ => return None,
        };
        let callback = self.callback(&arguments[0], arity)?;
        // A fused loop stays scalar: building its array to fold it in a kernel pays only for
        // long arrays, and a fused range's length is rarely known.
        let (analysis, shape) =
            self.vector_shape(iteration, &callback, arguments, result_element)?;
        let initial = matches!(iteration, Iteration::FoldLeft).then(|| &arguments[1]);
        if let Some(initial) = initial
            && self.element(initial.monotype) != Some(result_element)
        {
            return None;
        }
        let Analysis { inputs, captures, bindings, element, .. } = analysis;
        let copies = matches!(shape, Shape::Map(Term::Lane(_)));
        if copies || inputs.iter().any(|input| is_short(input, &self.vector_kernels.short_locals)) {
            return None;
        }
        let parameters = parameter_names(&captures);
        let (bindings, shape) = inline_single_uses(bindings, shape);
        let kernel = Kernel { element, inputs: inputs.len(), parameters, bindings, shape };
        Some(Plan { kernel, inputs, captures, initial })
    }

    /// What the kernel computes of each element.
    fn vector_shape<'a, 'e>(
        &'a self,
        iteration: Iteration,
        callback: &Found<'e>,
        arguments: &'e [Expression],
        result_element: Element,
    ) -> Option<(Analysis<'a, 'e, Self>, Shape)>
    where
        'p: 'e,
    {
        let mut analysis = Analysis::new(self, result_element);
        let shape = match iteration {
            Iteration::FoldLeft => {
                let element = analysis.source(&arguments[2])?;
                let step = analysis.apply(callback, vec![Term::Accumulator, element], 0)?;
                let reduction = analysis.reduction(&step)?;
                Shape::Fold { step, reduction }
            }
            Iteration::Map => {
                let element = analysis.source(&arguments[1])?;
                Shape::Map(analysis.apply(callback, vec![element], 0)?)
            }
            _ => {
                let left = analysis.source(&arguments[1])?;
                let right = analysis.source(&arguments[2])?;
                Shape::Map(analysis.apply(callback, vec![left, right], 0)?)
            }
        };
        Some((analysis, shape))
    }

    fn kernel_name(&mut self, kernel: &Kernel, line: Option<SourceLine>) -> String {
        let neon = kernel.vector_source(Flavor::Neon);
        let portable = kernel.vector_source(Flavor::Portable);
        let scalar = kernel.scalar_source();
        let key = format!("{portable}\n{scalar}");
        if let Some(name) = self.vector_kernels.names.get(&key) {
            return name.clone();
        }
        let base = match kernel.shape {
            Shape::Fold { .. } => "foldLanes",
            Shape::Map(_) if kernel.inputs > 1 => "zipLanes",
            Shape::Map(_) => "mapLanes",
        };
        let name = unique(base.to_string(), &mut self.global_names);
        self.vector_kernels.names.insert(key, name.clone());
        let imports_math = portable.contains("math.");
        self.vector_kernels.sources.push(KernelSource {
            name: name.clone(),
            neon: neon.replace("{name}", &name),
            portable: portable.replace("{name}", &name),
            scalar: scalar.replace("{name}", &name),
            imports_math,
            line,
        });
        name
    }

    fn element(&self, monotype: MonotypeId) -> Option<Element> {
        match self.monotypes.get(monotype) {
            Monotype::Number => Some(Element::Number),
            Monotype::Int64 => Some(Element::Int64),
            Monotype::UInt64 => Some(Element::UInt64),
            _ => None,
        }
    }

    fn array_element(&self, monotype: MonotypeId) -> Option<Element> {
        match self.monotypes.get(monotype) {
            Monotype::Array(element) => self.element(*element),
            _ => None,
        }
    }
}

/// Adds the kernels each package calls next to it: a file with their NEON
/// loops for arm64, one with their portable `simd` loops for wasm, and one
/// with their scalar twins for every other build.
pub(super) fn attach_kernels(files: &mut Vec<GoSourceFile>, kernels: &Kernels) {
    if kernels.sources.is_empty() {
        return;
    }
    let by_name: FxHashMap<&str, &KernelSource> =
        kernels.sources.iter().map(|source| (source.name.as_str(), source)).collect();
    let mut added = vec![];
    for file in files.iter_mut() {
        let mut called: Vec<&KernelSource> = vec![];
        for declaration in &mut file.file.declarations {
            declaration.for_each_reference_mut(&mut |reference| {
                if let Reference::Value(GoExpression::Identifier(name)) = reference
                    && let Some(source) = by_name.get(name.as_str())
                    && !called.iter().any(|known| known.name == source.name)
                {
                    called.push(source);
                }
            });
        }
        if called.is_empty() {
            continue;
        }
        called.sort_by(|left, right| left.name.cmp(&right.name));
        let stem = file.path.strip_suffix(".go").unwrap_or(&file.path);
        let package = file.file.package.clone();
        let math = called.iter().any(|source| source.imports_math);
        let imports = |path: &str| {
            let mut imports = vec![GoImport { path: path.into(), alias: None }];
            if math {
                imports.insert(0, GoImport { path: "math".into(), alias: None });
            }
            imports
        };
        let written = |text: &str, source: &KernelSource| GoDeclaration::Written {
            name: source.name.clone(),
            source: text.to_string(),
            line: source.line.clone(),
        };
        added.push(GoSourceFile {
            path: format!("{stem}_neon.go"),
            file: GoFile {
                constraint: Some(NEON_CONSTRAINT),
                package: package.clone(),
                imports: imports("simd/archsimd"),
                declarations: called.iter().map(|source| written(&source.neon, source)).collect(),
            },
        });
        added.push(GoSourceFile {
            path: format!("{stem}_vector.go"),
            file: GoFile {
                constraint: Some(PORTABLE_CONSTRAINT),
                package: package.clone(),
                imports: imports("simd"),
                declarations: called
                    .iter()
                    .map(|source| written(&source.portable, source))
                    .collect(),
            },
        });
        added.push(GoSourceFile {
            path: format!("{stem}_scalar.go"),
            file: GoFile {
                constraint: Some(SCALAR_CONSTRAINT),
                package,
                imports: vec![],
                declarations: called.iter().map(|source| written(&source.scalar, source)).collect(),
            },
        });
    }
    files.extend(added);
}

struct Plan<'e> {
    kernel: Kernel,
    inputs: Vec<&'e Expression>,
    captures: Vec<Capture<'e>>,
    initial: Option<&'e Expression>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Element {
    Number,
    Int64,
    UInt64,
}

impl Element {
    fn scalar(self) -> &'static str {
        match self {
            Element::Number => "float64",
            Element::Int64 => "int64",
            Element::UInt64 => "uint64",
        }
    }

    /// Whether comparisons are exact and total: no NaN, no signed zeros.
    fn is_integer(self) -> bool {
        self != Element::Number
    }

    /// The 64-bit Long an Int64 operation on this element works on.
    fn signedness(self) -> Option<Signedness> {
        match self {
            Element::Int64 => Some(Signedness::Signed),
            Element::UInt64 => Some(Signedness::Unsigned),
            Element::Number => None,
        }
    }
}

/// Which vectors a kernel's loop is written with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Flavor {
    /// The `simd` package, whose vectors are as wide as the machine's, for wasm.
    Portable,
    /// `simd/archsimd`'s 128-bit NEON vectors, for arm64. Its methods inline
    /// straight to instructions, where the portable package leaves no-ops of
    /// its wrappers' inlining in the loop.
    Neon,
}

impl Flavor {
    fn package(self) -> &'static str {
        match self {
            Flavor::Portable => "simd",
            Flavor::Neon => "archsimd",
        }
    }

    fn vector(self, element: Element) -> &'static str {
        match (self, element) {
            (Flavor::Portable, Element::Number) => "Float64s",
            (Flavor::Portable, Element::Int64) => "Int64s",
            (Flavor::Portable, Element::UInt64) => "Uint64s",
            (Flavor::Neon, Element::Number) => "Float64x2",
            (Flavor::Neon, Element::Int64) => "Int64x2",
            (Flavor::Neon, Element::UInt64) => "Uint64x2",
        }
    }

    /// The most lanes a vector of the element has: 512 bits' worth for the
    /// portable package.
    fn widest(self, element: Element) -> usize {
        match (self, element) {
            (Flavor::Portable, Element::Number | Element::Int64 | Element::UInt64) => 8,
            (Flavor::Neon, Element::Number | Element::Int64 | Element::UInt64) => 2,
        }
    }

    /// Defines `step`, the lanes in a vector, from `length` when only the
    /// running machine knows it.
    fn step(self, element: Element, length: &str) -> String {
        match self {
            Flavor::Portable => format!("\tstep := {length}\n"),
            Flavor::Neon => format!("\tconst step = {}\n", self.widest(element)),
        }
    }
}

/// One element's computation, which the kernel spells once for vectors of
/// lanes and once for scalars.
#[derive(Debug, Clone, PartialEq)]
enum Term {
    /// The element of the kernel's input at this position.
    Lane(usize),
    Accumulator,
    /// A captured scalar, which the kernel takes as a parameter.
    Parameter(usize),
    /// A Go literal.
    Constant(String),
    /// A `let` binding, which the loop body computes once.
    Bound(usize),
    Negate(Box<Term>),
    Binary(Arithmetic, Box<Term>, Box<Term>),
    Select {
        condition: Condition,
        then: Box<Term>,
        otherwise: Box<Term>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Arithmetic {
    Add,
    Subtract,
    Multiply,
    Divide,
}

impl Arithmetic {
    fn method(self) -> &'static str {
        match self {
            Arithmetic::Add => "Add",
            Arithmetic::Subtract => "Sub",
            Arithmetic::Multiply => "Mul",
            Arithmetic::Divide => "Div",
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            Arithmetic::Add => "+",
            Arithmetic::Subtract => "-",
            Arithmetic::Multiply => "*",
            Arithmetic::Divide => "/",
        }
    }

    fn precedence(self) -> u8 {
        match self {
            Arithmetic::Add | Arithmetic::Subtract => 4,
            Arithmetic::Multiply | Arithmetic::Divide => 5,
        }
    }
}

/// A condition that is false where an operand is NaN; a negated one swaps
/// the branches it chooses between instead.
#[derive(Debug, Clone, PartialEq)]
enum Condition {
    Compare(Ordering, Box<Term>, Box<Term>),
    And(Box<Condition>, Box<Condition>),
    Or(Box<Condition>, Box<Condition>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ordering {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
}

impl Ordering {
    fn method(self) -> &'static str {
        match self {
            Ordering::Less => "Less",
            Ordering::LessEqual => "LessEqual",
            Ordering::Greater => "Greater",
            Ordering::GreaterEqual => "GreaterEqual",
            Ordering::Equal => "Equal",
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            Ordering::Less => "<",
            Ordering::LessEqual => "<=",
            Ordering::Greater => ">",
            Ordering::GreaterEqual => ">=",
            Ordering::Equal => "==",
        }
    }

    /// The ordering that holds exactly where this one does not, which only
    /// exists without NaN.
    fn complement(self) -> Option<Ordering> {
        match self {
            Ordering::Less => Some(Ordering::GreaterEqual),
            Ordering::LessEqual => Some(Ordering::Greater),
            Ordering::Greater => Some(Ordering::LessEqual),
            Ordering::GreaterEqual => Some(Ordering::Less),
            Ordering::Equal => None,
        }
    }
}

/// How a fold's lanes and their results combine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reduction {
    Add,
    Multiply,
    Max,
    Min,
}

enum Shape {
    Fold {
        step: Term,
        reduction: Reduction,
    },
    /// Produces an array, the term computing each of its elements.
    Map(Term),
}

struct Kernel {
    element: Element,
    inputs: usize,
    parameters: Vec<String>,
    bindings: Vec<Term>,
    shape: Shape,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CaptureKey {
    Local(LocalId),
    Function(FunctionId),
    Argument(*const Expression),
}

struct Capture<'e> {
    key: CaptureKey,
    expression: &'e Expression,
    name: Option<String>,
}

struct Analysis<'a, 'e, E> {
    emitter: &'a E,
    element: Element,
    inputs: Vec<&'e Expression>,
    captures: Vec<Capture<'e>>,
    bindings: Vec<Term>,
}

/// What the analysis needs from the emitter, apart from its lifetimes.
trait Lookup<'e> {
    fn element_of(&self, monotype: MonotypeId) -> Option<Element>;
    fn array_element_of(&self, monotype: MonotypeId) -> Option<Element>;
    fn found(&self, function: &'e Expression, arity: usize) -> Option<Found<'e>>;
    fn fusible(&self, array: &Expression) -> bool;
    fn parameters_of(&self, function: FunctionId) -> (&'e [Local], &'e Expression);
    fn is_lazy(&self, function: FunctionId) -> bool;
    fn local_name_of(&self, local: LocalId) -> Option<String>;
}

impl<'e, 'p: 'e, Q> Lookup<'e> for Emitter<'p, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    fn element_of(&self, monotype: MonotypeId) -> Option<Element> {
        self.element(monotype)
    }

    fn array_element_of(&self, monotype: MonotypeId) -> Option<Element> {
        self.array_element(monotype)
    }

    fn found(&self, function: &'e Expression, arity: usize) -> Option<Found<'e>> {
        self.callback(function, arity)
    }

    fn fusible(&self, array: &Expression) -> bool {
        self.is_fusible(array, Demand::FORWARD)
    }

    fn parameters_of(&self, function: FunctionId) -> (&'e [Local], &'e Expression) {
        let program: &'p crate::monomorphic::Program = self.program;
        let function = program.function(function);
        (&function.parameters, &function.body)
    }

    fn is_lazy(&self, function: FunctionId) -> bool {
        self.lazy_constants.contains(&function)
    }

    fn local_name_of(&self, local: LocalId) -> Option<String> {
        match self.locals.get(&local)? {
            GoExpression::Identifier(name) => Some(name.clone()),
            _ => None,
        }
    }
}

impl<'a, 'e, E: Lookup<'e>> Analysis<'a, 'e, E> {
    fn new(emitter: &'a E, element: Element) -> Self {
        Analysis { emitter, element, inputs: vec![], captures: vec![], bindings: vec![] }
    }

    /// The element of an array source: an input, or a `map` or `zipWith` of
    /// sources, which the kernel runs in its own loop. A source the scalar
    /// loops would fuse with their consumer keeps them.
    fn source(&mut self, array: &'e Expression) -> Option<Term> {
        if let ExpressionKind::Foreign {
            foreign: Foreign::Call { boundary: Boundary { iteration: Some(iteration), .. }, .. },
            arguments,
        } = &array.kind
        {
            return match iteration {
                Iteration::Map => {
                    let callback = self.emitter.found(&arguments[0], 1)?;
                    let element = self.source(&arguments[1])?;
                    self.apply(&callback, vec![element], 0)
                }
                Iteration::ZipWith => {
                    let callback = self.emitter.found(&arguments[0], 2)?;
                    let left = self.source(&arguments[1])?;
                    let right = self.source(&arguments[2])?;
                    self.apply(&callback, vec![left, right], 0)
                }
                _ => None,
            };
        }
        if self.emitter.fusible(array) {
            return None;
        }
        self.built(array)
    }

    /// The element of an array the kernel is passed as it is, built first if it is a loop.
    fn built(&mut self, array: &'e Expression) -> Option<Term> {
        if self.emitter.array_element_of(array.monotype)? != self.element {
            return None;
        }
        self.inputs.push(array);
        Some(Term::Lane(self.inputs.len() - 1))
    }

    /// The term a callback computes from the terms of its arguments.
    fn apply(&mut self, callback: &Found<'e>, arguments: Vec<Term>, depth: usize) -> Option<Term> {
        let arguments: Vec<Term> =
            arguments.into_iter().map(|argument| self.shared(argument)).collect();
        match callback {
            Found::Inline { parameters, body } => {
                let mut scope: FxHashMap<LocalId, Term> = FxHashMap::default();
                for (parameter, argument) in parameters.iter().zip(arguments) {
                    scope.insert(parameter.id, argument);
                }
                self.term(body, &scope, depth)
            }
            Found::Direct { callee, leading, .. } => {
                let mut all = vec![];
                for argument in *leading {
                    all.push(self.captured(CaptureKey::Argument(argument), argument, None)?);
                }
                all.extend(arguments);
                self.call(*callee, all, depth)
            }
        }
    }

    /// A function's body with its parameters bound to terms.
    fn call(&mut self, callee: FunctionId, arguments: Vec<Term>, depth: usize) -> Option<Term> {
        if depth >= INLINE_DEPTH || self.emitter.is_lazy(callee) {
            return None;
        }
        let (parameters, body) = self.emitter.parameters_of(callee);
        if parameters.len() != arguments.len() {
            return None;
        }
        let mut scope: FxHashMap<LocalId, Term> = FxHashMap::default();
        for (parameter, argument) in parameters.iter().zip(arguments) {
            scope.insert(parameter.id, self.shared(argument));
        }
        // A function's body sees only its parameters.
        self.term(body, &scope, depth + 1)
    }

    /// A term that more than one place may read, computed once.
    fn shared(&mut self, term: Term) -> Term {
        match term {
            Term::Lane(_)
            | Term::Accumulator
            | Term::Parameter(_)
            | Term::Constant(_)
            | Term::Bound(_) => term,
            term => {
                self.bindings.push(term);
                Term::Bound(self.bindings.len() - 1)
            }
        }
    }

    fn captured(
        &mut self,
        key: CaptureKey,
        expression: &'e Expression,
        name: Option<String>,
    ) -> Option<Term> {
        if self.emitter.element_of(expression.monotype)? != self.element {
            return None;
        }
        if let Some(position) = self.captures.iter().position(|capture| capture.key == key) {
            return Some(Term::Parameter(position));
        }
        self.captures.push(Capture { key, expression, name });
        Some(Term::Parameter(self.captures.len() - 1))
    }

    fn term(
        &mut self,
        expression: &'e Expression,
        scope: &FxHashMap<LocalId, Term>,
        depth: usize,
    ) -> Option<Term> {
        if self.emitter.element_of(expression.monotype)? != self.element {
            return None;
        }
        // What reads nothing the callback binds is the same for every
        // element, and the call site works it out once.
        if depth == 0
            && !matches!(expression.kind, ExpressionKind::Literal(_) | ExpressionKind::Local(_))
            && self.closed(expression, scope)
        {
            let key = CaptureKey::Argument(std::ptr::from_ref(expression));
            return self.captured(key, expression, None);
        }
        match &expression.kind {
            ExpressionKind::Literal(literal) => self.constant(literal, expression),
            ExpressionKind::Local(id) => match scope.get(id) {
                Some(term) => Some(term.clone()),
                // Only a callback written in place sees the locals around it.
                None if depth == 0 => {
                    let name = self.emitter.local_name_of(*id);
                    self.captured(CaptureKey::Local(*id), expression, name)
                }
                None => None,
            },
            ExpressionKind::Function(id) => {
                let (parameters, _) = self.emitter.parameters_of(*id);
                if !parameters.is_empty() {
                    return None;
                }
                self.captured(CaptureKey::Function(*id), expression, None)
            }
            ExpressionKind::Coerce(inner) => self.term(inner, scope, depth),
            ExpressionKind::Let { bindings, body } => {
                let mut scope = scope.clone();
                for binding in bindings {
                    let value = self.term(&binding.value, &scope, depth)?;
                    scope.insert(binding.local.id, self.shared(value));
                }
                self.term(body, &scope, depth)
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let (condition, negated) = self.condition(condition, scope, depth)?;
                let then = self.term(then, scope, depth)?;
                let otherwise = self.term(otherwise, scope, depth)?;
                if then == otherwise {
                    return Some(then);
                }
                // Where `a == b` chooses `a` and otherwise `b`, it always
                // chooses `b`'s value, as `Data.Ord.min` and `max` do on ties;
                // a Number could differ in the sign of a zero.
                let exact = |term: &Term| {
                    self.element.is_integer()
                        || matches!(term, Term::Constant(text) if text.parse::<f64>().is_ok_and(|number| number != 0.0))
                };
                if let (Condition::Compare(Ordering::Equal, left, right), false) =
                    (&condition, negated)
                    && (exact(left) || exact(right))
                    && ((**left == then && **right == otherwise)
                        || (**right == then && **left == otherwise))
                {
                    return Some(otherwise);
                }
                let (then, otherwise) = if negated { (otherwise, then) } else { (then, otherwise) };
                Some(Term::Select {
                    condition,
                    then: Box::new(then),
                    otherwise: Box::new(otherwise),
                })
            }
            ExpressionKind::Apply { function, arguments } => {
                let ExpressionKind::Function(callee) = function.kind else { return None };
                let mut terms = vec![];
                for argument in arguments {
                    terms.push(self.term(argument, scope, depth)?);
                }
                self.call(callee, terms, depth)
            }
            ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments } => {
                self.operator(*operator, arguments, scope, depth)
            }
            ExpressionKind::Foreign {
                foreign: Foreign::Int64 { operation, signedness },
                arguments,
            } if self.element.signedness() == Some(*signedness) => {
                self.int64_operation(*operation, arguments, scope, depth)
            }
            _ => None,
        }
    }

    /// The term of an Int64 or UInt64 operation of the element's Long.
    fn int64_operation(
        &mut self,
        operation: Int64Operation,
        arguments: &'e [Expression],
        scope: &FxHashMap<LocalId, Term>,
        depth: usize,
    ) -> Option<Term> {
        let unsigned = self.element == Element::UInt64;
        let arithmetic = match operation {
            Int64Operation::Constant(bits) if unsigned => {
                return Some(Term::Constant((bits as u64).to_string()));
            }
            Int64Operation::Constant(bits) => return Some(Term::Constant(bits.to_string())),
            Int64Operation::FromInt => match &arguments[0].kind {
                ExpressionKind::Literal(Literal::Int(value)) => {
                    let bits = i64::from(*value as i32);
                    let text = if unsigned { (bits as u64).to_string() } else { bits.to_string() };
                    return Some(Term::Constant(text));
                }
                _ => return None,
            },
            Int64Operation::Same => return self.term(&arguments[0], scope, depth),
            Int64Operation::Negate if !unsigned => {
                let operand = self.term(&arguments[0], scope, depth)?;
                return Some(Term::Negate(Box::new(operand)));
            }
            Int64Operation::Add => Arithmetic::Add,
            Int64Operation::Subtract => Arithmetic::Subtract,
            _ => return None,
        };
        let left = self.term(&arguments[0], scope, depth)?;
        let right = self.term(&arguments[1], scope, depth)?;
        Some(Term::Binary(arithmetic, Box::new(left), Box::new(right)))
    }

    /// Whether the expression is scalar arithmetic on literals and locals
    /// the callback does not bind, which cannot fail.
    fn closed(&self, expression: &Expression, scope: &FxHashMap<LocalId, Term>) -> bool {
        match &expression.kind {
            ExpressionKind::Literal(Literal::Int(_) | Literal::Number(_)) => true,
            ExpressionKind::Local(id) => !scope.contains_key(id),
            ExpressionKind::Coerce(inner) => self.closed(inner, scope),
            ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments } => {
                matches!(
                    operator,
                    Operator::IntAdd
                        | Operator::IntSubtract
                        | Operator::IntMultiply
                        | Operator::IntNegate
                        | Operator::NumberAdd
                        | Operator::NumberSubtract
                        | Operator::NumberMultiply
                        | Operator::NumberDivide
                        | Operator::NumberNegate
                        | Operator::IntToNumber
                ) && arguments.iter().all(|argument| self.closed(argument, scope))
            }
            ExpressionKind::Foreign { foreign: Foreign::Int64 { operation, .. }, arguments } => {
                matches!(
                    operation,
                    Int64Operation::Constant(_)
                        | Int64Operation::Add
                        | Int64Operation::Subtract
                        | Int64Operation::Multiply
                        | Int64Operation::Negate
                        | Int64Operation::Same
                ) && arguments.iter().all(|argument| self.closed(argument, scope))
            }
            _ => false,
        }
    }

    fn constant(&mut self, literal: &Literal, expression: &'e Expression) -> Option<Term> {
        match (literal, self.element) {
            (Literal::Number(value), Element::Number) => {
                let number = value.parse::<f64>().ok()?;
                // Go spells -0, NaN and the infinities as calls, which the
                // call site makes once.
                if !number.is_finite() || (number == 0.0 && number.is_sign_negative()) {
                    let key = CaptureKey::Argument(std::ptr::from_ref(expression));
                    return self.captured(key, expression, None);
                }
                let mut text = value.to_string();
                if !text.contains(['.', 'e', 'E']) {
                    text.push_str(".0");
                }
                Some(Term::Constant(text))
            }
            _ => None,
        }
    }

    fn operator(
        &mut self,
        operator: Operator,
        arguments: &'e [Expression],
        scope: &FxHashMap<LocalId, Term>,
        depth: usize,
    ) -> Option<Term> {
        let arithmetic =
            match (operator, self.element) {
                (Operator::NumberAdd, Element::Number) => Arithmetic::Add,
                (Operator::NumberSubtract, Element::Number) => Arithmetic::Subtract,
                (Operator::NumberMultiply, Element::Number) => Arithmetic::Multiply,
                (Operator::NumberDivide, Element::Number) => Arithmetic::Divide,
                (Operator::NumberNegate, Element::Number) => {
                    let operand = self.term(&arguments[0], scope, depth)?;
                    return Some(Term::Negate(Box::new(operand)));
                }
                _ => return None,
            };
        let left = self.term(&arguments[0], scope, depth)?;
        let right = self.term(&arguments[1], scope, depth)?;
        Some(Term::Binary(arithmetic, Box::new(left), Box::new(right)))
    }

    /// A condition, and whether it holds where the returned one does not.
    fn condition(
        &mut self,
        expression: &'e Expression,
        scope: &FxHashMap<LocalId, Term>,
        depth: usize,
    ) -> Option<(Condition, bool)> {
        if let ExpressionKind::Foreign {
            foreign: Foreign::Int64 { operation: Int64Operation::Compare(comparison), signedness },
            arguments,
        } = &expression.kind
            && self.element.signedness() == Some(*signedness)
        {
            let compare = Foreign::Operator(Operator::Compare(*comparison));
            return self.comparison(compare, arguments, scope, depth);
        }
        let ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments } =
            &expression.kind
        else {
            return None;
        };
        if let Operator::Compare(_) = operator {
            // An Int comparison's operands are Ints, never 64-bit Longs.
            if self.element.signedness().is_some() {
                return None;
            }
            return self.comparison(Foreign::Operator(*operator), arguments, scope, depth);
        }
        match operator {
            Operator::BooleanNot => {
                let (condition, negated) = self.condition(&arguments[0], scope, depth)?;
                Some((condition, !negated))
            }
            Operator::BooleanAnd | Operator::BooleanOr => {
                let (left, left_negated) = self.condition(&arguments[0], scope, depth)?;
                let (right, right_negated) = self.condition(&arguments[1], scope, depth)?;
                if left_negated != right_negated {
                    return None;
                }
                // By De Morgan, `not a && not b` is `not (a || b)`.
                let conjunction = (*operator == Operator::BooleanAnd) != left_negated;
                let (left, right) = (Box::new(left), Box::new(right));
                let condition = if conjunction {
                    Condition::And(left, right)
                } else {
                    Condition::Or(left, right)
                };
                Some((condition, left_negated))
            }
            _ => None,
        }
    }

    /// A comparison of two terms, and whether it holds where the condition does not.
    fn comparison(
        &mut self,
        compare: Foreign,
        arguments: &'e [Expression],
        scope: &FxHashMap<LocalId, Term>,
        depth: usize,
    ) -> Option<(Condition, bool)> {
        let Foreign::Operator(Operator::Compare(comparison)) = compare else { return None };
        let (ordering, negated) = match comparison {
            Comparison::Equal => (Ordering::Equal, false),
            Comparison::NotEqual => (Ordering::Equal, true),
            Comparison::LessThan => (Ordering::Less, false),
            Comparison::LessThanOrEqual => (Ordering::LessEqual, false),
            Comparison::GreaterThan => (Ordering::Greater, false),
            Comparison::GreaterThanOrEqual => (Ordering::GreaterEqual, false),
            Comparison::GreaterThanOrUnordered => (Ordering::LessEqual, true),
            Comparison::GreaterThanOrEqualOrUnordered => (Ordering::Less, true),
        };
        let left = self.term(&arguments[0], scope, depth)?;
        let right = self.term(&arguments[1], scope, depth)?;
        Some((Condition::Compare(ordering, Box::new(left), Box::new(right)), negated))
    }

    /// How a fold step combines its accumulator with the element's term, when
    /// it is a reduction whose lanes may fold separately: `+` and `*`, and
    /// `max` and `min` in the form that keeps the accumulator where a
    /// comparison with NaN is false, as `Data.Ord.max` does.
    fn reduction(&self, step: &Term) -> Option<Reduction> {
        let element_term = |term: &Term| !self.reads_accumulator(term);
        match step {
            Term::Binary(arithmetic @ (Arithmetic::Add | Arithmetic::Multiply), left, right) => {
                let accumulates = (**left == Term::Accumulator && element_term(right))
                    || (**right == Term::Accumulator && element_term(left));
                let reduction = if *arithmetic == Arithmetic::Add {
                    Reduction::Add
                } else {
                    Reduction::Multiply
                };
                accumulates.then_some(reduction)
            }
            Term::Select {
                condition: Condition::Compare(ordering, left, right),
                then,
                otherwise,
            } => {
                let (chosen, kept, ordering) =
                    match (**then == Term::Accumulator, **otherwise == Term::Accumulator) {
                        (false, true) => (then, otherwise, *ordering),
                        // Choosing the accumulator where the comparison holds
                        // chooses NaN elements, unless there are none.
                        (true, false) if self.element.is_integer() => {
                            (otherwise, then, ordering.complement()?)
                        }
                        _ => return None,
                    };
                if !element_term(chosen) || **kept != Term::Accumulator {
                    return None;
                }
                let accumulator_first = if **left == Term::Accumulator && right == chosen {
                    true
                } else if **right == Term::Accumulator && left == chosen {
                    false
                } else {
                    return None;
                };
                match (ordering, accumulator_first) {
                    (Ordering::Less | Ordering::LessEqual, true)
                    | (Ordering::Greater | Ordering::GreaterEqual, false) => Some(Reduction::Max),
                    (Ordering::Less | Ordering::LessEqual, false)
                    | (Ordering::Greater | Ordering::GreaterEqual, true) => Some(Reduction::Min),
                    (Ordering::Equal, _) => None,
                }
            }
            _ => None,
        }
    }

    fn reads_accumulator(&self, term: &Term) -> bool {
        let mut reads = false;
        visit_term(term, &self.bindings, &mut |term| reads |= *term == Term::Accumulator);
        reads
    }
}

/// Visits a term and everything it reads, through the bindings it reads.
fn visit_term(term: &Term, bindings: &[Term], visit: &mut impl FnMut(&Term)) {
    visit(term);
    match term {
        Term::Bound(index) => visit_term(&bindings[*index], bindings, visit),
        Term::Negate(operand) => visit_term(operand, bindings, visit),
        Term::Binary(_, left, right) => {
            visit_term(left, bindings, visit);
            visit_term(right, bindings, visit);
        }
        Term::Select { condition, then, otherwise } => {
            visit_condition(condition, bindings, visit);
            visit_term(then, bindings, visit);
            visit_term(otherwise, bindings, visit);
        }
        Term::Lane(_) | Term::Accumulator | Term::Parameter(_) | Term::Constant(_) => {}
    }
}

fn visit_condition(condition: &Condition, bindings: &[Term], visit: &mut impl FnMut(&Term)) {
    match condition {
        Condition::Compare(_, left, right) => {
            visit_term(left, bindings, visit);
            visit_term(right, bindings, visit);
        }
        Condition::And(left, right) | Condition::Or(left, right) => {
            visit_condition(left, bindings, visit);
            visit_condition(right, bindings, visit);
        }
    }
}

/// The kernel's names for the scalars it captures: their own where they make
/// a Go identifier no other name in the kernel uses.
fn parameter_names(captures: &[Capture<'_>]) -> Vec<String> {
    let mut names: Vec<String> = vec![];
    for (position, capture) in captures.iter().enumerate() {
        let name = match capture.name.clone() {
            Some(name) if is_free_name(&name) && !names.contains(&name) => name,
            _ => format!("k{position}"),
        };
        names.push(name);
    }
    names
}

/// `if a < b then a else b` and its kin, as the Go builtin it computes and the two it compares.
fn extremum(term: &Term) -> Option<(&'static str, &Term, &Term)> {
    let Term::Select { condition: Condition::Compare(ordering, left, right), then, otherwise } =
        term
    else {
        return None;
    };
    let chooses_compared =
        (left == then && right == otherwise) || (left == otherwise && right == then);
    if *ordering == Ordering::Equal || !chooses_compared {
        return None;
    }
    let less = matches!(ordering, Ordering::Less | Ordering::LessEqual);
    let extremum = if less == (right == then) { "max" } else { "min" };
    Some((extremum, left, right))
}

struct Clamp<'t> {
    value: &'t Term,
    lower: i128,
    upper: i128,
}

/// `if x < lower then lower else min x upper`, in any of its spellings, with constant bounds
/// in order: a clamp, which `min(max(x, lower), upper)` computes only when `lower <= upper`.
fn clamp(term: &Term) -> Option<Clamp<'_>> {
    let Term::Select { condition: Condition::Compare(ordering, left, right), then, otherwise } =
        term
    else {
        return None;
    };
    let (value, bound, bound_is_lower) = match ordering {
        Ordering::Equal => return None,
        Ordering::Less | Ordering::LessEqual if right == then => (left, right, true),
        Ordering::Greater | Ordering::GreaterEqual if right == then => (left, right, false),
        Ordering::Less | Ordering::LessEqual if left == then => (right, left, false),
        Ordering::Greater | Ordering::GreaterEqual if left == then => (right, left, true),
        _ => return None,
    };
    let (inner, inner_left, inner_right) = extremum(otherwise)?;
    let inner_bound = match () {
        _ if inner_left == &**value => inner_right,
        _ if inner_right == &**value => inner_left,
        _ => return None,
    };
    if (inner == "min") != bound_is_lower {
        return None;
    }
    let bound = constant_value(bound)?;
    let inner_bound = constant_value(inner_bound)?;
    let (lower, upper) = if bound_is_lower { (bound, inner_bound) } else { (inner_bound, bound) };
    (lower <= upper).then_some(Clamp { value, lower, upper })
}

fn constant_value(term: &Term) -> Option<i128> {
    let Term::Constant(text) = term else { return None };
    text.parse().ok()
}

fn is_literal(term: &Term) -> bool {
    match term {
        Term::Constant(_) => true,
        Term::Negate(operand) => is_literal(operand),
        Term::Binary(_, left, right) => is_literal(left) && is_literal(right),
        _ => false,
    }
}

fn is_free_name(name: &str) -> bool {
    const KERNEL_NAMES: &[&str] = &[
        "xs",
        "ys",
        "zs",
        "ws",
        "x",
        "y",
        "z",
        "w",
        "i",
        "n",
        "step",
        "out",
        "accumulator",
        "initial",
        "lanes",
        "lane",
        "simd",
        "math",
    ];
    let numbered = |prefix: &str| {
        name.strip_prefix(prefix).is_some_and(|rest| {
            !rest.is_empty() && rest.bytes().all(|byte| byte.is_ascii_digit() || byte == b'_')
        })
    };
    name.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        && name.bytes().next().is_some_and(|byte| byte.is_ascii_alphabetic())
        && !GO_PREDECLARED.contains(&name)
        && !KERNEL_NAMES.contains(&name)
        && !name.ends_with("Lanes")
        && !["x", "y", "z", "w", "t", "s", "c", "k", "acc", "input", "lane"]
            .into_iter()
            .any(numbered)
}

/// How a spelling of the kernel's terms names what they read.
struct Spelling<'k> {
    kernel: &'k Kernel,
    /// The unrolled copy of the loop body being spelled, if any.
    copy: Option<usize>,
    accumulator: String,
    /// Statements a scalar spelling needs before its expression.
    statements: Vec<String>,
    selections: usize,
    /// The vectors a vector spelling is written with.
    flavor: Option<Flavor>,
}

const LANE_NAMES: &[&str] = &["x", "y", "z", "w"];
const INPUT_NAMES: &[&str] = &["xs", "ys", "zs", "ws"];

fn input_name(position: usize) -> String {
    INPUT_NAMES.get(position).map_or_else(|| format!("input{position}"), |name| name.to_string())
}

impl Kernel {
    fn root(&self) -> &Term {
        match &self.shape {
            Shape::Fold { step, .. } => step,
            Shape::Map(term) => term,
        }
    }

    /// The bindings and lanes the loop body reads, in the order they bind.
    fn reads(&self) -> (Vec<usize>, Vec<usize>) {
        let mut bound = vec![];
        let mut lanes = vec![];
        visit_term(self.root(), &self.bindings, &mut |term| match term {
            Term::Bound(index) if !bound.contains(index) => bound.push(*index),
            Term::Lane(index) if !lanes.contains(index) => lanes.push(*index),
            _ => {}
        });
        bound.sort_unstable();
        lanes.sort_unstable();
        (bound, lanes)
    }

    fn constants(&self) -> Vec<String> {
        let mut constants = vec![];
        visit_term(self.root(), &self.bindings, &mut |term| {
            if let Term::Constant(text) = term
                && !constants.contains(text)
            {
                constants.push(text.clone());
            }
        });
        constants
    }

    fn signature(&self) -> String {
        let scalar = self.element.scalar();
        let mut parameters: Vec<String> = (0..self.inputs)
            .map(|position| format!("{} []{scalar}", input_name(position)))
            .collect();
        parameters.extend(self.parameters.iter().map(|name| format!("{name} {scalar}")));
        let result = match self.shape {
            Shape::Fold { .. } => {
                parameters.push(format!("initial {scalar}"));
                scalar.to_string()
            }
            Shape::Map(_) => format!("[]{scalar}"),
        };
        format!("func {{name}}({}) {result} {{\n", parameters.join(", "))
    }

    /// Makes every input as long as the shortest, so that one bound covers
    /// them all, and is the number of elements.
    fn lengths(&self, out: &mut String) -> String {
        if self.inputs == 1 {
            return "len(xs)".into();
        }
        let names: Vec<String> = (0..self.inputs).map(input_name).collect();
        let lengths: Vec<String> = names.iter().map(|name| format!("len({name})")).collect();
        let _ = writeln!(out, "\tn := min({})", lengths.join(", "));
        let resliced: Vec<String> = names.iter().map(|name| format!("{name}[:n]")).collect();
        let _ = writeln!(out, "\t{} = {}", names.join(", "), resliced.join(", "));
        "len(xs)".into()
    }

    fn vector_source(&self, flavor: Flavor) -> String {
        let scalar = self.element.scalar();
        let vector = flavor.vector(self.element);
        let package = flavor.package();
        let mut out = String::new();
        out.push_str(&self.signature());
        let length = self.lengths(&mut out);
        for (position, name) in self.parameters.iter().enumerate() {
            if self.reads_in_loop(&Term::Parameter(position)) {
                let _ = writeln!(out, "\t{name}Lanes := {package}.Broadcast{vector}({name})");
            }
        }
        for (position, constant) in self.constants().iter().enumerate() {
            let _ = writeln!(out, "\tc{position} := {package}.Broadcast{vector}({constant})");
        }
        match &self.shape {
            Shape::Fold { step, reduction } => {
                let identity = match (reduction, self.element) {
                    (Reduction::Add, Element::Number) => "math.Copysign(0, -1)",
                    (Reduction::Add, _) => "0",
                    (Reduction::Multiply, _) => "1",
                    (Reduction::Max | Reduction::Min, _) => "initial",
                };
                let _ = writeln!(out, "\tacc0 := {package}.Broadcast{vector}({identity})");
                out.push_str("\tacc1, acc2, acc3 := acc0, acc0, acc0\n");
                out.push_str(&flavor.step(self.element, "acc0.Len()"));
                out.push_str("\ti := 0\n");
                let _ = writeln!(out, "\tfor ; i < {length}-4*step+1; i += 4 * step {{");
                for copy in 0..4 {
                    self.vector_body(flavor, Some(copy), &mut out, |kernel, spelling| {
                        let _ = kernel;
                        let value = spelling.vector(step);
                        format!("\t\tacc{copy} = {value}\n")
                    });
                }
                out.push_str("\t}\n");
                let pair =
                    |left: &str, right: &str| self.combine_vectors(*reduction, left, right);
                let _ = writeln!(
                    out,
                    "\tacc0 = {}",
                    pair(&pair("acc0", "acc1"), &pair("acc2", "acc3"))
                );
                let _ = writeln!(out, "\tvar lanes [{}]{scalar}", flavor.widest(self.element));
                out.push_str("\tacc0.Store(lanes[:])\n");
                out.push_str("\taccumulator := initial\n");
                out.push_str("\tfor _, lane := range lanes[:step] {\n");
                let _ = writeln!(out, "\t\t{}", self.combine_scalars(*reduction));
                out.push_str("\t}\n");
                let _ = writeln!(out, "\tfor ; i < {length}; i++ {{");
                out.push_str(&self.scalar_step(step, "\t\t", false));
                out.push_str("\t}\n");
                out.push_str("\treturn accumulator\n");
            }
            Shape::Map(term) => {
                let _ = writeln!(out, "\tout := make([]{scalar}, {length})");
                out.push_str(&flavor.step(self.element, &format!("{package}.{vector}{{}}.Len()")));
                out.push_str("\ti := 0\n");
                let _ = writeln!(out, "\tfor ; i < {length}-step+1; i += step {{");
                self.vector_body(flavor, None, &mut out, |_, spelling| {
                    format!("\t\t{}.Store(out[i : i+step])\n", spelling.vector(term))
                });
                out.push_str("\t}\n");
                let _ = writeln!(out, "\tif i < {length} {{");
                self.partial_body(flavor, &mut out, term);
                out.push_str("\t}\n");
                out.push_str("\treturn out\n");
            }
        }
        out.push_str("}\n");
        out
    }

    fn reads_in_loop(&self, wanted: &Term) -> bool {
        let mut reads = false;
        visit_term(self.root(), &self.bindings, &mut |term| reads |= term == wanted);
        reads
    }

    /// One copy of the vector loop body: its lanes, its bindings, then what
    /// `finish` makes of the result.
    fn vector_body(
        &self,
        flavor: Flavor,
        copy: Option<usize>,
        out: &mut String,
        finish: impl FnOnce(&Kernel, &mut Spelling<'_>) -> String,
    ) {
        let vector = flavor.vector(self.element);
        let package = flavor.package();
        let (bound, lanes) = self.reads();
        let mut spelling =
            self.spelling(copy, copy.map_or("acc".into(), |copy| format!("acc{copy}")));
        spelling.flavor = Some(flavor);
        for lane in lanes {
            let (low, high) = match copy {
                None | Some(0) => ("i".to_string(), "i+step".to_string()),
                Some(1) => ("i+step".to_string(), "i+2*step".to_string()),
                Some(copy) => (format!("i+{copy}*step"), format!("i+{}*step", copy + 1)),
            };
            let _ = writeln!(
                out,
                "\t\t{} := {package}.Load{vector}({}[{low} : {high}])",
                spelling.lane(lane),
                input_name(lane)
            );
        }
        for index in bound {
            let value = spelling.vector(&self.bindings[index]);
            let _ = writeln!(out, "\t\t{} := {value}", spelling.bound(index));
        }
        out.push_str(&finish(self, &mut spelling));
    }

    /// The last elements of a map, fewer than a vector holds, loaded into
    /// part of one and stored from it.
    fn partial_body(&self, flavor: Flavor, out: &mut String, term: &Term) {
        let vector = flavor.vector(self.element);
        let package = flavor.package();
        let (bound, lanes) = self.reads();
        let mut spelling = self.spelling(None, "acc".into());
        spelling.flavor = Some(flavor);
        for lane in lanes {
            let _ = writeln!(
                out,
                "\t\t{}, _ := {package}.Load{vector}Part({}[i:])",
                spelling.lane(lane),
                input_name(lane)
            );
        }
        for index in bound {
            let value = spelling.vector(&self.bindings[index]);
            let _ = writeln!(out, "\t\t{} := {value}", spelling.bound(index));
        }
        let _ = writeln!(out, "\t\t{}.StorePart(out[i:])", spelling.vector(term));
    }

    fn combine_vectors(
        &self,
        reduction: Reduction,
        left: &str,
        right: &str,
    ) -> String {
        match reduction {
            Reduction::Add => format!("{left}.Add({right})"),
            Reduction::Multiply => format!("{left}.Mul({right})"),
            Reduction::Max => format!("{right}.IfElse({left}.Less({right}), {left})"),
            Reduction::Min => format!("{right}.IfElse({right}.Less({left}), {left})"),
        }
    }

    fn combine_scalars(&self, reduction: Reduction) -> &'static str {
        match reduction {
            Reduction::Add => "accumulator = accumulator + lane",
            Reduction::Multiply => "accumulator = accumulator * lane",
            Reduction::Max => "if accumulator < lane {\n\t\t\taccumulator = lane\n\t\t}",
            Reduction::Min => "if lane < accumulator {\n\t\t\taccumulator = lane\n\t\t}",
        }
    }

    /// The scalar loop body of a fold: the element, then the step.
    fn scalar_step(&self, step: &Term, indentation: &str, ranged: bool) -> String {
        let mut out = String::new();
        let mut spelling = self.spelling(None, "accumulator".into());
        self.scalar_prelude(&mut spelling, indentation, ranged, &mut out);
        let value = spelling.scalar(step, 0);
        for statement in std::mem::take(&mut spelling.statements) {
            let _ = writeln!(
                out,
                "{indentation}{}",
                statement.replace('\n', &format!("\n{indentation}"))
            );
        }
        let _ = writeln!(out, "{indentation}accumulator = {value}");
        out
    }

    /// The lanes and bindings of a scalar loop body; a `ranged` loop has its
    /// only input's element already.
    fn scalar_prelude(
        &self,
        spelling: &mut Spelling<'_>,
        indentation: &str,
        ranged: bool,
        out: &mut String,
    ) {
        let (bound, lanes) = self.reads();
        for lane in lanes.into_iter().filter(|_| !ranged) {
            let _ =
                writeln!(out, "{indentation}{} := {}[i]", spelling.lane(lane), input_name(lane));
        }
        for index in bound {
            let value = spelling.declared(&self.bindings[index]);
            for statement in std::mem::take(&mut spelling.statements) {
                let _ = writeln!(
                    out,
                    "{indentation}{}",
                    statement.replace('\n', &format!("\n{indentation}"))
                );
            }
            let _ = writeln!(out, "{indentation}{} := {value}", spelling.bound(index));
        }
    }

    /// The loop as the program would run it without vectors, in the order it
    /// is written.
    fn scalar_source(&self) -> String {
        let scalar = self.element.scalar();
        let mut out = String::new();
        out.push_str(&self.signature());
        let length = self.lengths(&mut out);
        match &self.shape {
            Shape::Fold { step, .. } => {
                out.push_str("\taccumulator := initial\n");
                let ranged = self.inputs == 1;
                if !ranged {
                    let _ = writeln!(out, "\tfor i := range {length} {{");
                } else if self.reads().1.is_empty() {
                    out.push_str("\tfor range xs {\n");
                } else {
                    let _ = writeln!(out, "\tfor _, {} := range xs {{", LANE_NAMES[0]);
                }
                out.push_str(&self.scalar_step(step, "\t\t", ranged));
                out.push_str("\t}\n");
                out.push_str("\treturn accumulator\n");
            }
            Shape::Map(term) => {
                let _ = writeln!(out, "\tout := make([]{scalar}, {length})");
                let ranged = self.inputs == 1 && !self.reads().1.is_empty();
                if ranged {
                    let _ = writeln!(out, "\tfor i, {} := range xs {{", LANE_NAMES[0]);
                } else {
                    out.push_str("\tfor i := range out {\n");
                }
                let mut spelling = self.spelling(None, "accumulator".into());
                self.scalar_prelude(&mut spelling, "\t\t", ranged, &mut out);
                let value = spelling.scalar(term, 0);
                for statement in std::mem::take(&mut spelling.statements) {
                    let _ = writeln!(out, "\t\t{}", statement.replace('\n', "\n\t\t"));
                }
                let _ = writeln!(out, "\t\tout[i] = {value}");
                out.push_str("\t}\n");
                out.push_str("\treturn out\n");
            }
        }
        out.push_str("}\n");
        out
    }

    fn spelling(&self, copy: Option<usize>, accumulator: String) -> Spelling<'_> {
        Spelling {
            kernel: self,
            copy,
            accumulator,
            statements: vec![],
            selections: 0,
            flavor: None,
        }
    }
}

impl Spelling<'_> {
    fn lane(&self, position: usize) -> String {
        let base = LANE_NAMES
            .get(position)
            .map_or_else(|| format!("lane{position}_"), |name| name.to_string());
        match self.copy {
            Some(copy) => format!("{base}{copy}"),
            None => base,
        }
    }

    fn bound(&self, index: usize) -> String {
        match self.copy {
            Some(copy) => format!("t{index}_{copy}"),
            None => format!("t{index}"),
        }
    }

    fn constant(&self, text: &str) -> String {
        let position = self.kernel.constants().iter().position(|known| known == text).unwrap_or(0);
        format!("c{position}")
    }

    fn vector(&mut self, term: &Term) -> String {
        match term {
            Term::Lane(position) => self.lane(*position),
            Term::Accumulator => self.accumulator.clone(),
            Term::Parameter(position) => format!("{}Lanes", self.kernel.parameters[*position]),
            Term::Constant(text) => self.constant(text),
            Term::Bound(index) => self.bound(*index),
            Term::Negate(operand) => format!("{}.Neg()", self.vector(operand)),
            // `a * b + c` fuses, as the scalar loop may.
            Term::Binary(Arithmetic::Add, left, right)
                if self.kernel.element == Element::Number
                    && matches!(**left, Term::Binary(Arithmetic::Multiply, ..)) =>
            {
                let Term::Binary(_, a, b) = &**left else { unreachable!() };
                format!("{}.MulAdd({}, {})", self.vector(a), self.vector(b), self.vector(right))
            }
            Term::Binary(Arithmetic::Add, left, right)
                if self.kernel.element == Element::Number
                    && matches!(**right, Term::Binary(Arithmetic::Multiply, ..)) =>
            {
                let Term::Binary(_, a, b) = &**right else { unreachable!() };
                format!("{}.MulAdd({}, {})", self.vector(a), self.vector(b), self.vector(left))
            }
            Term::Binary(arithmetic, left, right) => {
                format!("{}.{}({})", self.vector(left), arithmetic.method(), self.vector(right))
            }
            Term::Select { condition, then, otherwise } => {
                let mask = self.mask(condition);
                format!("{}.IfElse({mask}, {})", self.vector(then), self.vector(otherwise))
            }
        }
    }

    fn mask(&mut self, condition: &Condition) -> String {
        match condition {
            Condition::Compare(ordering, left, right) => {
                format!("{}.{}({})", self.vector(left), ordering.method(), self.vector(right))
            }
            Condition::And(left, right) => format!("{}.And({})", self.mask(left), self.mask(right)),
            Condition::Or(left, right) => format!("{}.Or({})", self.mask(left), self.mask(right)),
        }
    }

    /// A Go expression for the term, parenthesised where an operator binding
    /// at `context` would otherwise regroup it.
    fn scalar(&mut self, term: &Term, context: u8) -> String {
        match term {
            Term::Lane(position) => self.lane(*position),
            Term::Accumulator => self.accumulator.clone(),
            Term::Parameter(position) => self.kernel.parameters[*position].clone(),
            Term::Constant(text) if text.starts_with('-') && context > 0 => format!("({text})"),
            Term::Constant(text) => text.clone(),
            Term::Bound(index) => self.bound(*index),
            Term::Negate(operand) => format!("-{}", self.scalar(operand, 6)),
            Term::Binary(arithmetic, left, right) => {
                let precedence = arithmetic.precedence();
                let left = self.scalar(left, precedence);
                // Right operands of equal precedence keep their grouping:
                // floating-point arithmetic does not reassociate.
                let right = self.scalar(right, precedence + 1);
                let text = format!("{left} {} {right}", arithmetic.symbol());
                if precedence < context { format!("({text})") } else { text }
            }
            // Go's `min` and `max` treat NaN and signed zeros unlike a Number comparison.
            Term::Select { .. }
                if self.kernel.element != Element::Number
                    && let Some(chosen) = self.scalar_extremum(term) =>
            {
                chosen
            }
            Term::Select { condition, then, otherwise } => {
                let otherwise = self.declared(otherwise);
                let then = self.scalar(then, 0);
                let condition = self.condition(condition, 0);
                let name = format!("s{}", self.selections);
                self.selections += 1;
                self.statements.push(format!(
                    "{name} := {otherwise}\nif {condition} {{\n\t{name} = {then}\n}}"
                ));
                name
            }
        }
    }

    /// A choice between two values by comparing them as Go's `min` or `max`, and a clamp
    /// between two constants as both.
    fn scalar_extremum(&mut self, term: &Term) -> Option<String> {
        if let Some((extremum, left, right)) = extremum(term) {
            return Some(format!(
                "{extremum}({}, {})",
                self.scalar(left, 0),
                self.scalar(right, 0)
            ));
        }
        let Clamp { value, lower, upper } = clamp(term)?;
        let value = self.scalar(value, 0);
        Some(format!("min(max({value}, {lower}), {upper})"))
    }

    fn declared(&mut self, term: &Term) -> String {
        let value = self.scalar(term, 0);
        if self.kernel.element == Element::Number || !is_literal(term) {
            return value;
        }
        format!("{}({value})", self.kernel.element.scalar())
    }

    fn condition(&mut self, condition: &Condition, context: u8) -> String {
        match condition {
            Condition::Compare(ordering, left, right) => {
                let left = self.scalar(left, 4);
                let right = self.scalar(right, 4);
                format!("{left} {} {right}", ordering.symbol())
            }
            Condition::And(left, right) => {
                let text = format!("{} && {}", self.condition(left, 2), self.condition(right, 3));
                if context > 2 { format!("({text})") } else { text }
            }
            Condition::Or(left, right) => {
                let text = format!("{} || {}", self.condition(left, 1), self.condition(right, 2));
                if context > 1 { format!("({text})") } else { text }
            }
        }
    }
}

/// Substitutes every binding read only once into the term that reads it.
fn inline_single_uses(bindings: Vec<Term>, shape: Shape) -> (Vec<Term>, Shape) {
    let root = match &shape {
        Shape::Fold { step, .. } => step,
        Shape::Map(term) => term,
    };
    let mut uses = vec![0usize; bindings.len()];
    let mut seen = vec![false; bindings.len()];
    count_uses(root, &bindings, &mut uses, &mut seen);
    let resolve = |term: &Term| substitute(term, &bindings, &uses);
    let shape = match &shape {
        Shape::Fold { step, reduction } => {
            Shape::Fold { step: resolve(step), reduction: *reduction }
        }
        Shape::Map(term) => Shape::Map(resolve(term)),
    };
    let resolved = bindings.iter().map(resolve).collect();
    (resolved, shape)
}

fn count_uses(term: &Term, bindings: &[Term], uses: &mut [usize], seen: &mut [bool]) {
    match term {
        Term::Bound(index) => {
            uses[*index] += 1;
            if !seen[*index] {
                seen[*index] = true;
                count_uses(&bindings[*index], bindings, uses, seen);
            }
        }
        Term::Negate(operand) => count_uses(operand, bindings, uses, seen),
        Term::Binary(_, left, right) => {
            count_uses(left, bindings, uses, seen);
            count_uses(right, bindings, uses, seen);
        }
        Term::Select { condition, then, otherwise } => {
            count_condition_uses(condition, bindings, uses, seen);
            count_uses(then, bindings, uses, seen);
            count_uses(otherwise, bindings, uses, seen);
        }
        Term::Lane(_) | Term::Accumulator | Term::Parameter(_) | Term::Constant(_) => {}
    }
}

fn count_condition_uses(
    condition: &Condition,
    bindings: &[Term],
    uses: &mut [usize],
    seen: &mut [bool],
) {
    match condition {
        Condition::Compare(_, left, right) => {
            count_uses(left, bindings, uses, seen);
            count_uses(right, bindings, uses, seen);
        }
        Condition::And(left, right) | Condition::Or(left, right) => {
            count_condition_uses(left, bindings, uses, seen);
            count_condition_uses(right, bindings, uses, seen);
        }
    }
}

fn substitute(term: &Term, bindings: &[Term], uses: &[usize]) -> Term {
    let again = |term: &Term| Box::new(substitute(term, bindings, uses));
    match term {
        Term::Bound(index) if uses[*index] == 1 => substitute(&bindings[*index], bindings, uses),
        Term::Negate(operand) => Term::Negate(again(operand)),
        Term::Binary(arithmetic, left, right) => {
            Term::Binary(*arithmetic, again(left), again(right))
        }
        Term::Select { condition, then, otherwise } => Term::Select {
            condition: substitute_condition(condition, bindings, uses),
            then: again(then),
            otherwise: again(otherwise),
        },
        term => term.clone(),
    }
}

fn substitute_condition(condition: &Condition, bindings: &[Term], uses: &[usize]) -> Condition {
    match condition {
        Condition::Compare(ordering, left, right) => Condition::Compare(
            *ordering,
            Box::new(substitute(left, bindings, uses)),
            Box::new(substitute(right, bindings, uses)),
        ),
        Condition::And(left, right) => Condition::And(
            Box::new(substitute_condition(left, bindings, uses)),
            Box::new(substitute_condition(right, bindings, uses)),
        ),
        Condition::Or(left, right) => Condition::Or(
            Box::new(substitute_condition(left, bindings, uses)),
            Box::new(substitute_condition(right, bindings, uses)),
        ),
    }
}
