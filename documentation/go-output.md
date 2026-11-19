# Go output: differences from the JavaScript backend

The Go backend aims to produce a program whose standard output and exit status are byte for byte
the same as the JavaScript build's. This guide lists the places where it does not, and the programs
it refuses to compile. Everything not listed here is meant to behave as it does in JavaScript; a
difference that is not listed is a bug.

## What stays the same

- `Int` is a 32-bit integer and wraps on overflow, as `| 0` does in JavaScript.
- `Number` is a 64-bit float, and `show` formats it exactly as JavaScript does.
- `String` operations count, index and compare by UTF-16 code units. A string can hold a lone
  surrogate, and joining the two halves of a surrogate pair gives back the original character.
- `Data.String.Regex` follows JavaScript `RegExp` semantics, including the `g`, `i`, `m`, `s`, `u`
  and `y` flags and `lastIndex`.
- `toUpper` and `toLower` use JavaScript's full case mappings, including one-to-many mappings such
  as `ß` to `SS` and the final form of sigma.
- `Effect.Console` writes what Bun's console writes: `log`, `info` and `debug` to standard output,
  `warn` and `error` to standard error, indented by `group` as in Bun, and the timings of `timeLog`
  and `timeEnd` to standard error. The timings themselves differ from run to run in both. Node
  differs from Bun here: it indents every line of a message in a group, and writes timings to
  standard output.
- An uncaught exception ends the program with exit status 1, including one thrown while the program
  loads or inside an `Aff` fiber.

## Run-time differences

### Uncaught exceptions and stacks

An uncaught exception prints `Error: <message>` to standard error. Bun and Node print the source
line and a stack trace as well. For the same reason, `Effect.Exception.stack` and `show` on an
`Error` return only the `Error: <message>` header, with no stack frames.

### Division of the smallest `Int` by -1

`bottom / -1` is `-2147483648`, the wrapped result. In JavaScript it is `2147483648`, which is not
a valid `Int` and is a bug in the JavaScript Prelude's `intDiv`. `bottom `mod` -1` is `0` in both.

### Other `Int` results outside the `Int` range

A few JavaScript foreigns compute with doubles and return a value that is not an `Int` at all. The
Go backend keeps every `Int` a 32-bit integer instead:

| Expression | JavaScript | Go |
|---|---|---|
| `Int.rem 5 0` | `NaN` | `0` |
| `Bits.zshr (-3) 0` | `4294967293` | `-3` |
| `Bits.zshr (-1073741824) (-1073741824)` | `3221225472` | `-1073741824` |

`zshr` is JavaScript's unsigned `>>>`, whose result does not fit an `Int` when the top bit stays
set. `Int.quot`, `div` and `mod` by zero are `0` in both.

Such a value then behaves differently wherever it is used. A `NaN` index passes JavaScript's bounds
check, so `Array.index [] (Int.rem 5 0)` is `Just undefined`, which crashes or prints an empty
element when it is shown or matched, while `STArray.poke (Int.rem 5 0) x array` is `false` and
changes no element. In Go the index is `0`: the lookup is `Nothing`, and the poke writes the first
element of a non-empty array and is `true`. Likewise `Array.range 0 (clamp 0 1 (div bottom
(-1)))` is `[0,1]` in JavaScript and `[0]` in Go.

### Trigonometric, exponential and power functions

`sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `exp`, `log` and `pow` from `Data.Number`
use Go's `math` package. ECMAScript leaves their last bit to the engine, and V8 and JavaScriptCore
already disagree with each other, so a result can differ from JavaScript's in the last digit:
`7.892418775380858` where JavaScript prints `7.892418775380859`. The special cases ECMAScript
defines (`NaN`, infinities, `-0`, `pow` with a `NaN` exponent or a base of ±1) are the same. A
program that needs one engine's exact digits can bring its own implementation through a foreign
import.

### Unused top-level effects

The Go backend compiles only the definitions that `main` reaches. A top-level value that nothing
uses is not compiled, so an `unsafePerformEffect` in it never runs. In JavaScript, it runs when its
module loads. Top-level values that the program does use are evaluated when the program loads, as
in JavaScript.

### Deep recursion

Go stacks grow to 1 GB, so recursion that is not tail-recursive goes far deeper before it fails.
A program that overflows the JavaScript stack with a `RangeError` may finish in Go. A Go stack
overflow is a fatal Go runtime error, not a PureScript exception, so `try` and `catchException`
cannot catch it.

### `localeCompare`

`Data.String.Common.localeCompare` uses the Unicode CLDR root collation, as JavaScript does without
a locale. The weights come from Go's `golang.org/x/text`, not from the ICU that Bun and Node
bundle, and characters are weighed one at a time. Results can differ:

- where the two CLDR versions disagree, for example in the order of some CJK ideographs;
- for contractions, sequences of characters that the collation weighs together;
- for combining marks that follow one another out of canonical order.

### Regular expressions

Most patterns are translated to Go's RE2 engine. A pattern with backreferences or lookaround uses a
vendored backtracking engine (regexp2, in its ECMAScript mode) instead. Rare edge cases in patterns
without the `u` flag can match differently from JavaScript.

### Parallel arrays

`Data.Array.Parallel.parallelMap` runs the mapped function on several goroutines. The function is
pure, so the result is the same. A function that hides an effect with `unsafePerformEffect` runs
its effects in an unpredictable order. If several elements throw, the program rethrows the first
element's exception, as JavaScript's sequential map does.

## Programs the Go backend rejects

Iris type-checks the whole program and then specialises every polymorphic function to the concrete
types that `main` uses. Programs that cannot be specialised fail to compile, with a message that
starts `cannot specialize <definition>:`. The JavaScript backend compiles them.

### Foreign imports

JavaScript foreign files are not used. Each foreign module needs a Go implementation in
`go-ffi/<Module>.go` or a `go-ffi/<Module>/` package, and each `foreign import data` needs a named
Go type there. Without one, the compiler reports `foreign import <name> has no Go implementation` or
`foreign data type <name> has no Go representation`. Only the foreign imports that `main` reaches
need an implementation. The support module provides implementations for the core libraries.

Go has no generic variables, so a quantified foreign value without arguments, such as
`undefined :: forall a. UndefinedOr a`, is a generic Go function without parameters:
`func Undefined[A any]() UndefinedOr[A]`. It has one type parameter per quantifier, in the order of
the `forall`, and the compiler calls it with explicit type arguments, spelled as the package's
functions take them (an `Int` is a Go `int`). When the value is an effect, such as
`forall a. Effect (Box a)`, the instantiated function is the effect itself, and the compiler calls
it to perform the effect.

### Polymorphic recursion

Polymorphic recursion that only changes the types of plain values compiles. Some recursion that
also grows the type class evidence it passes compiles too, using run-time dictionaries. These cases
do not compile yet:

- recursion through an instance member, such as a derived `Show` on a nested data type. The compiler
  reports `specialization exceeded <limit> instances`;
- growing evidence of a class with polymorphic members, such as `Functor` or `Foldable`;
- growing evidence of a compiler-solved constraint, such as `IsSymbol`, `Reflectable` or `Lacks`.

### `unsafeCoerce` between unrelated types

Each type has its own Go representation, so `unsafeCoerce` between two types with different
representations does not compile. The message is
`representation changes between unrelated types is not supported by the Go backend yet`.
`unsafeCoerce` between a newtype and the type it wraps, and between types with the same
representation, compiles.

### Other constructs

These report `<construct> is not supported by the Go backend yet`:

- constrained higher-rank arguments, such as `(forall a. Show a => a -> String) -> …`;
- foreign imports with constraints;
- inferred polymorphic local bindings: a `let` or `where` function whose polymorphic or constrained
  type the checker infers, rather than reading it from an annotation.

### The entry module

Go cannot import a `main` package, so no other module may import the module that contains `main`.
