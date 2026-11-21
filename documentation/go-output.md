# Go output: differences from the JavaScript backend

A Go build of your program does what the JavaScript build does, wherever PureScript says what
should happen. Where JavaScript only does something by accident of how it works, such as the last
digits of a float or an `Int` result that doesn't fit in 32 bits, Go does the natural thing
instead. This guide lists those differences, and the programs the Go backend refuses to compile.
A difference that isn't listed here is a bug.

## Running a program

```bash
iris run --go -- first second
```

That compiles your package to Go, builds it, and runs it with `first second` as its arguments. Its
output, input and exit status are your program's. You need Go 1.27 or later on your `PATH`;
nothing else to set up.

- **Entry point**: `main` in `Main`, or in the module your `spago.yaml` names under `run.main`.
  Pick another with `--main Some.Module` or `--entry Some.Module.value`.
- **Arguments**: whatever follows `--`, or your `run.execArgs` when nothing does.
- **Packages**: `-p my-app` in a workspace with several.
- **Fast reruns**: the first run downloads the Go runtime. After that, if your program compiles to
  the same Go, it starts right away without building again.
- **Just the executable**: `iris go` builds it and prints its path. It lives under
  `.spago/go/<package>/bin/`.
- **Hacking on the runtime**: `IRIS_GO=~/code/iris-go iris run --go` builds against your checkout
  of [iris-go](https://github.com/i-am-the-slime/iris-go) instead of the release.

Want the Go source in a directory of your own instead? `iris go out` writes it to `out/`, which
needs a `go.mod`.

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
| `123456789 * 987654321` | `-67153024` | `-67153019` |
| `Int.pow 3 40` | `689956864` | `689956897` |

`zshr` is JavaScript's unsigned `>>>`, whose result does not fit an `Int` when the top bit stays
set. `Int.quot`, `div` and `mod` by zero are `0` in both.

`*` and `Int.pow` wrap like 32-bit integers in Go, so they keep the low 32 bits of the exact
product. JavaScript computes the product as a double first, which drops low bits once it passes
2^53, and then cuts it to 32 bits. Products below 2^53 are the same in both.

Such a value then behaves differently wherever it is used. A `NaN` index passes JavaScript's bounds
check, so `Array.index [] (Int.rem 5 0)` is `Just undefined`, which crashes or prints an empty
element when it is shown or matched, while `STArray.poke (Int.rem 5 0) x array` is `false` and
changes no element. In Go the index is `0`: the lookup is `Nothing`, and the poke writes the first
element of a non-empty array and is `true`. Likewise `Array.range 0 (clamp 0 1 (div bottom
(-1)))` is `[0,1]` in JavaScript and `[0]` in Go.

### Multiply, then add

Go may compute `a * b + c` as one fused multiply-add, which rounds once where JavaScript rounds the
product and then the sum. The fused result is the more precise one, but a `Number` can differ from
JavaScript's in its last digits. Where a computation cancels to almost nothing, only rounding noise
is left, and the noise differs: summing `x / 10.0 * 3.0 - 0.3 * x` for `x` from 1 to 10 gives
`4.440892098500626e-16` in JavaScript and `9.992007221626409e-16` in Go, both for an exact 0.
Whether Go fuses depends on the CPU it compiles for: it does on arm64, and on amd64 only with
`GOAMD64=v3` or later.

### Sums over vectors

On arm64 (and wasm), with `GOEXPERIMENT=simd`, which `iris run --go` sets for you, simple number
crunching over `Array Number` and `Array Int` runs on SIMD vectors: `foldl (+) 0.0 xs`, `sum`,
`foldl (*)`, `foldl max`, `map (_ * k)`, `zipWith (\x y -> a * x + y)`, `sum (zipWith (*) xs ys)`,
clamping with `min`, `max` and `if`, and so on. That's several times faster than a plain Go loop.

The catch: a vector adds up several elements at once and combines the partial sums at the end, so
a `Number` sum or product is added in a different order than JavaScript does it. The result can
differ in its last digits, the same way `[0.1, 0.2, 0.3]` gives a different last digit depending on
which pair you add first. Maps and `Int` arithmetic come out exactly the same. A `foldl min` over
`Number`s stays an ordinary loop, because `Data.Ord.min` lets a `NaN` win only when it comes last.

Everywhere else (amd64, or without `GOEXPERIMENT=simd`) you get a plain loop that adds in
JavaScript's order.

### Trigonometric, exponential and power functions

`sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `exp`, `log` and `pow` from `Data.Number`
use Go's `math` package. ECMAScript leaves their last bit to the engine, and V8 and JavaScriptCore
already disagree with each other, so a result can differ from JavaScript's in the last digit:
`7.892418775380858` where JavaScript prints `7.892418775380859`. The special cases ECMAScript
defines (`NaN`, infinities, `-0`, `pow` with a `NaN` exponent or a base of ±1) are the same. A
program that needs one engine's exact digits can bring its own implementation through a foreign
import.

### `Foreign.Object` key order

```purescript
Object.keys (Object.fromFoldable [ "b" /\ 1, "10" /\ 2, "a" /\ 3, "2" /\ 4 ])
-- Go:         ["b","10","a","2"]
-- JavaScript: ["2","10","b","a"]
```

Go keeps keys in the order you inserted them. JavaScript lists keys that look like array indices
first, in numeric order. `Foreign.Object` doesn't promise any order, and this goes for `keys`,
`values`, folds, `toUnfoldable`, `show` and JSON objects (argonaut and yoga-json) alike. Want
sorted keys? Use `Object.toAscUnfoldable`, or sort the keys yourself.

### `replace` and `replaceAll`

```purescript
String.replace (Pattern "b") (Replacement "[$&]") "abc"
-- Go:         "a[$&]c"
-- JavaScript: "a[b]c"
```

The `Replacement` goes in exactly as you wrote it. JavaScript expands `$$`, `$&`, `` $` `` and `$'`
in it. `Data.String.Regex.replace` is a regex replacement and still expands `$1` and friends.

### Error messages

Messages that the libraries don't spell out are Go's own:

| Call | Go | JavaScript (Bun) |
|---|---|---|
| `jsonParser "[1,]"` (argonaut) | `Invalid JSON at offset 3` | `JSON Parse error: Unexpected comma at the end of array expression` |
| `regex "(" noFlags` | ``Invalid regex /(/: missing closing ): `(` `` | `Invalid regular expression: missing )` |

The offset counts UTF-16 code units from the start of the input. Whether something parses is the
same in both.

### `JS.BigInt.fromString` of a lone sign

`fromString "-"` and `fromString "+"` are `Nothing`. Bun says `Just 0`, Node throws.

### Unused top-level effects

The Go backend compiles only the definitions that `main` reaches. A top-level value that nothing
uses is not compiled, so an `unsafePerformEffect` in it never runs. In JavaScript, it runs when its
module loads. Top-level values that the program does use are evaluated when the program loads, as
in JavaScript.

### Deep recursion

Go stacks grow to 1 GB, so recursion that is not tail-recursive goes far deeper before it fails.
A program that overflows the JavaScript stack with a `RangeError` may finish in Go, and so does
`Data.BigInt.toBase 1` of a large number. A Go stack
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

## Foreign imports

Your `.js` files don't come along to Go. Put a `.go` file right next to them instead:

```
src/Stopwatch.purs
src/Stopwatch.js
src/Stopwatch.go
```

```purescript
module Stopwatch where

import Prelude (Unit)
import Effect (Effect)

foreign import data Stopwatch :: Type

foreign import start :: Effect Stopwatch
foreign import elapsed :: Stopwatch -> Effect Number
foreign import repeat :: forall a. Int -> a -> Array a
foreign import every :: Int -> (Int -> Effect Unit) -> Effect Unit
```

```go
package ffi

import "time"

type Stopwatch struct{ started time.Time }

func Start() Stopwatch { return Stopwatch{started: time.Now()} }

func Elapsed(stopwatch Stopwatch) float64 {
	return float64(time.Since(stopwatch.started).Milliseconds())
}

func Repeat[A any](n int32, x A) []A {
	xs := make([]A, n)
	for i := range xs {
		xs[i] = x
	}
	return xs
}

func Every(n int32, f func(int32)) {
	for i := int32(0); i < n; i++ {
		f(i)
	}
}
```

Every foreign import is a Go function with its name capitalised. Call the package whatever you
like, Iris renames it.

| PureScript | Go |
| --- | --- |
| `Int` | `int32` |
| `Number` | `float64` |
| `String` | `string` |
| `Boolean` | `bool` |
| `Unit` | `struct{}` |
| `Array a` | `[]A` |
| `Effect a` | `func() A`, and `Effect Unit` is just `func()` (only where an effect is passed around) |
| `forall a.` | a type parameter `[A any]` |
| `foreign import data T` | any Go type you declare as `T` |

- **Arguments come all at once.** `repeat :: Int -> a -> Array a` is `Repeat(n int32, x A)`, not a
  function returning a function.
- **Calling a function performs its effect.** `elapsed :: Stopwatch -> Effect Number` is
  `Elapsed(stopwatch Stopwatch) float64`: no thunk to return, Iris calls it when the effect runs.
  `start` has no arguments, so `Start` _is_ the effect.
- **Callbacks stay curried and perform when called.** `Int -> Effect Unit` is `func(int32)`, and
  `a -> b -> Effect c` is `func(A) func(B) C`.
- **`EffectFn` and `STFn` work the same way.** `EffectFn2 a b c` is `func(A, B) C`.
- **An `Int` is an `int32`, everywhere.** Where a Go API wants an `int`, convert it yourself:
  `os.Exit(int(code))`. Where a Go value might not fit 32 bits, decide what to do about it rather
  than letting `int32(…)` cut it off: a file size is better a `Number`.
- **Values with a `forall` are generic functions.** Go has no generic variables, so
  `undefined :: forall a. UndefinedOr a` is `func Undefined[A any]() UndefinedOr[A]`.
- **Name clashes get a `Type` suffix.** If your module has a `foreign import data Event` and a
  value `event`, the Go type is `EventType`.

### Records

Give a record a name and declare a Go struct with the same name, and the two are the same thing:

```purescript
type Reading = { city :: String, celsius :: Number, rainy :: Boolean }

foreign import current :: String -> Effect Reading
foreign import report :: Reading -> String
```

```go
type Reading struct {
	City    string
	Celsius float64
	Rainy   bool
}

func Current(city string) Reading {
	return Reading{City: city, Celsius: 11.5, Rainy: true}
}

func Report(reading Reading) string {
	return fmt.Sprintf("%s: %.1f°C", reading.City, reading.Celsius)
}
```

Your PureScript builds, reads and updates a `Reading` as usual, and Go gets the struct as it is.
Fields are the labels with their first letter capitalised. Characters Go doesn't allow in a name
become `_`, and a label that doesn't start with a letter gets an `X` in front: `_respondNow` is
`X_respondNow`, `"content-type"` is `Content_type`. If two labels end up with the same name, the
second gets a number: `content_type` next to `"content-type"` is `Content_type2`. A field can hold
another named record if that one has a struct too:
`Headers []Header`.

A record without a matching struct still works, but Go only sees it as an untyped `any`.

A big module can spread its Go over several files: `Stopwatch.go`, `Stopwatch.laps.go` and so on.
`_test.go` files are ignored.

### Libraries

Libraries work the same way. If a package you install has `.go` files next to its `.js` files, Iris
picks them up. iris-go also ships Go versions of some popular libraries that don't have their own
yet, such as hyrule's `FRP.Event`, and of all the core libraries. A `.go` file next to the source
always wins.

You only need Go for the foreign imports your program actually uses. If a module has no Go at all,
Iris tells you:

```
cannot specialize Main.main: foreign import Stopwatch.elapsed has no Go implementation; write one in a Go file next to its module's source (Foo.go beside Foo.purs)
```

If the `.go` file is there but a function is missing, `go build` tells you instead:

```
./main.go:18:26: undefined: Stopwatch_ffi.Elapsed
```

## Programs the Go backend rejects

Iris type-checks the whole program and then specialises every polymorphic function to the concrete
types that `main` uses. Programs that cannot be specialised fail to compile, with a message that
starts `cannot specialize <definition>:`. The JavaScript backend compiles them.

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
