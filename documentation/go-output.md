# Go output: differences from the JavaScript backend

A Go build of your program does what the JavaScript build does, wherever PureScript says what
should happen. Where JavaScript only does something by accident of how it works, such as the last
digits of a float or an `Int` result that doesn't fit in 32 bits, Go does the natural thing
instead. This guide lists those differences, and the programs the Go backend refuses to compile.
A difference that isn't listed here is a bug.

To see what the Go for your PureScript looks like, read
[What your PureScript becomes in Go](go/index.md).

## Running a program

```bash
googoo run -- first second
```

That compiles your package to Go, builds it, and runs it with `first second` as its arguments. Its
output, input and exit status are your program's. You need Go 1.27 or later and Spago on your
`PATH`. googoo fetches your packages with Spago, and `brew install spago` or `npm install -g spago`
gets you one.

- **Entry point**: `main` in `Main`, or in the module your `spago.yaml` names under `run.main`.
  Pick another with `--main Some.Module` or `--entry Some.Module.value`.
- **An entry that isn't an `Effect`**: an `Int`, `Number`, `Boolean`, `Char` or `String`, or an
  array of them, gets printed, arrays as `[1 2 3]`. Anything else (a record, a `Maybe`, a
  function) is computed but not printed, and `googoo go` says so.
- **Tests**: `googoo run --main Test.Main` runs your test suite, and a failing test exits with a
  non-zero status. `googoo test` runs tests with Node.js, so it fails on Go-only packages.
- **Arguments**: whatever follows `--`, or your `run.execArgs` when nothing does.
- **Packages**: `-p my-app` in a workspace with several.
- **Fast reruns**: the first run downloads the Go runtime. After that, if your program compiles to
  the same Go, it starts right away without building again.
- **Just the executable**: `googoo go` builds it and prints its path. It lives under
  `.spago/go/<package>/bin/`.

Want the Go source in a directory of your own instead? `googoo go out` writes it to `out/`. If
`out/` has no `go.mod` yet, you get one naming the module `iris.local/<package>`; change the
`module` line whenever you like, and the next `googoo go out` uses your name. It has no `go.sum`,
so let Go write one before you build:

```bash
googoo go out
cd out
go mod tidy
go build
```

### Profile-guided optimisation

```bash
googoo run --profile -- 4200000
```

That runs your program once while recording where it spends its time, keeps the profile in
`.spago/go/<package>/default.pgo`, and builds it again with Go's
[profile-guided optimisation](https://go.dev/doc/pgo). Every later `googoo run` and `googoo go`
builds with that profile, until you record a new one. `googoo go --profile -- 4200000` does the same
without running the program a second time, and runs it with your `run.execArgs` when nothing
follows `--`.

- **Your own profile**: `--pgo cpu.pprof` builds with a profile you recorded yourself, say with
  `runtime/pprof` in a server.
- **Without it**: `--pgo off` leaves the recorded profile out.
- **Profile a typical run**: Go optimises for what the profile saw, so run it on input like the real
  thing. A run that ends in `os.Exit`, such as `Node.Process.exit`, leaves no profile.
- **What to expect**: on our benchmarks, half of the programs that build and rebuild trees got
  9 to 50 % faster, and the rest, loops over arrays among them, a few percent at most. On macOS a
  CPU profile catches fewer of your own functions than on Linux, so a profile recorded on Linux can
  help more.

### Garbage collector settings

A Go build of a PureScript program allocates more than handwritten Go does, so the garbage collector
runs often. Go's defaults favour memory over speed: `GOGC=100` collects whenever the heap has
doubled. Setting it higher trades memory for speed:

```bash
GOGC=400 googoo run
```

On the benchmarks we measured, `GOGC=400` made allocation-heavy programs up to 30 % faster, and
peak memory grew by up to 1.6 times. A program with a large heap that it keeps around, such as a
server, can grow up to 2.5 times bigger, which is why googoo leaves `GOGC` alone. To bound it, set
`GOMEMLIMIT` as well, say `GOGC=400 GOMEMLIMIT=2GiB`: Go then collects more often as the heap gets
close to 2 GiB.

## Stack traces point at your PureScript

```purescript
module Main where

import Effect (Effect)

foreign import at :: Array Int -> Int -> Int    -- Main.go: return numbers[index]
foreign import exitWith :: Int -> Effect Int

main :: Effect Int
main = exitWith (at [ 1, 2 ] 2)
```

`googoo run` crashes with:

```
panic: runtime error: index out of range [2] with length 2 [recovered, repanicked]
...
iris.local/app/Main_ffi.At(...)
	/home/you/app/.spago/go/app/module/Main_ffi/Main.go:4
main.main_(...)
	/home/you/app/src/Main.purs:9
main.main()
	/home/you/app/.spago/go/app/module/main.go:18 +0x40
```

When a Go build crashes, the trace names the lines of your `.purs` files, library code under
`.spago` included, and so do `pprof` profiles and Delve's breakpoints (for Delve, `go build`
the output of `googoo go out` yourself: `googoo run` builds without debug info). That's the
`//line` comments in the generated Go. A function googoo inlines shows up as the line that calls
it.

They make the Go a bit noisier to read. `googoo go --no-line-directives out` leaves them out.

## What stays the same

- `Number` is a 64-bit float, and `show` formats it exactly as JavaScript does.
- `String` operations count, index and compare by UTF-16 code units. A string can hold a lone
  surrogate, and joining the two halves of a surrogate pair gives back the original character.
- `Data.String.Regex` follows JavaScript `RegExp` semantics, including the `g`, `i`, `m`, `s`, `u`
  and `y` flags and `lastIndex`.
- `String.replace` and `replaceAll` expand `$$`, `$&`, `` $` `` and `$'` in the `Replacement`, as
  JavaScript does: `String.replace (Pattern "b") (Replacement "[$&]") "abc"` is `"a[b]c"`.
- `Foreign.Object` lists its keys in JavaScript's order: keys that are array indices (`"0"`, `"2"`,
  `"10"`) first, in numeric order, then the rest in the order you inserted them. That goes for
  `keys`, `values`, folds, `toUnfoldable`, `show` and JSON objects alike.
- `toUpper` and `toLower` use JavaScript's full case mappings, including one-to-many mappings such
  as `ß` to `SS` and the final form of sigma.
- `Effect.Console` writes what Bun's console writes: `log`, `info` and `debug` to standard output,
  `warn` and `error` to standard error, indented by `group` as in Bun, and the timings of `timeLog`
  and `timeEnd` to standard error. The timings themselves differ from run to run in both. Node
  differs from Bun here: it indents every line of a message in a group, and writes timings to
  standard output.
- `Int64` and `UInt64` from the `int64` package use Go's own 64-bit arithmetic, so
  `foldl (+) zero (map Int64.fromInt (range 1 10_000_000))` is an ordinary Go loop adding `int64`s.
  They wrap, divide, compare and `show` (`42l`, `42ul`) as the package documents.

## Run-time differences

### Uncaught exceptions

An exception nothing catches is a Go panic. Go prints `panic: <message>` and a stack trace that
points into your `.purs` files, and exits with status 2, where Bun and Node exit with 1. That
goes for one thrown while the program loads, too. One that escapes an `Aff` fiber ends the
program a turn later, as in JavaScript, and its trace shows Aff's scheduler rather than the
line that threw.

So if a script or CI step checks for exit code 1 to spot a crash, have it check for anything
non-zero instead.

`Effect.Exception.stack` and `show` on an `Error` give just the `Error: <message>` header, with
no stack frames.

### `Int` is Go's `int`

An `Int` is a Go `int`: 64 bits on the 64-bit machines Go runs on (amd64, arm64), 32 bits only on
32-bit ones. In JavaScript it's a 32-bit integer that every operation wraps with `| 0`. Go doesn't
emulate that, because wrapping at 32 bits on a 64-bit machine costs instructions on every `+` and
`*`, and Go code is written with `int` anyway. As long as your numbers stay within 32 bits, which is
what a program that runs correctly on JavaScript does, both backends print the same. They differ
where a result passes 32 bits:

| Expression | JavaScript | Go |
|---|---|---|
| `top :: Int` | `2147483647` | `9223372036854775807` (`math.MaxInt`) |
| `bottom :: Int` | `-2147483648` | `-9223372036854775808` (`math.MinInt`) |
| `top + 1` | `-2147483648` | `-9223372036854775808` |
| `123456789 * 987654321` | `-67153024` | `121932631112635269` |
| `sum (1 .. 1000000)` | `1784293664` | `500000500000` |
| `Int.pow 10 10` | `1410065408` | `10000000000` |
| `bottom / -1` | `2147483648` | `math.MinInt`, the wrapped result |
| `Int.fromString "2147483648"` | `Nothing` | `Just 2147483648` |
| `Int.fromNumber 1.0e10` | `Nothing` | `Just 10000000000` |
| `Int.round 1.0e20`, `floor`, `ceil` | `2147483647` | `9223372036854775807`: they clamp to Go's `top` |
| `Int.rem 5 0` | `NaN` | `0` |

The bit operations of `Data.Int.Bits` work on all 64 bits too:

| Expression | JavaScript | Go |
|---|---|---|
| `1 `shl` 31` | `-2147483648` | `2147483648` |
| `1 `shl` 32` | `1` (the count is taken mod 32) | `4294967296` (the count is taken mod 64) |
| `(-1) `zshr` 1` | `2147483647` | `9223372036854775807` |
| `(-1) `zshr` 0` | `4294967295`, which isn't an `Int` | `-1` |
| `complement 0` | `-1` | `-1` |

More to know:

- **`toNumber` is exact up to 2^53.** An `Int` past that rounds to the nearest `Number`, and
  `fromNumber` accepts every whole `Number` from `-2^63` up to just below `2^63`.
- **Hashes and random numbers that rely on 32-bit wrapping come out different.** A hash such as
  `foldl (\h c -> h * 31 + toCharCode c) 0`, FNV's `* 16777619`, djb2's `* 33`, an LCG like
  `n * 1103515245 + 12345`, or xorshift32 with `shl 13`, `zshr 17` and `shl 5` all keep more bits in
  Go, so their values, and anything chosen by them, differ from JavaScript's. `Math.imul`-style code
  that ends in `.|. 0` doesn't cut back to 32 bits either. To get JavaScript's numbers on both
  backends, keep the value in 32 bits yourself: `(x `shl` 32) `shr` 32` is the low 32 bits with
  their sign, as JavaScript sees them, and `(x `shl` 32) `zshr` 32` the same bits unsigned. In
  JavaScript both are `x` itself, since it takes the shift count mod 32. Registry packages that do
  such arithmetic include unordered-collections (`hash`; a `HashMap` still lists its entries in
  JavaScript's order, because it only uses the low 32 bits of a hash), grain (class names), midi
  (32-bit lengths read with `shl 24`), open-memoize and yoga-protobuf.
- **JSON reads and writes the whole `Int`.** `readJSON` of `{"id": 2147483648}` into an `Int` is
  `2147483648`, where JavaScript reports a type mismatch, and `writeJSON` writes every digit of a
  large `Int`. JavaScript can't read back an integer past 2^53 exactly.
- **Arrays.** An array's length is an `int` too, so it can hold as many elements as Go allows.

Go `int64` from the `int64` package is unchanged: it's 64 bits everywhere.

### Multiply, then add

Go may compute `a * b + c` as one fused multiply-add, which rounds once where JavaScript rounds the
product and then the sum. The fused result is the more precise one, but a `Number` can differ from
JavaScript's in its last digits. Where a computation cancels to almost nothing, only rounding noise
is left, and the noise differs: summing `x / 10.0 * 3.0 - 0.3 * x` for `x` from 1 to 10 gives
`4.440892098500626e-16` in JavaScript and `9.992007221626409e-16` in Go, both for an exact 0.
Whether Go fuses depends on the CPU it compiles for: it does on arm64, and on amd64 only with
`GOAMD64=v3` or later.

### Sums over vectors

On arm64 (and wasm), with `GOEXPERIMENT=simd`, which `googoo run` sets for you, simple number
crunching over `Array Number`, `Array Int` and `Array Int64` runs on SIMD vectors:
`foldl (+) 0.0 xs`, `sum`, `foldl (*)`, `foldl max`, `map (_ * k)`, `zipWith (\x y -> a * x + y)`,
`sum (zipWith (*) xs ys)`, clamping with `min`, `max` and `if`, and so on. That's several times faster than a plain Go loop.

The catch: Go may reassociate a fold over `Number`s. A vector keeps one partial sum (or product) per
lane, adds every lane's next element at once, and combines the lanes at the end, so the elements are
added in a different order than JavaScript adds them. That goes for any fold the backend
recognises, whether you write `sum`, `foldl (+) 0.0` or your own `foldWith (\a b -> a + b)` over
`Array.foldl`. The result can differ in its last digits, the same way `[0.1, 0.2, 0.3]` gives a
different last digit depending on which pair you add first:

```purescript
Array.foldl (+) 0.0 (Array.range 0 4095 <#> \i -> toNumber (i `mod` 1000) * 0.5 * 1.19)
-- Go:         1191523.2
-- JavaScript: 1191523.1999999997
```

Like fused multiply-adds and Go's `math` functions, this is a difference in rounding only: `Number`
results aren't promised to be bit-identical to JavaScript's, so compare them with a tolerance. Maps
and `Int` arithmetic come out exactly the same. A `foldl min` over
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

### `Data.HashMap` and `Data.HashSet`

With `Int`, `Char` or `String` keys, a `HashMap` (and a `HashSet`) is a Go map, so a lookup is one
hash probe. `keys`, `values`, `toArrayBy`, folds and `show` still list the entries in the same order
as JavaScript, with one exception: keys whose hashes collide (`"Aa"` and `"BB"` do) can come out in
a different order.

Old versions stay valid, they just cost more. Change a map that something else still holds and Go
switches to JavaScript's trie from there on, which costs one pass over the whole map. Every other
key type (records, arrays, newtypes) uses the trie throughout. `traverse` over a `HashMap` and
`debugShow` aren't supported yet.

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

### `int64`'s parsing of uppercase digits

`Int64.fromStringAs` and `UInt64.fromStringAs` are `Nothing` for every number out of range. In
JavaScript, a number in a radix above 10 written in uppercase can slip past the range check and
wrap: there, `Int64.fromStringAs (radix 36) "1Z00000000000"` is `Just -9101603100908584960l`. The internal `fromString_` throws on a character that is not a digit, where JavaScript
reads digits up to it.

### Unused top-level effects

The Go backend compiles only the definitions that `main` reaches. A top-level value that nothing
uses is not compiled, so an `unsafePerformEffect` in it never runs. In JavaScript, it runs when its
module loads. Top-level values that the program does use are evaluated when the program loads, as
in JavaScript.

### Pure code can move past effects

Pure code has no effects, so the Go backend is free to compute it wherever it likes, and it does:
it moves a pure value to where it's first needed, which can be after an effect that comes before
it in your `do` block. That's usually what you want, but it bites timing code. This `timed`
measures nothing:

```purescript
timed :: forall a. String -> a -> Effect a
timed label work = do
  start <- now
  let result = work
  end <- now
  log (label <> " " <> show (un Milliseconds (unInstant end) - un Milliseconds (unInstant start)))
  pure result

main :: Effect Unit
main = do
  total <- timed "sum" (sum (1 .. 10000000))
  log (show total)
```

On Go the sum runs after the second `now`, right before `log (show total)` needs it, so `timed`
prints `sum 0.0`. On JavaScript it's measured wrong too, the other way round: the argument is
computed before `timed` even starts, so it's never between the two clocks either.

Passing the work as a function `Unit -> a` and calling it between the clocks isn't enough on its
own: once `timed` is inlined, the call is just pure code again, and it moves the same way. What
stops the move is an effect that needs the value. Hand it to one, like this `evaluate`, which puts
it in a `Ref` and reads it back (on Go the `Ref` is optimised away, and only the order stays):

```purescript
evaluate :: forall a. a -> Effect a
evaluate value = Ref.new value >>= Ref.read

timed :: forall a. String -> (Unit -> a) -> Effect a
timed label work = do
  start <- now
  result <- evaluate (work unit)
  end <- now
  log (label <> " " <> show (un Milliseconds (unInstant end) - un Milliseconds (unInstant start)))
  pure result

main :: Effect Unit
main = do
  total <- timed "sum" \_ -> sum (1 .. 10000000)
  log (show total)
```

Now both backends time the sum: the thunk keeps JavaScript from computing it before `timed` starts,
and `evaluate` keeps Go from computing it after `timed` is done.

### Pure values can be shared

Pure code gives the same answer every time, so the Go backend computes it once where it can: two
calls of the same function on the same arguments become one, and `Array.concat [ mempty, errors ]`
is `errors` itself. You can only tell with `unsafeRefEq`, which then answers `true` where
JavaScript built two arrays and answers `false`.

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
vendored backtracking engine (regexp2, in its ECMAScript mode) instead.

Without the `u` flag, `.` and character classes match a whole emoji or other character outside the
Basic Multilingual Plane on Go, but each of its UTF-16 halves on JavaScript:
`Regex.split (unsafeRegex "." global) "😀x"` is `["","",""]` on Go and `["","","",""]` on
JavaScript. Use the `u` flag to get the same behaviour on both. Other rare edge cases in patterns
without the `u` flag can also match differently from JavaScript.

### Parallel arrays

`Data.Array.Parallel.parallelMap` runs the mapped function on several goroutines. The function is
pure, so the result is the same. A function that hides an effect with `unsafePerformEffect` runs
its effects in an unpredictable order. If several elements throw, the program rethrows the first
element's exception, as JavaScript's sequential map does.

### `traverse` over an `Array`

Go builds the applies of an `Array` `traverse` (and `sequence`, `for`) left to right, one element
after the other. JavaScript splits the array in halves and builds a balanced tree of applies. For a
lawful applicative, such as `Effect`, `Maybe`, `Either`, `V`, `State` or a `Writer`, both give the
same result, and the left fold is faster.

An applicative that lets you see how its applies are nested, like one that records them as a
string, shows a different shape: three elements are `((pure <*> 1) <*> 2) <*> 3` in Go. `ParOm`,
where the nesting decides what runs or combines first, uses JavaScript's balanced tree in Go too.
`ParIO` uses the left fold: its applies run their two sides on goroutines, so the order they start
in isn't fixed by the shape anyway. `ParAff` has its own parallel traversal.

`traverse1` over a `NonEmptyArray` works the same way. Go calls the function on the first element
first and nests the applies to the left, `(1 <*> 2) <*> 3`. JavaScript calls it on the last element
first and nests them to the right, `1 <*> (2 <*> 3)`. A lawful applicative gives the same result
either way, and the left fold is faster. `ParOm` gets JavaScript's order in Go too.

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

func Repeat[A any](n int, x A) []A {
	xs := make([]A, n)
	for i := range xs {
		xs[i] = x
	}
	return xs
}

func Every(n int, f func(int)) {
	for i := range n {
		f(i)
	}
}
```

Every foreign import is a Go function or variable with its name capitalised. Call the package
whatever you like, googoo renames it.

| PureScript | Go |
| --- | --- |
| `Int` | `int` |
| `Number` | `float64` |
| `String` | `string` |
| `Boolean` | `bool` |
| `Unit` | `struct{}` |
| `Array a` | `[]A` |
| `Effect a` | `func() A`, and `Effect Unit` is just `func()` (only where an effect is passed around) |
| `forall a.` | a type parameter `[A any]` |
| `foreign import data T` | any Go type you declare as `T` |

- **Strings are WTF-8.** A JavaScript string is UTF-16 and can hold half a character, a lone
  surrogate like `"\uD83D"`. Plain UTF-8 can't store that, so googoo uses WTF-8 ("wobbly
  transformation format"): ordinary text is byte for byte normal UTF-8, and only a lone surrogate
  gets the extra three-byte encoding. You'll never see it with normal text. When your Go hands a
  string to PureScript, make it valid UTF-8; bytes from outside (files, sockets, protobuf) are
  worth a `utf8.Valid` first, or keep them as bytes.
- **Arguments come all at once.** `repeat :: Int -> a -> Array a` is `Repeat(n int, x A)`, not a
  function returning a function.
- **Calling a function performs its effect.** `elapsed :: Stopwatch -> Effect Number` is
  `Elapsed(stopwatch Stopwatch) float64`: no thunk to return, googoo calls it when the effect runs.
  `start` has no arguments, so `Start` _is_ the effect.
- **Callbacks stay curried and perform when called.** `Int -> Effect Unit` is `func(int)`, and
  `a -> b -> Effect c` is `func(A) func(B) C`.
- **An `Effect` callback gets called right away.** Go calls it while your foreign runs, on the same
  goroutine, like `Every` above or a sort's comparator. googoo puts nothing around it. Calling one
  later, from a goroutine, is a bug: see
  [Callbacks from goroutines](#callbacks-from-goroutines).
- **`EffectFn` and `STFn` work the same way.** `EffectFn2 a b c` is `func(A, B) C`.
- **An `Int` is an `int`, everywhere.** Hand it straight to Go APIs: `os.Exit(code)`, `make([]A, n)`,
  `time.Duration(ms) * time.Millisecond`. Where JavaScript must agree, remember that its `Int` has
  32 bits: a file size is better a `Number` if the same code also runs on JavaScript.
- **A value without arguments or effects is a variable.** `greeting :: String` is
  `var Greeting string`, not a function.
- **Values with a `forall` are generic functions.** Go has no generic variables, so
  `undefined :: forall a. UndefinedOr a` is `func Undefined[A any]() UndefinedOr[A]`.
- **Name clashes get a `Type` suffix.** If your module has a `foreign import data Event` and a
  value `event`, the Go type is `EventType`.

### Callbacks from goroutines

Go code loves goroutines: `net/http` calls your handler on the request's goroutine, a timer fires
on one of its own. PureScript runs one piece at a time, as on JavaScript's event loop, so a
callback like that can't just go and touch a `Ref`. It's the same deal as a `Promise` in JavaScript
FFI: its callbacks run later, not inside your call, and the types should say so.

So type a callback that Go calls from a goroutine `IO`, from
[purescript-go](https://github.com/i-am-the-slime/purescript-go)'s `Go.IO`. When it needs
an `Effect`, `liftEffect` waits for its turn on the event loop and runs it there:

```purescript
module Ex.Workers where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_, makeAff, nonCanceler)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Effect.Ref as Ref
import Go.IO (IO)

foreign import onWorkersImpl :: Int -> IO Unit -> Effect Unit -> Effect Unit

onWorkers :: Int -> IO Unit -> Aff Unit
onWorkers workers handler = makeAff \done -> onWorkersImpl workers handler (done (Right unit)) $> nonCanceler

main :: Effect Unit
main = launchAff_ do
  visits <- Ref.new 0 # liftEffect
  onWorkers 32 (Ref.modify_ (_ + 1) visits # liftEffect)
  total <- Ref.read visits # liftEffect
  log (show total <> " visits from 32 goroutines")
```

```go
package ffi

import (
	"sync"

	"github.com/i-am-the-slime/iris-go/eventloop"
)

func OnWorkersImpl(workers int, handler func(), done func()) {
	retire := eventloop.Hold()
	go func() {
		var running sync.WaitGroup
		for range workers {
			running.Go(handler)
		}
		running.Wait()
		done()
		retire()
	}()
}
```

```
32 visits from 32 goroutines
```

An `IO Unit` is a plain `func()` in Go, so the Go side just calls it, from as many goroutines as it
likes. googoo doesn't wrap anything at the crossing: `liftEffect` is the only place that waits.

Two more things in there:

- **What `makeAff` hands you is fine from any goroutine.** `done` only wakes up the fiber that
  waits for it, and so do `EffectFnAff`'s callbacks. That's why `done` can stay an `Effect`.
- **`eventloop.Hold()` keeps the program alive.** Like node, a Go program ends once nothing is
  left to run, even with a fiber waiting on Go. `Hold` says there's more to come; call what it
  returns once you're done.

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
`X_respondNow`, `"content-type"` is `Content_type`.

If two labels end up with the same name, the one starting with a lower-case letter wins, so `a` is
always `A`. A label starting with a capital gets a `_` behind it: `"A"` next to `a` is `A_`. Anything
else that clashes gets a number: `"content-type"` next to `content_type` is `Content_type2`. In the
structs googoo writes, every field whose name isn't just its label with a capital first letter has
the label as a tag, so you can look it up. `{ "A" :: Int, a :: String, "content-type" :: String,
content_type :: String }` is:

```go
type Header struct {
	A             string
	Content_type2 string `purescript:"content-type"`
	Content_type  string
	A_            int    `purescript:"A"`
}
```

Tags are optional in your own structs; googoo only goes by the field names. A field can hold another
named record if that one has a struct too: `Headers []Header`.

A function in a field looks just like a callback: curried, and it performs its effect when called,
unless it's an `EffectFn`, which takes all its arguments at once. That holds inside arrays and
nested records too:

```purescript
type Routes =
  { handle :: EffectFn2 String (String -> Effect Unit) Unit
  , add :: Int -> Int -> Int
  , each :: Array (String -> Effect Unit)
  }
```

```go
type Routes struct {
	Handle func(string, func(string))
	Add    func(int) func(int) int
	Each   []func(string)
}
```

A record without a matching struct still works, but Go only sees it as an untyped `any`.

A big module can spread its Go over several files: `Stopwatch.go`, `Stopwatch.laps.go` and so on.
`_test.go` files are ignored.

### Embedded files

`//go:embed` works. Put the files next to your `.go` file:

```
src/Greeting.purs
src/Greeting.go
src/greeting.txt
```

```purescript
module Greeting where

foreign import greeting :: String
```

```go
package ffi

import _ "embed"

//go:embed greeting.txt
var Greeting string
```

googoo copies whatever the patterns match along with the `.go` file, so your program is one binary
with its fonts, templates and data baked in. Patterns work as in Go: several per line, quoted,
globs like `fonts/*.ttf`, whole directories (minus files starting with `.` or `_`, unless you
write `all:fonts`). Symlinks are followed, so several modules can link to one asset folder.

A pattern has to stay beside or below the `.go` file, and has to match something. If it doesn't,
googoo says so before `go build` runs:

```
src/Greeting.go: //go:embed greeting.txt: no matching files found
```

### Libraries

Libraries work the same way. If a package you install has `.go` files next to its `.js` files, googoo
picks them up. iris-go also ships Go versions of some popular libraries that don't have their own
yet, such as hyrule's `FRP.Event`, and of all the core libraries. A `.go` file next to the source
always wins.

You only need Go for the foreign imports your program actually uses. If a module has no Go at all,
googoo tells you:

```
cannot specialize Main.main: foreign import Stopwatch.elapsed has no Go implementation; write one in a Go file next to its module's source (Foo.go beside Foo.purs)
```

If the `.go` file is there but a function is missing, `go build` tells you instead:

```
./main.go:18:26: undefined: Stopwatch_ffi.Elapsed
```

## Programs the Go backend rejects

googoo type-checks the whole program and then specialises every polymorphic function to the concrete
types that `main` uses. Programs that cannot be specialised fail to compile, with a message that
starts `cannot specialize <definition>:`. The JavaScript backend compiles them.

### Polymorphic recursion

Polymorphic recursion that only changes the types of plain values compiles. Some recursion that
also grows the type class evidence it passes compiles too, using run-time dictionaries. So do
functions that turn a run-time number into a type-level one, like `reifyPrecision` from
fixed-precision and `reifyInt` from typelevel: the continuation you give them takes its dictionary
at run time, and the compiler prints a note saying so. These cases do not compile yet:

- recursion through an instance member, such as a derived `Show` on a nested data type. The compiler
  reports `specialization exceeded <limit> instances`;
- growing evidence of a class with polymorphic members, such as `Functor` or `Foldable`;
- growing evidence of a compiler-solved constraint, such as `IsSymbol`, `Reflectable` or `Lacks`.

### `unsafeCoerce` between unrelated types

Each type has its own Go representation, so most `unsafeCoerce`s between two types with different
representations don't compile. The message looks like
`unsafeCoerce from { line, column } (Go ColumnLine) to Data.Argonaut.Core.Json (Go argonaut.Json) changes representation`,
often followed by why and what to do instead.

These compile:

- between a newtype and the type it wraps, and between types with the same representation;
- a record to `Foreign`, and a record to a `Foreign.Object` and back, the way
  `Data.Homogeneous.Record` does it: Go copies the fields across by name;
- `unsafeCoerce unit` to any type, the usual trick for a value nobody looks at (see below).

These don't:

- a record to `Json`. On JavaScript a record already is a JSON object, on Go it's a struct. Build
  the `Json` with `encodeJson` or `fromObject` instead;
- a value typed `Unit` (or kept as `Void`) that's coerced back to a type with a value, like a
  function `a -> m b` stored as `a -> m Unit`. Go keeps no value for `Unit`, so the original value is
  gone by then. Keep its real type instead.

#### `unsafeCoerce unit`

On JavaScript `unsafeCoerce unit` is `undefined`. On Go it's the Go zero value of the type you
coerce it to, so code that does look at it gets a different answer:

```purescript
nothingInParticular :: forall a. a
nothingInParticular = unsafeCoerce unit
```

| Expression | Go | JavaScript |
|---|---|---|
| `show ((nothingInParticular :: Number) + 1.0)` | `1.0` | `NaN` |
| `show ((nothingInParticular :: Int) + 1)` | `1` | `0` |
| `show (nothingInParticular :: String)` | `""` | crashes |
| `show (nothingInParticular :: Boolean)` | `false` | crashes |
| `show (length (nothingInParticular :: Array Int))` | `0` | crashes |

A data type, a record of pointers or a function becomes Go's `nil`. That's fine as long as nothing
looks inside it, which is what the trick is for: typelevel's `undefined` values, for instance, work.

### Other constructs

These report `<construct> is not supported by the Go backend yet`:

- constrained higher-rank arguments, such as `(forall a. Show a => a -> String) -> …`;
- foreign imports with constraints;
- inferred polymorphic local bindings: a `let` or `where` function whose polymorphic or constrained
  type the checker infers, rather than reading it from an annotation.

### The entry module

Go cannot import a `main` package, so no other module may import the module that contains `main`.
