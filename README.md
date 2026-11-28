# googoo — 'cause I don't want the world to see Go

googoo is a fork of [Iris](https://github.com/purefunctor/purescript-iris), the PureScript
compiler, that also compiles your program to Go. You get a single native binary that starts right
away, uses every core you've got and talks to Go libraries through foreign imports. Everything else
Iris does works as it does upstream, and upstream's README follows the Go part.

## Getting started

### Install

```bash
brew install spago i-am-the-slime/tap/googoo
```

- **Go 1.27 or later**, which Homebrew brings along. An older Go downloads 1.27 by itself on
  your first build, unless you've set `GOTOOLCHAIN=local`.
- **Spago** fetches your packages. Got Node already? `npm install -g spago` works too.
- **No Homebrew?** The [releases](https://github.com/i-am-the-slime/iris-go-backend/releases) have
  archives for macOS, Linux and Windows. Put `googoo` somewhere on your `PATH`.

googoo used to be called `iris`. The `iris` command still works for now: it tells you it's called
googoo now and then runs googoo.

### Your first program

```bash
mkdir hello && cd hello
googoo new
googoo run
```

```
🍝
```

`googoo run` compiles your package to Go, builds it and runs it. The first run downloads the Go
runtime, a second run of an unchanged program skips the build.

### A project on the Go package set

`googoo new` starts you on the registry's package set. The Go libraries, like Go's own maps, files
and HTTP, are in the [Go package set](https://github.com/rowtype-yoga/purescript-go-package-sets).
Make a project and give it this `spago.yaml`:

```bash
mkdir words && cd words
googoo new
```

```yaml
package:
  name: words
  dependencies:
    - console
    - effect
    - foldable-traversable
    - go-map
    - go-os
    - maybe
    - newtype
    - prelude
    - tuples
  test:
    main: Test.Main
    dependencies:
      - go-spec
      - spec
workspace:
  packageSet:
    url: https://raw.githubusercontent.com/rowtype-yoga/purescript-go-package-sets/go-0.1.18-20261127/packages.json
```

The test dependencies matter: the `assert` that `googoo new` puts there isn't in the Go set, and
Spago refuses a package that isn't in the set. Later on, `googoo add go-time` adds one more.

`src/Words.purs` counts words in Go's built-in map:

```purescript
module Words (countWords) where

import Prelude

import Data.Foldable (for_)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple.Nested (type (/\))
import Effect (Effect)
import Go.Map as GoMap

countWords :: Array String -> Effect (Array (String /\ Int))
countWords words = do
  counts <- GoMap.new
  for_ words \word -> GoMap.alter (Just <<< maybe 1 (_ + 1)) word counts
  GoMap.entries counts
```

`src/Main.purs` counts its arguments:

```purescript
module Main where

import Prelude

import Data.Foldable (for_)
import Data.Newtype (un)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Go.OS (Arg(..))
import Go.OS as OS
import Words (countWords)

main :: Effect Unit
main = do
  words <- OS.args
  counts <- countWords (map (un Arg) words)
  for_ counts \(word /\ count) -> log (word <> ": " <> show count)
```

```
$ googoo run -- to be or not to be
be: 2
not: 1
or: 1
to: 2
```

### Test

`test/Test/Main.purs`, with [purescript-spec](https://github.com/purescript-spec/purescript-spec)
and go-spec's runner:

```purescript
module Test.Main where

import Prelude

import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Class (liftEffect)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Go (runSpecAndExitProcess)
import Words (countWords)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "countWords" do
    it "counts every word, sorted" do
      counts <- countWords [ "to", "be", "or", "not", "to", "be" ] # liftEffect
      counts `shouldEqual` [ "be" /\ 2, "not" /\ 1, "or" /\ 1, "to" /\ 2 ]
```

```
$ googoo run --main Test.Main
countWords
  ✓︎ counts every word, sorted

Summary
1/1 test passed
```

A failing spec exits with 1. Tests are just another program, so they run with `googoo run`:
`googoo test` and `googoo build` still go the JavaScript way, and a project with Go-only packages
fails there with `MissingFFIModule`.

### Build a binary

```
$ googoo go
/home/you/words/.spago/go/words/bin/words
$ .spago/go/words/bin/words to be
be: 1
to: 1
```

One file, no runtime to install next to it. Want the Go source instead? `googoo go out` writes it
to `out/`, see [Running a program](documentation/go-output.md#running-a-program).

### Calling Go

Put a `.go` file next to your `.purs` file:

```purescript
module Shout where

foreign import shout :: String -> Int -> String
```

```go
package ffi

import "strings"

func Shout(text string, times int) string {
	return strings.ToUpper(text) + strings.Repeat("!", times)
}
```

`log (shout "moin" 3)` prints `MOIN!!!`. Each foreign import is the Go function with its name
capitalised, taking all its arguments at once. `Int` is `int`, `Number` is `float64`, `Array a` is
`[]A`, and an `Effect` is a function you just call. [Foreign imports](documentation/go-output.md#foreign-imports)
has the whole table, records as Go structs, callbacks from goroutines and `//go:embed`.

### Different from JavaScript

Your program does what PureScript says on both backends. Where JavaScript only does something by
accident, Go does the natural thing:

| | Go |
| --- | --- |
| **`Number`** | can differ in the last digits: Go fuses `a * b + c` into one rounding, uses its own `sin`, `exp` and `pow`, and may sum arrays in SIMD lanes. Compare floats with a tolerance. |
| **`Int`** | is 64 bits. `top` is `9223372036854775807`, and hashes that count on 32-bit wrapping come out different. |
| **An uncaught exception** | is a Go panic with a trace into your `.purs` files, and exits with 2, not 1. |
| **Pure code** | can move past effects to where it's needed, so a `let` between two clocks times nothing. |
| **Deep recursion** | goes much further before it fails, and then can't be caught. |
| **Regex, `localeCompare`, error messages** | match JavaScript almost everywhere, with a few documented edge cases. |
| **Some programs** | don't compile: certain polymorphic recursion, `unsafeCoerce` between types Go stores differently, and importing the module that has `main`. |

All of it, with examples: [Go output: differences from the JavaScript backend](documentation/go-output.md).

### Hot loops

Write the plain PureScript first. googoo already turns a `Data.Map` that only your loop holds into
a Go map, and an `Array.index` it can see is in range into a plain slice read. Reach for something
else when it can't:

- **[Go.Map](https://github.com/i-am-the-slime/purescript-go#packages)** (`go-map`) for a map that
  lives on, say in a `Ref` your program keeps updating. A `Data.Map` there stays a balanced tree, a
  `GoMap` is Go's map, read and written in `Effect`, with `Int`, `String`, `Char` or `Number` keys.
- **[arrays-indexed](https://github.com/rowtype-yoga/purescript-arrays-indexed)** for index walks,
  like two pointers moving in from both ends. `at` takes an index that's in range by its type, so
  there's no `Maybe` to unwrap and no `fromMaybe 0` hiding a bug. It's in the registry, not yet in
  the Go set: add `arrays-indexed: 0.3.0` under `workspace.extraPackages`.
- **`ST` arrays** for updates in place, see [Loops, arrays and memory](documentation/go/loops.md).

## Learn more

- [Go output](documentation/go-output.md): running programs, foreign imports in Go, how a Go build
  differs from a JavaScript one, and the programs the Go backend rejects.
- [What your PureScript becomes in Go](documentation/go/index.md): the Go googoo writes, by example.
- [PureScript and Go side by side](https://i-am-the-slime.github.io/iris-go-backend/): the examples
  and benchmarks next to the Go they compile to, with timings against hand-written Go.
- [Effect, Aff and IO](documentation/go/effects.md): which one to use when, and how to share state
  between threads.

## Libraries

- [purescript-go](https://github.com/i-am-the-slime/purescript-go): Go's standard library for
  PureScript. Files, programs, HTTP, time, Go's maps, and `Go.IO` for threads.
- [Go package set](https://github.com/rowtype-yoga/purescript-go-package-sets): purescript-go, gRPC,
  HTTP, Postgres, terminal UIs and the registry packages that work on Go, at versions that build
  together.
- [iris-go](https://github.com/i-am-the-slime/iris-go): the runtime every Go build uses, with Go
  versions of the core libraries and a few popular ones.

---

<h1 align="center"><a href="https://iris-lang.com"><img src=".github/assets/iris-readme-banner.webp" alt="Iris" width="1200"></a></h1>

> [!NOTE]
> We are in the process of updating documentation across the Iris project.

---

Iris is an implementation of the PureScript programming language. See the [website](https://iris-lang.com) for more information.

Here are some links to get started:

- [Getting started](https://iris-lang.com/docs/getting-started): install Iris and run your first application.
- [Installation](https://iris-lang.com/docs/installation): installer options, release verification, canary builds, and packaging.
- [Language server](https://iris-lang.com/docs/language-server): set up Visual Studio Code or another editor, configure diagnostics, and understand workspace preparation.
- [Formatting](https://iris-lang.com/docs/formatting): format sources with `iris format` or from your editor.
