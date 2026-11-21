# What your PureScript becomes in Go

These pages show, by example, the Go that Iris writes for your PureScript. Each example is a small
program next to the Go it compiles to, trimmed to the lines that correspond to it: imports,
start-up plumbing and the `//line` comments that point stack traces at your PureScript are left
out, nothing is rewritten.

1. [The basics](basics.md): `Int`, `Number`, `String`, functions and currying, records, data types
   and `case`, newtypes, `Maybe` and `Either`, type classes, polymorphic functions, closures,
   arrays, recursion, `let` and `where`, `Effect` and `Ref`.
2. [Loops, arrays and memory](loops.md): pipelines that fuse into one loop, accumulators and trees
   updated in place, record accumulators split into variables, SIMD kernels, `ST` arrays.
3. [What compiles away](compiled-away.md): `$` and `#`, lenses, and `let`s that only some branches
   need.
4. [Int64, Aff, JSON and foreign code](libraries.md): 64-bit integers, fibers and threads,
   `yoga-json`, and Go files next to your modules.

## See it for yourself

```bash
mkdir out
printf 'module example.com/app\n\ngo 1.27.0\n' > out/go.mod
iris go --entry Main.main out
```

That writes your program to `out/main.go`, with packages for your modules' foreign code and for the
types several modules share. To build and run your program in one step, use `iris run --go`.

How a Go build behaves differently from a JavaScript one, and which programs it can't compile yet,
is in [Go output: differences from the JavaScript backend](../go-output.md).
