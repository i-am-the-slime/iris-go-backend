# Differential fuzzer for the Go backend

Generates random, well-typed PureScript programs, compiles each with Iris to JavaScript
(`iris build`, run with Bun) and to Go (`iris go`, `go build`), runs both, and reports every
program whose stdout or exit status differs, or that Iris or `go build` rejects.

## Usage

```sh
cd compiler-backend/go/fuzz
bun fuzz.ts gen --seed 7                                   # print the program for a seed
bun fuzz.ts run --seed-from 1 --count 500 --jobs 6         # a campaign; failures kept in results
bun fuzz.ts run --seed-from 1 --count 500 --features "st=3,-lists,-aff"
bun fuzz.ts minimise RESULTS/go-build-error/P105           # shrink a kept failure to minimal.purs
bun fuzz.ts report [--copy DIR]                            # group kept failures by signature
bun fuzz.ts recheck RESULTS/*/P*                           # run kept failures again with the current compiler
bun fuzz.ts attribute RESULTS/output-mismatch/P16          # purs's JavaScript as a third oracle
bun fuzz.ts features                                       # the feature names
```

A seed names a program: the same seed and features always generate the same source.

`--features` is a comma list. Bare names enable only those features; `+name`, `-name` and
`name=WEIGHT` adjust the defaults. Features: `prims`, `strings`, `surrogates` (lone surrogates,
off by default), `transcendental` (exp, log, trigonometry: Go's math package differs from
JavaScript in the last bit, off by default), `adts`, `records`,
`patterns`, `classes`, `hof`, `containers`, `lists`, `poly`, `lazy`, `recursion`, `effects`,
`exceptions`, `st`, `aff`.

Other flags: `--batch` (modules per `iris build`, default 8), `--statements` and `--depth`
(program size), `--work DIR` (project directories, reused between runs), `--results DIR`,
`--keep-ok`. Environment: `IRIS` (compiler binary, default `target/release/iris`), `GO_SUPPORT`
(purs-backend-go/go-support checkout), `FUZZ_RUN_TIMEOUT` (milliseconds per program run).

Classifications: `OK`, `DOCUMENTED DIFFERENCE` (outputs differ only by a documented platform
difference: a JavaScript Int result outside int32 such as `Int.rem x 0`, `div bottom (-1)` or
`Bits.zshr`, or a last-ulp result of the numeric library such as `Number.pow`), `OUTPUT
MISMATCH`, `EXIT MISMATCH`, `IRIS ERROR` (Go backend rejected
the program), `IRIS JS ERROR` (the JavaScript build failed for a reason other than the generated
module), `GO BUILD ERROR`, `GO PANIC`, `TIMEOUT JS`, `TIMEOUT GO`, `TIMEOUT BOTH`,
`JS STACK OVERFLOW` (Bun ran out of stack; Go finished), `GENERATOR ILL-TYPED` (the generated
module does not typecheck: a generator bug, counted separately).

Each kept failure directory holds the source, both outputs and logs, the generated Go, and after
`minimise` a `minimal.purs` with its `minimal.json` signature.
