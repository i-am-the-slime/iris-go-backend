# Go backend

Read the repository's root `AGENTS.md` first. This file adds the rules that are specific to the Go
backend. They exist because the cheapest way to make a failing program compile is almost always a
shortcut, and a shortcut taken once becomes the pattern for every later fix.

## What generated Go must look like

The backend specialises the whole program from the checker's exact types. Generated Go should read
as if a careful person had written it by hand for those types.

- Real Go types everywhere. `any` and type assertions are reserved for polymorphic recursion whose
  types genuinely grow without bound. Every other source of erasure is a backend bug.
  - Rank-N quantified values (`Scene`, CPS parsers' answer types, and similar) are specialised per
    instantiation, not erased.
  - Recursive newtypes and data types become recursive named Go types.
- Effects are direct. `a -> Effect b` is `func(A) B`, a do-block is a sequence of statements, and a
  thunk exists only where an effect is genuinely first-class.
- PureScript `Int` is `int32` and wraps like JS. Conversions to Go's `int` happen only at Go API
  boundaries.
- No `reflect` and no `unsafe` in generated code.
- Calls read like the PureScript they come from: `n(f, x)`, never `n.Apply(f, x)`, `Invoke`,
  `Call2` or similar plumbing names.
- Programs keep PureScript's semantics: the same output as the JS backend for everything
  PureScript defines, such as `show`, String's UTF-16 code units and Int's 32-bit wrapping.
  JavaScript and engine accidents are not copied: float results may differ in the last digits
  (Go's math, fused multiply-add), and an Int result JS leaves outside 32 bits wraps. Each such
  difference is listed in documentation/go-output.md.

## Gates

Work is done when every gate passes. A passing gate that was weakened to pass does not count.

- `compiler-backend/go/scripts/run-examples.sh` runs every example, compares its output with JS, and
  then checks generated-Go quality with `scripts/quality.sh`.
- `compiler-backend/go/scripts/markgraf/run.sh` checks that the compactor's output equals JS.
- `just integration` runs the snapshot tests.

`quality-baseline.txt` holds the number of escape hatches (`any` and its causes, type assertions,
`reflect`, `unsafe`, `panic`) in each scope. It is a ratchet:

- A rise fails the gate. Fix the cause; do not raise the number.
- When one drops, lower the baseline with `quality.sh --update` in the same change.
- Raising one is a hand edit in a change whose description explains why no typed solution exists.

Size and readability numbers (lines, functions, nesting) are printed for information only.

## Shortcuts that are not allowed

- Erasing a type to `any` to get past a Go type error.
- Generic runtime helpers over `any` where a specialised, typed function can be emitted.
- Special-casing a function, module or type by name to make one program build. The one exception
  is `primitives::known`, a small table of primitives of very stable libraries (`Data.Exists`)
  whose meaning the backend implements in general, approved by the maintainer.
- Stubbing a foreign or emitting `panic("not implemented")` for code the target program reaches.
- Weakening a test: removing an edge case, loosening a comparison, excluding an example, or
  accepting a regenerated snapshot without reading the diff.
- Silent fallbacks. Every degraded code path reports a diagnostic with its reason, so that the
  erasure census accounts for every `any` that remains.

When the correct fix is out of scope or needs a design decision, stop and report it. Do not ship
the shortcut and mention it afterwards.

## Reporting

Say what changed, the gate results, and anything left undone.
