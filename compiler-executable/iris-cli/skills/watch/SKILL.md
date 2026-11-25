---
name: watch
description: Ask a running `googoo watch` about a PureScript project with `googoo watch query` for signatures, module exports, definitions, references, instances, dependent modules, name search, diagnostics, and generated JavaScript, addressed by qualified name. Use when working in a project built with Iris, after editing PureScript files, or instead of reading dependency sources to learn an API.
---

# Querying `googoo watch`

`googoo watch` keeps the whole project compiled in memory, dependencies included. `googoo watch query`
asks it questions by qualified name, so you do not need to open files or start a second compiler.

## Find the watcher

Run queries from anywhere inside the project. If the watcher was started with `--output DIR`, pass
the same option: append `query …` to the watcher's command line (`googoo watch --output DIR query
wait`), or run `googoo watch query --output DIR wait`. A relative `DIR` is resolved from the current
directory, so run the query from the directory the watcher was started in.

```bash
googoo watch query wait
```

- Exit status 4 means no watcher is running for the project's output directory. Before starting
  one, check whether the project already starts it: look at `package.json` scripts (a `dev` script
  may run `googoo watch` next to a dev server), `.amp/services.yaml`, and the project's agent guide.
  If a service runs it, start or restart that service instead. Otherwise run `googoo watch` in the
  background and keep it running; queries right after it starts exit 4 until Spago has fetched
  dependencies, so retry for a few seconds.
- Never stop or restart a watcher you did not start. Only one watcher can run per output directory.
- A warning that the watcher runs a different Iris version means the project uses another `iris`
  build, which the warning names; use that executable for queries if answers look wrong.

## After editing files

```bash
googoo watch query wait
googoo watch query diagnostics
```

`wait` rescans the sources, rebuilds if anything changed, and reports whether the build succeeded.
Always run it after writing files and before other queries, so answers reflect your edits. It exits
0 even when the build has errors; read its output, then ask for `diagnostics`.

## Queries

| Command | Answer |
|---|---|
| `googoo watch query wait` | Build outcome after picking up every change on disk |
| `googoo watch query signature Data.Maybe.fromMaybe` | Signature of a value, or kind of a type or class, with its documentation |
| `googoo watch query module Data.Maybe` | Every export of a module with signatures and documentation |
| `googoo watch query definition Data.Maybe.Maybe` | `path:line:column` of the declaration |
| `googoo watch query references Data.Maybe.fromMaybe` | `path:line:column` of every use |
| `googoo watch query dependents Data.Maybe` | Every module that imports a module; an indirect one names the module it imports on the way |
| `googoo watch query instances class Data.Show.Show` | `path:line:column` and head of every instance of a class |
| `googoo watch query instances type Data.Maybe.Maybe` | `path:line:column` and head of every instance whose head mentions a type, whatever its class |
| `googoo watch query search foldl` | Qualified names and signatures of declarations whose names match, best first |
| `googoo watch query diagnostics [Main]` | Errors and warnings of every module, or of one module |
| `googoo watch query javascript Main` | The JavaScript written to `output/` for a module |

- Use `search` when you do not know which module declares something; it matches whole names,
  then prefixes, then substrings, then letters in order (`fromMay` finds `fromMaybe`), ignoring
  case, and lists the best 50.
- Names are fully qualified: the module, a dot, then the item. Operators may be written with or
  without parentheses: `Data.Function.(<<<)`.
- A name that is both a type and a value, such as a constructor named after its type, answers both.
  To ask about one, put `value` or `type` before the name: `googoo watch query definition type
  Data.Maybe.Maybe`, `googoo watch query signature value Data.Tuple.Tuple`. This works for `signature`,
  `definition`, and `references`; classes are in the `type` namespace, and data constructors and
  class members in the `value` namespace.
- Any module in the project or its dependencies can be queried, including ones that are not
  imported anywhere.
- Declarations of the built-in `Prim` modules point at copies the watcher writes to a temporary
  directory, which you can read like any other source.
- Paths inside the project, dependencies included, are relative to its root; lines and columns
  count from 1, and columns count characters.
- `javascript` fails while any module has errors, because nothing is written to `output/` then.
- Each query invocation connects, receives its answer, and exits; there is no client session.
- `--json` prints the watcher's response as JSON: successful answers have `kind` and `value`;
  errors have `kind` and `message`. Locations in `value` are objects with `path`, `line`, and
  `column`.
- Exit status: 0 answered, 1 the query failed (the message says why, for example an unknown name),
  2 invalid arguments, 4 no watcher.

## Refactorings

`googoo watch refactor` runs type-aware code modifications against the running watcher. The watcher
rescans sources on disk, computes a structured edit plan over the latest snapshot, and the CLI
verifies file digests before writing edits back to disk.

| Command | Effect |
|---|---|
| `googoo watch refactor let-signatures [Main]` | Add explicit type signatures to strictly monomorphic `let`, `where`, and multi-line `do`/`ado` `let` bindings across project modules (or one named module), auto-importing missing types as needed |

- Writes modified files by default and prints a summary of signatures added, imports added or
  updated, and skipped bindings or modules.
- `--preview` skips writing files, prints a unified diff (`.patch`) to stdout, and prints any
  skipped bindings or modules to stderr so stdout stays valid patch output.
- `--json` prints the raw watcher response JSON envelope (`kind` and `value` or `message`);
  combine `--preview --json` to inspect the machine-readable edit plan without touching disk.
- Only editable workspace and local project files are modified; fetched dependencies (`.spago/p/`
  and git checkouts) and `Prim` are excluded and refused when named explicitly. Modules with
  parse, indexing, resolving, lowering, cycle, checking, foreign, or codegen errors are skipped;
  naming an errored module explicitly exits with status 1.
- After applying edits, run `googoo watch query wait` and `googoo watch query diagnostics` to confirm
  the rebuild succeeded cleanly.

## MCP server

`googoo watch mcp` serves the same queries and refactorings as MCP tools over standard input and
output. Add it to the agent's MCP configuration; it finds the watcher the same way `googoo watch query`
does, so `googoo watch` must still be running:

```json
{ "mcpServers": { "iris": { "command": "iris", "args": ["watch", "mcp"] } } }
```

- Each query is a tool with the same name, such as `wait`, `signature`, and `references`.
  `googoo watch refactor let-signatures` is `refactor_let_signatures`, which writes files unless
  `preview` is set.
- Each result has the text `googoo watch query` prints and, as structured content, the same `value`
  that `--json` prints. Every tool declares an output schema for it. `refactor_let_signatures` also
  reports `written`, and `patch` when previewing.
- Add `"--output", "DIR"` to `args` when the watcher was started with `--output DIR`.
- Without a watcher, tools return an error rather than exit status 4. The server keeps running and
  finds a watcher that starts later.
