# googoo — 'cause I don't want the world to see Go

googoo is a fork of [Iris](https://github.com/purefunctor/purescript-iris), the PureScript
compiler, that also compiles your program to Go. You get a single native binary that starts right
away, uses every core you've got and talks to Go libraries through foreign imports. Everything else
Iris does works as it does upstream, and upstream's README follows the Go part.

## Installing

You need Go 1.27 or later and [Spago](https://github.com/purescript/spago). Homebrew gets you all
three:

```bash
brew install spago i-am-the-slime/tap/googoo
```

Got Node already? `npm install -g spago` works too.

googoo used to be called `iris`. The `iris` command still works for now: it tells you it's called
googoo now and then runs googoo.

## Your first program

```bash
mkdir my-app && cd my-app
googoo new
googoo run --go
```

```
🍝
```

`googoo run --go` compiles your package to Go, builds it and runs it. The second run of an
unchanged program skips the build. `googoo go` builds the binary and prints where it put it.

There's no `googoo test --go` yet. Run your test suite like any other program:

```bash
googoo run --go --main Test.Main
```

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
  PureScript. Files, programs, HTTP, time, and `Go.IO` for threads.
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
