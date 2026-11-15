// Dhall sources that compare.ts parses with both parsers.

const hash = "sha256:" + "0123456789abcdef".repeat(4);

export const cases: string[] = [
  // Compat.Dhall.Parse's sources.
  "let double = \\(n : Natural) -> n * 2 in double 21",
  '{ name = "dhall", version = 3 }.version',
  "Natural/fold 5 Natural (\\(x : Natural) -> x + 3) 0",
  "merge { Left = \\(n : Natural) -> n + 1, Right = \\(b : Bool) -> 0 } (< Left : Natural | Right : Bool >.Left 7)",
  "List/length Natural ([1, 2] # [3])",
  'let Person = { name : Text, age : Natural } let people : List Person = [ { name = "ann", age = 30 }, { name = "bob", age = 41 } ] in List/fold Person people Natural (\\(p : Person) -> \\(total : Natural) -> p.age + total) 0',
  "\\(a : Type) -> \\(x : a) -> x",
  "1 + True",
  "{ unclosed = ",

  // Text: interpolation, escapes, Unicode, multi-line literals.
  '"Hello, ${name}!"',
  '"a${"b${"c"}d"}e"',
  '"\\${not interpolated} costs $5 $"',
  '"\\"\\\\\\/\\b\\f\\n\\r\\t"',
  '"\\u00E9\\u{1F600}\\u{0000041}\\u{10FFFD}\\uFFFD"',
  '"héllo 日本 😀 \u{10FFFD}"',
  "''\n    first\n      second\n    ${x}\n    ''",
  "''\n\tone\n\ttwo ''",
  "''\n  a ''' b ''${c} d $''",
  "''\nno indent\n  more\n''",
  '"" ++ ""',

  // Records and unions.
  "{ a = 1, b.c.d = 2, a = 3 }",
  "{ x, y, `quoted label` = 1, Some = 2 }",
  "{=}",
  "{ , a : Natural, b : Bool }",
  "{}",
  "< A | B : Natural | C >",
  "< >",
  "< | A | B : Bool | >",
  "r.{ a, b }",
  "r.{}",
  "r.(T)",
  "r.x.y.`z`",
  "T::{ a = 1 }",
  "r with a.b = 1 with c = 2",
  "r with Some = 1",
  "{ a = 1 } /\\ { b = 2 } // { c = 3 } //\\\\ { d : Natural }",
  "{ a = 1 } ∧ { b = 2 } ⫽ { c = 3 } ⩓ { d : Natural }",

  // Bindings and functions.
  "let x : Natural = 1 let y = 2 in x + y",
  "let x = 1 in let y = x in y",
  "λ(x : Natural) → x",
  "∀(a : Type) → a",
  "forall (x : Type) -> x",
  "forall (x : a) -> b",
  "Natural -> Bool -> Text",
  "\\(`a b` : Type) -> `a b`",

  // Numbers and variables.
  "[0, 0x1F, 0xff, 12345678901234567890]",
  "[+5, -0x10, -0, +0]",
  "[1.5, -2.5e10, 1e5, 1.0e-7, 0.1, 1.7976931348623157e308]",
  "6.02E23",
  "1e400",
  "[Infinity, -Infinity, NaN]",
  "x@2",
  "x@0x10",
  "x @ 3",
  "x@99999999999",

  // Temporal literals.
  "2020-01-31",
  "2020-02-30",
  "12:30:45.123456789",
  "12:30:45",
  "2020-01-31T12:30:45Z",
  "2020-01-31t12:30:45.5z",
  "2020-01-31T12:30:45+05:30",
  "+05:30",
  "00:00:00-08:00",

  // Imports.
  "./foo/bar.dhall",
  "../baz",
  "~/home/file",
  "/absolute/path",
  './"quoted dir"/file',
  "env:HOME",
  'env:"FOO BAR\\n"',
  "env:Natural",
  "https://example.com/a/b.dhall",
  "https://example.com",
  "https://user:pw@example.com:8080/x/y?a=1&b=2 using ./headers.dhall",
  "http://[::1]/x",
  "http://192.168.0.1/",
  "missing",
  `./a ${hash}`,
  "./a as Text",
  "./a as Location",
  "./a ? ./b ? missing",
  `https://prelude.dhall-lang.org/v20.0.0/package.dhall ${hash}`,

  // Operators, keywords and builtins.
  "a || b && c == d != e + f * g ++ h # i // j /\\ k === m ? n",
  "a//b",
  "merge x y : T",
  "merge x y",
  "toMap r",
  "toMap r : T",
  "Some 1",
  "None Natural",
  "assert : 1 + 1 === 2",
  "assert : a ≡ b",
  "if True then 1 else 2",
  "[] : List Natural",
  "[ , ] : List Natural",
  "[1, 2, 3]",
  "[ , 1, 2, ]",
  "x : T",
  "Natural/fold Natural/build Natural/isZero Natural/even Natural/odd Natural/toInteger Natural/show Natural/subtract",
  "Integer/show Integer/toDouble Integer/negate Integer/clamp Double/show Text/show Text/replace",
  "List/build List/fold List/length List/head List/last List/indexed List/reverse",
  "[Type, Kind, Sort, Bool, True, False, Natural, Integer, Double, Text, List, Date, Time, TimeZone, Optional, None]",
  "Optional/fold",

  // Whitespace and comments.
  "-- a comment\n1",
  "{- nested {- block -} comment -} 1 -- trailing",
  "#!/usr/bin/env dhall\n1",
  "  \t\r\n  1  \r\n",
  "1 -- no newline",

  // Spago configuration in the style of spago.dhall and packages.dhall.
  `let upstream =
      https://github.com/purescript/package-sets/releases/download/psc-0.15.4-20220829/packages.dhall
        ${hash}

let overrides = { metadata = upstream.metadata // { version = "v0.15.4" } }

let additions =
      { react-basic-hooks =
        { dependencies = [ "aff", "aff-promise", "console" ]
        , repo = "https://github.com/megamaddu/purescript-react-basic-hooks.git"
        , version = "v8.0.0"
        }
      }

in  upstream // overrides // additions`,
  `let conf = ./spago.dhall

in      conf
    //  { sources = conf.sources # [ "test/**/*.purs" ]
        , dependencies = conf.dependencies # [ "spec", "spec-discovery" ]
        }`,

  // Inputs that do not parse.
  "",
  "   ",
  "1 +",
  "let in",
  '"unterminated',
  "if",
  "{ a = 1, }}",
  "\\(x : ) -> x",
];
