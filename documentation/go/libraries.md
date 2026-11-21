# Int64, Aff, JSON and foreign code

## `Int64` and `UInt64` are Go's 64-bit integers

```purescript
factorial :: Int64 -> Int64
factorial n = if n <= one then one else n * factorial (n - one)

main :: Effect Unit
main = do
  argv <- args
  let n = Int64.fromInt (20 + length argv)
  log (show (factorial n))
  log (show (Int64.toUnsigned (negate one) `div` (one + one)))
```

```go
func main() {
	argv := os.Args()
	console.Print(strconv.FormatInt(factorial(int64(20+int32(len(argv)))), 10) + "l")
	long := uint64(2)
	var result uint64
	if long == 0 {
		result = uint64(0)
	} else {
		result = Data_Int64_Internal_ffi.Divide_(uint64(18446744073709551615), long)
	}
	console.Print(strconv.FormatUint(result, 10) + "ul")
}

func factorial(n int64) int64 {
	if n <= 1 {
		return int64(1)
	}
	return n * factorial(n-1)
}
```

```
2432902008176640000l
9223372036854775807ul
```

`Int64` from the `int64` package is an `int64` and `UInt64` a `uint64`, so `+`, `*`, `<=` and
`one` are Go's own arithmetic and constants. No boxing, no pairs of 32-bit halves.

PureScript has no literal syntax beyond 32-bit `Int`, but type-level `Int`s can be as big as you
like, so they're how you write a 64-bit number at compile time: `Prim.Int`'s `ToString`,
`Compare`, `Add` and `Mul` all work on them. Iris keeps them as 128-bit numbers. That's every
`Int64` and `UInt64` with room to spare, but not unlimited like `purs`. A literal, sum or product
past 128 bits is a `TypeIntegerTooLarge` error. Reflecting a type-level `Int` that doesn't fit in
a 32-bit `Int` with `reflectType` is a `ReflectedIntegerOutOfRange` error.

## `Aff` runs on fibers

```purescript
main :: Effect Unit
main = launchAff_ do
  fiber <- forkAff do
    delay (Milliseconds 100.0)
    log "background done"
    pure 42
  log "main keeps going"
  answer <- joinFiber fiber
  log ("joined: " <> show answer)
```

```go
func main() {
	defer aff.Await()
	fiber4 := aff.NewFiber(func() struct{} {
		func() {
			fiber2 := aff.ForkFiber(true, func() int32 {
				aff.DelayDirect(nil, 100.0)
				console.Print("background done")
				return 42
			})
			isSuspended, join, kill, onComplete, run := aff.FiberFields(fiber2, func(payload exception.Error) either.EitherErrorInt {
				return either.EitherErrorInt{Tag: either.EitherErrorIntLeft, Left: payload}
			}, func(payload int32) either.EitherErrorInt {
				return either.EitherErrorInt{Tag: either.EitherErrorIntRight, Right: payload}
			}, either.EitherErrorUnit{Tag: either.EitherErrorUnitRight, Right: struct{}{}}, func(value either.OnCompleteInt) func(func(either.EitherErrorInt)) {
				return value.Handler
			})
			fiber3 := either.FiberInt{IsSuspended: isSuspended, Join: join, Kill: kill, OnComplete: onComplete, Run: run}
			console.Print("main keeps going")
			answer := aff.MakeAffDirect(func(value either.EitherErrorInt) bool {
				return value.Tag == either.EitherErrorIntLeft
			}, func(value either.EitherErrorInt) exception.Error {
				return value.Left
			}, func(value either.EitherErrorInt) int32 {
				return value.Right
			}, func(k func(either.EitherErrorInt)) func(exception.Error) {
				effect := fiber3.Join(k)
				return func(_ exception.Error) {
					effect()
				}
			})
			console.Print("joined: " + strconv.Itoa(int(answer)))
		}()
		return struct{}{}
	})
	isSuspended2, join2, kill2, onComplete2, run2 := aff.FiberFields(fiber4, func(payload exception.Error) either.EitherErrorUnit {
		return either.EitherErrorUnit{Tag: either.EitherErrorUnitLeft, Left: payload}
	}, func(payload struct{}) either.EitherErrorUnit {
		return either.EitherErrorUnit{Tag: either.EitherErrorUnitRight, Right: payload}
	}, either.EitherErrorUnit{Tag: either.EitherErrorUnitRight, Right: struct{}{}}, func(value either.OnCompleteUnit) func(func(either.EitherErrorUnit)) {
		return value.Handler
	})
	fiber := either.FiberUnit{IsSuspended: isSuspended2, Join: join2, Kill: kill2, OnComplete: onComplete2, Run: run2}
	fiber.Run()
}
```

```
main keeps going
background done
joined: 42
```

The body of an `Aff` is straight-line Go, like an `Effect`: `delay` blocks the fiber and the next
statement runs when it's done. There's no callback chain. The fibers themselves are values with a
field for each thing you can do with one (join, kill, …), and `main` waits for every fiber
before the program exits.

Each fiber is a goroutine, but they take turns, as they do in JavaScript: only one runs PureScript
code at a time, so a `Ref` shared between fibers needs no locking.

## `Go.IO` runs on threads

For real parallelism, [purescript-golang](https://github.com/i-am-the-slime/purescript-golang)'s
`Go.IO` is Haskell's `IO`: its actions run on goroutines.

```purescript
main :: Effect Unit
main = launchAff_ do
  toAff do
    concurrently_
      (threadDelay (Milliseconds 50.0) *> log "slow")
      (log "fast")
  log "both done"
```

```
fast
slow
both done
```

`concurrently_` starts each action on its own goroutine and waits for both. `toAff` waits for the
whole `IO` without blocking the other fibers. `Go.IO` also has `forkIO`, `MVar`, `Chan` and the
rest of `Async`.

## JSON with `yoga-json` gets a decoder for your type

```purescript
type Todo = { title :: String, done :: Boolean, tags :: Array String }

main :: Effect Unit
main = do
  case readJSON """{ "title": "write docs", "done": false, "tags": ["iris"] }""" of
    Left errors -> log ("bad JSON: " <> show errors)
    Right (todo :: Todo) -> log (writeJSON todo { done = true })
```

```go
func main() {
	decoded, ok := foreignvalue.Decode("{ \"title\": \"write docs\", \"done\": false, \"tags\": [\"iris\"] }", shared.DecodeJSONTodo)
	var read foreign.EitherNonEmptyListForeignErrorTodo
	if ok {
		read = foreign.EitherNonEmptyListForeignErrorTodo{Tag: foreign.EitherNonEmptyListForeignErrorTodoRight, Right: decoded}
	} else {
```

```go
	default: // foreign.EitherNonEmptyListForeignErrorTodoRight
		updated := read.Right
		updated.Done = true
		console.Print(foreignvalue.Encode(shared.EncodeJSONTodo, updated))
	}
}
```

```go
func DecodeJSONTodo(d *foreignvalue.Decoder) Todo {
	var done bool
	hasDone := false
	var tags []string
	hasTags := false
	var title string
	hasTitle := false
	if d.Object() {
		for {
			switch d.Key() {
			case "done":
				done = d.Boolean()
				hasDone = true
			case "tags":
				tags = DecodeJSONArrayString(d)
				hasTags = true
			case "title":
				title = d.String()
				hasTitle = true
			default:
				d.Skip()
			}
			if !d.MoreMembers() {
				break
			}
		}
	}
	if !hasDone || !hasTags || !hasTitle {
		d.Fail()
	}
	return Todo{Done: done, Tags: tags, Title: title}
}

func EncodeJSONTodo(e *foreignvalue.Encoder, value Todo) {
	e.Raw("{\"title\":")
	e.String(value.Title)
	e.Raw(",\"tags\":")
	EncodeJSONArrayString(e, value.Tags)
	e.Raw(",\"done\":")
	e.Boolean(value.Done)
	e.Raw("}")
}
```

```
{"title":"write docs","tags":["iris"],"done":true}
```

`readJSON` at a record type reads the text straight into the `Todo` struct, and `writeJSON` writes
the struct straight out. Neither goes through a generic JSON value. When the input doesn't fit,
the decoder gives up, and `readJSON` reads it again the way `yoga-json` does in JavaScript, to
give you the same errors. That part, left out above, is the long `else` branch.

### Labels that clash in Go

JSON keys aren't always nice PureScript names. Here `"A"` and `a` would both be `A` in Go, and
`"content-type"` can't be a Go name at all:

```purescript
type Request = { "A" :: Int, a :: String, "content-type" :: String }

main :: Effect Unit
main = do
  case readJSON """{ "A": 1, "a": "one", "content-type": "text/plain" }""" of
    Left errors -> log ("bad JSON: " <> show errors)
    Right (request :: Request) -> do
      log (request.a <> " " <> show request."A" <> " " <> request."content-type")
      log (writeJSON request { "A" = 2 })
```

```go
type Request struct {
	A            string
	Content_type string `purescript:"content-type"`
	A_           int32  `purescript:"A"`
}

func EncodeJSONRequest(e *foreignvalue.Encoder, value Request) {
	e.Raw("{\"content-type\":")
	e.String(value.Content_type)
	e.Raw(",\"a\":")
	e.String(value.A)
	e.Raw(",\"A\":")
	e.Int(value.A_)
	e.Raw("}")
}
```

```
one 1 text/plain
{"content-type":"text/plain","a":"one","A":2}
```

The lower-case `a` gets the plain `A`, and `"A"` gets out of its way as `A_`. Every field whose name
isn't just its label with a capital first letter carries the label as a tag, so you can tell what
it was when you write Go against it. The JSON keys stay the labels, whatever the fields are called.

## Foreign code is Go next to your module

```purescript
module Ex.Greeting where

import Effect (Effect)

foreign import data Stopwatch :: Type

foreign import greeting :: String
foreign import start :: Effect Stopwatch
foreign import elapsed :: Stopwatch -> Effect Number
foreign import repeat :: forall a. Int -> a -> Array a
foreign import none :: forall a. Array a
```

`src/Ex/Greeting.go`, next to `src/Ex/greeting.txt`:

```go
package ffi

import (
	_ "embed"
	"time"
)

//go:embed greeting.txt
var Greeting string

type Stopwatch struct{ started time.Time }

func Start() Stopwatch { return Stopwatch{started: time.Now()} }

func Elapsed(stopwatch Stopwatch) float64 {
	return float64(time.Since(stopwatch.started).Microseconds()) / 1000
}

func Repeat[A any](n int32, x A) []A {
	xs := make([]A, n)
	for i := range xs {
		xs[i] = x
	}
	return xs
}

func None[A any]() []A { return nil }
```

```purescript
main :: Effect Unit
main = do
  watch <- start
  log greeting
  log (show (repeat 3 "hi"))
  log (show (length (none :: Array Int)))
  ms <- elapsed watch
  log (if ms < 1000.0 then "fast" else "slow")
```

```go
func main() {
	watch := Ex_Greeting_ffi.Start()
	console.Print(Ex_Greeting_ffi.Greeting)
	console.Print(string(show.AppendShowArrayString(nil, Ex_Greeting_ffi.Repeat(3, "hi"))))
	console.Print(strconv.Itoa(len(Ex_Greeting_ffi.None[int32]())))
	number := Ex_Greeting_ffi.Elapsed(watch)
	var result string
	if number < 1000.0 {
		result = "fast"
	} else {
		result = "slow"
	}
	console.Print(result)
}
```

Your foreign imports are called like any Go function, with all their arguments at once. A value
such as `greeting :: String` is a Go variable, and the `//go:embed` file ends up inside your
binary. A polymorphic function is a generic Go function, called at the type you use it with:
`Repeat(…, "hi")` lets Go infer `string`. Go has no generic variables, so a polymorphic value like
`none :: forall a. Array a` is a generic function without arguments, `None[int32]()`.

[Foreign imports](../go-output.md#foreign-imports) has the full rules: types, effects, callbacks,
records and libraries.
