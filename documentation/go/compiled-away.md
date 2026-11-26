# What compiles away

Some PureScript is there for you, not for the machine. This is what's left of it in Go.

## `$` and `#` cost nothing

```purescript
main :: Effect Unit
main = do
  argv <- args
  let n = length argv
  log $ toUpper $ "count: " <> show n
  1 .. (n + 6)
    # filter (\i -> i `mod` 3 == 0)
    # map (_ * 10)
    # show
    # log
```

```go
func main() {
	argv := os.Args()
	n := len(argv)
	console.Print(prim.StringToUpper("count: " + strconv.Itoa(n)))
	step, count := array.RangeSteps(1, n+6)
	mapped := []int{}
	for index := range count {
		i := 1 + index*step
		if i%3 == 0 {
			mapped = append(mapped, i*10)
		}
	}
	console.Print(show.ArrayInt(mapped))
}
```

`f $ x` and `x # f` are just `f(x)`. Write whichever reads better.

## Lenses are field accesses

```purescript
type Player = { name :: String, stats :: { hp :: Int, xp :: Int }, items :: Array String }

hp = prop (Proxy :: _ "stats") <<< prop (Proxy :: _ "hp")
firstItem = prop (Proxy :: _ "items") <<< ix 0

main :: Effect Unit
main = do
  argv <- args
  let hero = { name: "Ada", stats: { hp: 10 + length argv, xp: 0 }, items: [ "sword", "map" ] }
  let healed = over hp (_ + 5) hero
  let upgraded = set firstItem "better sword" healed
  log (show (view hp upgraded))
  log (show upgraded.items)
```

```go
func main() {
	argv := os.Args()
	x := []string{"sword", "map"}
	var upgradedItems []string
	updated := slices.Clone(x)
	updated[0] = "better sword"
	upgradedItems = updated
	console.Print(strconv.Itoa(len(argv) + 15))
	console.Print(show.ArrayString(upgradedItems))
}
```

```
15
["better sword","map"]
```

The profunctors, the `Proxy`s and the composition are gone, and so are the records: each lens is
the field it points at. `view hp` after `over hp (_ + 5)` is just `len(argv) + 15`, and
`set firstItem` on an array that's known to have two elements copies it and assigns, with no bounds
test left.

## Pure `let`s move into the branches that use them

```purescript
validate :: String -> Int -> Either String Int
validate field n = do
  let problem = Left (field <> " must be between 1 and 100, got " <> show n)
  if n < 1 then problem
  else if n > 100 then problem
  else Right n

main :: Effect Unit
main = do
  argv <- args
  for_ [ 0, 50 + length argv, 500 ] \n -> case validate "age" n of
    Left err -> log err
    Right ok -> log ("ok " <> show ok)
```

```go
func main() {
	argv := os.Args()
	for _, i := range []int{0, 50 + len(argv), 500} {
		if i < 1 || i > 100 {
			console.Print("age must be between 1 and 100, got " + strconv.Itoa(i))
		} else {
			console.Print("ok " + strconv.Itoa(i))
		}
	}
}
```

PureScript is strict, so you might expect `problem`, message and all, to be built every time. It
isn't: building it has no effect, so it's only built on the paths that return it. Here the `case`
takes the `Either` apart right away, so it never exists at all. The two bad branches are one `if`,
and the valid path never formats a message.

The same goes when you call `validate` through `either identity show`:

```purescript
main :: Effect Unit
main = do
  argv <- args
  for_ [ 0, 50 + length argv, 500 ] \n -> do
    log (either identity show (validate "age" n))
    log (either identity show (validate "weight" (n * 2)))
```

```go
	for _, i := range []int{0, 50 + len(argv), 500} {
		var result string
		if i < 1 || i > 100 {
			result = "age must be between 1 and 100, got " + strconv.Itoa(i)
		} else {
			result = strconv.Itoa(i)
		}
		console.Print(result)
		n := i * 2
		var result2 string
		if n < 1 || n > 100 {
			result2 = "weight must be between 1 and 100, got " + strconv.Itoa(n)
		} else {
			result2 = strconv.Itoa(n)
		}
		console.Print(result2)
	}
```
