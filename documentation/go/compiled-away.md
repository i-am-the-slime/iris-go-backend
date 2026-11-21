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
	n := int32(len(argv))
	console.Print(prim.StringToUpper("count: " + strconv.Itoa(int(n))))
	step, count := array.RangeSteps(1, n+6)
	mapped := []int32{}
	for index := range count {
		i := 1 + int32(index)*step
		if prim.IntMod(i, 3) == 0 {
			mapped = append(mapped, i*10)
		}
	}
	console.Print(prim.ShowArray(show.Show, mapped))
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
	hero := shared.Player{Name: "Ada", Stats: shared.HpXp{Hp: 10 + int32(len(argv)), Xp: 0}, Items: []string{"sword", "map"}}
	x := hero.Stats
	healed := shared.Player{Name: hero.Name, Stats: shared.HpXp{Hp: x.Hp + 5, Xp: x.Xp}, Items: hero.Items}
	x2 := healed.Items
	var result []string
	if 0 < int32(len(x2)) {
		updateAt := direct.UpdateAt(func(payload []string) maybe.ArrayString {
			return maybe.JustArrayString(payload)
		}, maybe.NoArrayString, 0, "better sword", x2)
		switch updateAt.Tag {
		case maybe.TagNothing:
			result = x2
		default: // maybe.TagJust
			result = updateAt.Just
		}
	} else {
		result = x2
	}
	upgraded := shared.Player{Name: healed.Name, Stats: healed.Stats, Items: result}
	console.Print(strconv.Itoa(int(upgraded.Stats.Hp)))
	console.Print(prim.ShowArray(show.Show, upgraded.Items))
}
```

```
15
["better sword","map"]
```

The profunctors, the `Proxy`s and the composition are gone. `view hp` is `upgraded.Stats.Hp`,
`over hp` builds the updated record directly, and `set (ix 0)` is the same bounds test and
`updateAt` you'd get from `Data.Array.updateAt`.

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
	for _, i := range []int32{0, 50 + int32(len(argv)), 500} {
		var result either.EitherStringInt
		if i < 1 {
			result = either.EitherStringInt{Tag: either.EitherStringIntLeft, Left: "age must be between 1 and 100, got " + strconv.Itoa(int(i))}
		} else if i > 100 {
			result = either.EitherStringInt{Tag: either.EitherStringIntLeft, Left: "age must be between 1 and 100, got " + strconv.Itoa(int(i))}
		} else {
			result = either.EitherStringInt{Tag: either.EitherStringIntRight, Right: i}
		}
		switch result.Tag {
		case either.EitherStringIntLeft:
			console.Print(result.Left)
		default: // either.EitherStringIntRight
			console.Print("ok " + strconv.Itoa(int(result.Right)))
		}
	}
}
```

PureScript is strict, so you might expect `problem`, message and all, to be built every time. It
isn't: building it has no effect, so it's built in each branch that returns it, and the valid path
never formats a message.

This doesn't always happen yet. Calling `validate` through `either identity show` builds `problem`
up front:

```purescript
main :: Effect Unit
main = do
  argv <- args
  for_ [ 0, 50 + length argv, 500 ] \n -> do
    log (either identity show (validate "age" n))
    log (either identity show (validate "weight" (n * 2)))
```

```go
		problem := either.EitherStringInt{Tag: either.EitherStringIntLeft, Left: "age must be between 1 and 100, got " + strconv.Itoa(int(i))}
		var result2 either.EitherStringInt
		if i < 1 {
			result2 = problem
		} else if i > 100 {
			result2 = problem
		} else {
			result2 = either.EitherStringInt{Tag: either.EitherStringIntRight, Right: i}
		}
```
