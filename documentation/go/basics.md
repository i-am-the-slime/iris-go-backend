# The basics

Each section shows a small PureScript program and the Go that `iris go` writes for it, trimmed to
the lines that matter.

## Constants are worked out before your program runs

```purescript
answer :: Int
answer = 42

ratio :: Number
ratio = 0.75

name :: String
name = "Iris"

main :: Effect Unit
main = do
  log (show (answer + 1))
  log (show (ratio * 2.0))
  log (name <> "!")
```

```go
func main() {
	console.Print("43")
	console.Print(prim.ShowNumber(1.5))
	console.Print("Iris!")
}
```

`answer`, `ratio` and `name` are gone, and so are `+`, `*` and `<>`: Iris did the sums, and
`show 43` is just `"43"`. Small functions get copied into the code that calls them, so whatever
depends only on constants ends up computed too.

That's why most examples on these pages start with `argv <- args` (from `Go.OS`) and use
`length argv`. The compiler can't know how many arguments you'll pass, so the code you want to look
at stays in the output.

## `Int`, `Number`, `String`, `Boolean` and `Char`

```purescript
main :: Effect Unit
main = do
  argv <- args
  let count = length argv
  let half = toNumber count / 2.0
  let word = "args: " <> show count
  let many = count > 1
  let first = fromMaybe '?' (charAt 0 word)
  log word
  log (show half)
  log (show many)
  log (show first)
```

```go
func main() {
	argv := os.Args()
	count := int32(len(argv))
	word := "args: " + strconv.Itoa(int(count))
	codeUnitCharAt := prim.CodeUnitCharAt(func(payload rune) maybe.Char {
		return maybe.Char(payload)
	}, maybe.NoChar, 0, word)
	var first rune
	if codeUnitCharAt == maybe.NoChar {
		first = '?'
	} else {
		first = rune(codeUnitCharAt)
	}
	console.Print(word)
	console.Print(prim.ShowNumber(float64(count) / 2.0))
	console.Print(strconv.FormatBool(count > 1))
	console.Print(prim.ShowChar(first))
}
```

| PureScript | Go |
| --- | --- |
| `Int` | `int32` |
| `Number` | `float64` |
| `String` | `string` |
| `Boolean` | `bool` |
| `Char` | `rune` |

A `let` that's used once is written where it's used, like `half` and `many` here. One that's used
more than once becomes a Go variable, like `word`, and so does an `if` or a `case`, like `first`.
Either way the Go variable keeps your name. `show` on an `Int` is `strconv.Itoa` and on a `Boolean`
`strconv.FormatBool`, straight from Go's standard library.

## Functions take all their arguments at once

```purescript
label :: String -> Int -> Number -> String
label unit amount price =
  if amount == 0 then "no " <> unit
  else if amount == 1 then "one " <> unit <> " for " <> show price
  else show amount <> " " <> unit <> "s for " <> show (price * 0.9)

main :: Effect Unit
main = do
  argv <- args
  let n = length argv
  log (label "apple" n 1.25)
  let pears = label "pear"
  log (pears (n + 1) 0.8)
  log (pears (n + 2) 0.8)
```

```go
func main() {
	argv := os.Args()
	n := int32(len(argv))
	var result string
	if n == 0 {
		result = "no apple"
	} else if n == 1 {
		result = "one apple for " + prim.ShowNumber(1.25)
	} else {
		result = strconv.Itoa(int(n)) + " apples for " + prim.ShowNumber(1.125)
	}
	console.Print(result)
	console.Print(mainPears(n+1, 0.8))
	console.Print(mainPears(n+2, 0.8))
}

func mainPears(amount int32, price float64) string {
	if amount == 0 {
		return "no pear"
	}
	if amount == 1 {
		return "one pear for " + prim.ShowNumber(price)
	}
	return strconv.Itoa(int(amount)) + " pears for " + prim.ShowNumber(price*0.9)
}
```

A curried PureScript function is a Go function with several parameters. You don't pay for
currying: the first call is written out in place, and the partial application `label "pear"`
becomes its own function, `mainPears`, with `"pear"` already filled in.

## Records are structs

```purescript
type Address = { street :: String, city :: String }
type Person = { name :: String, age :: Int, address :: Address }

birthday :: Person -> Person
birthday person = person { age = person.age + 1 }

moveTo :: String -> Person -> Person
moveTo city person = person { address { city = city } }

describe :: Person -> String
describe { name, age, address } = name <> " (" <> show age <> ") lives in " <> address.city

main :: Effect Unit
main = do
  argv <- args
  let ada = { name: "Ada", age: 36 + length argv, address: { street: "St James's Square", city: "London" } }
  log (describe ada)
  log (describe (moveTo "Paris" (birthday ada)))
```

```go
type Address struct {
	City   string
	Street string
}

type Person struct {
	Address Address
	Name    string
	Age     int32
}

func main() {
	argv := os.Args()
	ada := shared.Person{Name: "Ada", Age: 36 + int32(len(argv)), Address: shared.Address{Street: "St James's Square", City: "London"}}
	console.Print(ada.Name + " (" + strconv.Itoa(int(ada.Age)) + ") lives in " + ada.Address.City)
	ada.Age += 1
	ada.Address.City = "Paris"
	console.Print(ada.Name + " (" + strconv.Itoa(int(ada.Age)) + ") lives in " + ada.Address.City)
}
```

Every record type is a struct. It takes the name of its type synonym, and field names are the
labels with a capital first letter. A nested record is a nested struct, not a pointer. Nothing reads
the old `ada` after `birthday` and `moveTo`, so the updates change its fields where they are instead
of copying it.

A record type without a synonym gets a name made from its labels: `{ hp :: Int, xp :: Int }` is
`HpXp`.

## Data types are structs with a tag, and `case` is a `switch`

```purescript
data Shape
  = Circle Number
  | Rectangle Number Number
  | Dot

area :: Shape -> Number
area = case _ of
  Circle r -> 3.14159 * r * r
  Rectangle w h -> w * h
  Dot -> 0.0

main :: Effect Unit
main = do
  argv <- args
  let shapes = [ Circle 1.0, Rectangle 2.0 3.0, Dot ] <> replicate (length argv) Dot
  for_ shapes \shape -> log (show (area shape))
```

```go
type Shape struct {
	Circle     float64
	Rectangle0 float64
	Rectangle1 float64
	Tag        uint8
}

const (
	ShapeCircle = iota
	ShapeRectangle
	ShapeDot
)

func main() {
	argv := os.Args()
	for _, shape := range array.Append([]Shape{{Tag: ShapeCircle, Circle: 1.0}, {Tag: ShapeRectangle, Rectangle0: 2.0, Rectangle1: 3.0}, {Tag: ShapeDot}}, array.Replicate(int32(len(argv)), Shape{Tag: ShapeDot})) {
		var result float64
		switch shape.Tag {
		case ShapeCircle:
			r := shape.Circle
			result = 3.14159 * r * r
		case ShapeRectangle:
			result = shape.Rectangle0 * shape.Rectangle1
		default: // ShapeDot
			result = 0.0
		}
		console.Print(prim.ShowNumber(result))
	}
}
```

A data type is one struct with a field for each constructor argument and a `Tag` that says which
constructor it is. The struct is a plain value, so an array of shapes is one block of memory.

A data type whose constructors have no arguments is just a number:

```purescript
data Suit = Hearts | Spades
```

```go
type Suit uint8

const (
	SuitHearts Suit = iota
	SuitSpades
)
```

A recursive data type is a pointer, and its constructors without arguments are one shared value
that you compare against:

```purescript
data Tree = Leaf | Node Tree Int Tree

sum :: Tree -> Int
sum = case _ of
  Leaf -> 0
  Node left x right -> sum left + x + sum right
```

```go
type Tree struct {
	Node0 *Tree
	Node2 *Tree
	Node1 int32
}

var sharedTreeLeaf = &Tree{}

func sum(value *Tree) int32 {
	if value == sharedTreeLeaf {
		return 0
	}
	return sum(value.Node0) + value.Node1 + sum(value.Node2)
}
```

When a `case` looks at a value that was built right before it, the value is never built at all.
`case pick n of Circle r -> …`, where `pick` returns a `Circle` for `0`, becomes a `switch` on `n`.

## Newtypes disappear

```purescript
newtype Celsius = Celsius Number

type Reading = { city :: String, temperature :: Celsius }

toFahrenheit :: Celsius -> Number
toFahrenheit (Celsius c) = c * 9.0 / 5.0 + 32.0

main :: Effect Unit
main = do
  argv <- args
  let readings = map (\i -> { city: "City " <> show i, temperature: Celsius (toNumber i * 10.0) }) (1 .. (length argv + 2))
  log (show (map (\r -> toFahrenheit r.temperature) readings))
  log (show (length readings))
```

```go
type Reading struct {
	City        string
	Temperature float64
}

func main() {
	argv := os.Args()
	step, count := array.RangeSteps(1, int32(len(argv))+2)
	mapped := make([]shared.Reading, count)
	for index := range count {
		i := 1 + int32(index)*step
		mapped[index] = shared.Reading{City: "City " + strconv.Itoa(int(i)), Temperature: float64(i) * 10.0}
	}
	mapped2 := make([]float64, len(mapped))
	for index := range mapped {
		mapped2[index] = mapped[index].Temperature*9.0/5.0 + 32.0
	}
	console.Print(prim.ShowArray(show.Show, mapped2))
	console.Print(strconv.Itoa(len(mapped)))
}
```

A `Celsius` is a `float64`. Wrapping and unwrapping it costs nothing.

## `Maybe` and `Either`

```purescript
parse :: Int -> Either String Int
parse n = if n > 2 then Left ("too big: " <> show n) else Right (n * 10)

nickname :: Int -> Maybe String
nickname n = if n == 1 then Just "one" else Nothing

main :: Effect Unit
main = do
  argv <- args
  let numbers = 0 .. (length argv + 3)
  let parsed = map parse numbers
  let names = map nickname numbers
  for_ parsed case _ of
    Left err -> log err
    Right n -> log (show n)
  for_ names case _ of
    Nothing -> log "-"
    Just name -> log name
```

```go
type EitherStringInt struct {
	Left  string
	Right int32
	Tag   uint8
}

type String struct {
	Just string
	Tag  uint8
}

func main() {
	argv := os.Args()
	numbers := array.RangeInt32(0, int32(len(argv))+3)
	mapped := make([]either.EitherStringInt, len(numbers))
	for index, element := range numbers {
		mapped[index] = parse(element)
	}
	for eitherIndex := range mapped {
		switch mapped[eitherIndex].Tag {
		case either.EitherStringIntLeft:
			console.Print(mapped[eitherIndex].Left)
		default: // either.EitherStringIntRight
			console.Print(strconv.Itoa(int(mapped[eitherIndex].Right)))
		}
	}
	mapped2 := make([]maybe.String, len(numbers))
	for index, element := range numbers {
		mapped2[index] = nickname(element)
	}
	for maybeIndex := range mapped2 {
		switch mapped2[maybeIndex].Tag {
		case maybe.TagNothing:
			console.Print("-")
		default: // maybe.TagJust
			console.Print(mapped2[maybeIndex].Just)
		}
	}
}

func parse(n int32) either.EitherStringInt {
	if n > 2 {
		return either.EitherStringInt{Tag: either.EitherStringIntLeft, Left: "too big: " + strconv.Itoa(int(n))}
	}
	return either.EitherStringInt{Tag: either.EitherStringIntRight, Right: n * 10}
}

func nickname(n int32) maybe.String {
	if n == 1 {
		return maybe.JustString("one")
	}
	return maybe.NoString
}
```

`Maybe` and `Either` are data types like any other, with a struct for each type they hold:
`maybe.String` is a `Maybe String`, `either.EitherStringInt` an `Either String Int`.

A `Maybe Int` or a `Maybe Char` doesn't need a struct. It's a 64-bit number, and `Nothing` is a
value no `Int` can have:

```purescript
firstEven :: Array Int -> Maybe Int
firstEven = find \n -> n `mod` 2 == 0

main :: Effect Unit
main = do
  argv <- args
  let numbers = 0 .. (length argv + 2)
  case firstEven (map (_ + 1) numbers) of
    Nothing -> log "all odd"
    Just n -> log ("first even: " <> show n)
```

```go
package maybe

type Int int64

const NoInt Int = 1 << 32
```

```go
func main() {
	argv := os.Args()
	step, count := array.RangeSteps(0, int32(len(argv))+2)
	mapped := make([]int32, count)
	for index := range count {
		value := int32(index) * step
		mapped[index] = value + 1
	}
	found := maybe.NoInt
	for index, n := range mapped {
		if prim.IntMod(n, 2) == 0 {
			found = maybe.Int(int32(index))
			break
		}
	}
	if found != maybe.NoInt {
		console.Print("first even: " + strconv.Itoa(int(mapped[int32(found)])))
		return
	}
	console.Print("all odd")
}
```

## Type classes are resolved at compile time

```purescript
data Suit = Hearts | Spades

derive instance Eq Suit
derive instance Ord Suit

instance Show Suit where
  show Hearts = "♥"
  show Spades = "♠"

type Card = { rank :: Int, suit :: Suit }

showCard :: Card -> String
showCard { rank, suit } = show rank <> show suit

main :: Effect Unit
main = do
  argv <- args
  let n = length argv
  let cards = map (\i -> { rank: 10 - i, suit: if i `mod` 2 == 0 then Hearts else Spades }) (0 .. (n + 3))
  for_ (sort (map _.suit cards)) \suit -> log (show suit)
  log (show (map showCard cards))
  log (show (cards == cards))
```

```go
func main() {
	argv := os.Args()
	step, count := array.RangeSteps(0, int32(len(argv))+3)
	mapped := make([]Card, count)
	for index := range count {
		i := int32(index) * step
		var result Suit
		if prim.IntMod(i, 2) == 0 {
			result = SuitHearts
		} else {
			result = SuitSpades
		}
		mapped[index] = Card{Rank: 10 - i, Suit: result}
	}
	mapped2 := make([]Suit, len(mapped))
	for index := range mapped {
		mapped2[index] = mapped[index].Suit
	}
	for _, suit := range direct.SortBy(compare, func(value ordering.Ordering) int32 {
		switch value {
		case ordering.OrderingGT:
			return 1
		case ordering.OrderingEQ:
			return 0
		default: // ordering.OrderingLT
			return -1
		}
	}, mapped2) {
		var result string
		switch suit {
		case SuitHearts:
			result = "♥"
		default: // SuitSpades
			result = "♠"
		}
		console.Print(result)
	}
	mapped3 := make([]string, len(mapped))
	for index, element := range mapped {
		mapped3[index] = showCard(element)
	}
	console.Print(prim.ShowArray(show.Show, mapped3))
	console.Print(strconv.FormatBool(array.Eq(eqCardConsIntConsSuitNil, mapped, mapped)))
}

func showCard(card Card) string {
	var result string
	switch card.Suit {
	case SuitHearts:
		result = "♥"
	default: // SuitSpades
		result = "♠"
	}
	return strconv.Itoa(int(card.Rank)) + result
}

func compare(left Suit, right Suit) ordering.Ordering {
	if left == SuitHearts && right == SuitHearts {
		return ordering.OrderingEQ
	}
	if left == SuitHearts {
		return ordering.OrderingLT
	}
	if right == SuitHearts {
		return ordering.OrderingGT
	}
	return ordering.OrderingEQ
}

func eqCardConsIntConsSuitNil(ra Card, rb Card) bool {
	scrutinee := eqCardConsIntConsSuitNilGet2(ra)
	scrutinee2 := eqCardConsIntConsSuitNilGet2(rb)
	tail := scrutinee == SuitHearts && scrutinee2 == SuitHearts || scrutinee == SuitSpades && scrutinee2 == SuitSpades
	return eqCardConsIntConsSuitNilGet(ra) == eqCardConsIntConsSuitNilGet(rb) && tail
}

func eqCardConsIntConsSuitNilGet(card Card) int32 {
	return card.Rank
}

func eqCardConsIntConsSuitNilGet2(card Card) Suit {
	return card.Suit
}
```

```
♥
♥
♠
♠
["10♥","9♠","8♥","7♠"]
true
```

There are no dictionaries. Iris knows which instance each `show`, `compare` and `==` means, and
writes that instance's code where it's used: `show suit` is a `switch`, `show rank` is
`strconv.Itoa`, the derived `Ord Suit` is the function `compare`, and `==` on two arrays of cards
gets an equality function for `Card`.

## Polymorphic functions get one copy per type

```purescript
-- | Is `x` in the sorted array?
search :: forall a. Ord a => a -> Array a -> Boolean
search x xs = go 0 (length xs - 1)
  where
  go low high
    | low > high = false
    | otherwise = do
        let mid = (low + high) / 2
        let y = unsafePartial (unsafeIndex xs mid)
        case compare x y of
          EQ -> true
          LT -> go low (mid - 1)
          GT -> go (mid + 1) high

main :: Effect Unit
main = do
  argv <- args
  let ints = 1 .. (length argv + 5)
  let words = map (\i -> "w" <> show i) ints
  log (show (search 4 ints))
  log (show (search "w9" words))
```

```go
func main() {
	argv := os.Args()
	ints := array.RangeInt32(1, int32(len(argv))+5)
	mapped := make([]string, len(ints))
	for index, i := range ints {
		mapped[index] = "w" + strconv.Itoa(int(i))
	}
	console.Print(strconv.FormatBool(mainGo(ints, 0, int32(len(ints))-1)))
	console.Print(strconv.FormatBool(mainGo2(mapped, 0, int32(len(mapped))-1)))
}

func mainGo(ints []int32, low int32, high int32) bool {
	for {
		if low > high {
			return false
		}
		mid := prim.IntDiv(low+high, 2)
		y := ints[mid]
		if 4 < y {
			high = mid - 1
			continue
		}
		if 4 == y {
			return true
		}
		low = mid + 1
	}
}

func mainGo2(words []string, low int32, high int32) bool {
	for {
		if low > high {
			return false
		}
		mid := prim.IntDiv(low+high, 2)
		y := words[mid]
		if prim.CompareString("w9", y) < 0 {
			high = mid - 1
			continue
		}
		if "w9" == y {
			return true
		}
		low = mid + 1
	}
}
```

`search` is used at two types, so there are two Go functions: one for `[]int32` that compares with
`<`, and one for `[]string` that compares with `prim.CompareString`. The value you search for is
baked in too. `compare x y` returning `EQ`, `LT` or `GT` turned into two plain comparisons.

Strings compare by UTF-16 code units, as they do in JavaScript, which is why `String` uses
`prim.CompareString` rather than Go's `<`.

## Functions are values, and closures capture what they use

```purescript
type Rule = { name :: String, check :: Int -> Boolean }

rules :: Int -> Array Rule
rules limit =
  [ { name: "positive", check: \n -> n > 0 }
  , { name: "small", check: \n -> n < limit }
  , { name: "even", check: \n -> n `mod` 2 == 0 }
  ]

main :: Effect Unit
main = do
  argv <- args
  let limit = length argv + 3
  for_ (0 .. 4) \n ->
    for_ (rules limit) \rule ->
      when (rule.check n) do
        log (show n <> " is " <> rule.name)
```

```go
type Rule struct {
	Check func(int32) bool
	Name  string
}

func main() {
	argv := os.Args()
	limit := int32(len(argv)) + 3
	for i := int32(0); i < 5; i++ {
		for _, rule := range []shared.Rule{{Name: "positive", Check: func(n int32) bool {
			return n > 0
		}}, {Name: "small", Check: func(n int32) bool {
			return n < limit
		}}, {Name: "even", Check: func(n int32) bool {
			return prim.IntMod(n, 2) == 0
		}}} {
			if rule.Check(i) {
				console.Print(strconv.Itoa(int(i)) + " is " + rule.Name)
			}
		}
	}
}
```

An `Int -> Boolean` is a `func(int32) bool`, and a lambda is a Go function literal. `\n -> n < limit`
captures `limit` the way any Go closure does. A function you pass to `map`, `filter` or `for_` is
usually written straight into the loop instead, so it never exists as a value.

## Arrays are slices

```purescript
main :: Effect Unit
main = do
  argv <- args
  let scores = [ 70, 85, 92 ] <> (0 .. length argv)
  let more = snoc scores 100
  log (show (length more))
  log (show (reverse more))
  case more !! 1 of
    Just second -> log ("second: " <> show second)
    Nothing -> log "too short"
```

```go
func main() {
	argv := os.Args()
	more := array.Snoc(array.Append([]int32{70, 85, 92}, array.RangeInt32(0, int32(len(argv)))), int32(100))
	console.Print(strconv.Itoa(len(more)))
	console.Print(prim.ShowArray(show.Show, array.Reverse(more)))
	if 1 < int32(len(more)) {
		console.Print("second: " + strconv.Itoa(int(more[1])))
		return
	}
	console.Print("too short")
}
```

An `Array Int` is a `[]int32`, and `length` is `len`. `more !! 1` returns a `Maybe`, but matching
on it right away leaves only the bounds test and the index.

## Recursion, and tail recursion as a loop

```purescript
data Tree = Leaf | Node Tree Int Tree

insert :: Int -> Tree -> Tree
insert x = case _ of
  Leaf -> Node Leaf x Leaf
  node@(Node left y right)
    | x < y -> Node (insert x left) y right
    | x > y -> Node left y (insert x right)
    | otherwise -> node

countdown :: Int -> Int -> Int
countdown acc n = if n <= 0 then acc else countdown (acc + n) (n - 1)
```

```go
func insert(x int32, value *Tree) *Tree {
	if value == sharedTreeLeaf {
		return &Tree{Node0: sharedTreeLeaf, Node1: x, Node2: sharedTreeLeaf}
	}
	left := value.Node0
	y := value.Node1
	right := value.Node2
	if x < y {
		return &Tree{Node0: insert(x, left), Node1: y, Node2: right}
	}
	if x > y {
		return &Tree{Node0: left, Node1: y, Node2: insert(x, right)}
	}
	return value
}

func countdown(acc int32, n int32) int32 {
	for {
		if n <= 0 {
			return acc
		}
		acc, n = acc+n, n-1
	}
}
```

A recursive call is a Go call. A call in tail position is a loop that reassigns the parameters, so
`countdown` runs in constant stack space however big `n` is.

## `let` and `where`

```purescript
price :: Int -> Number -> String
price quantity unitPrice = do
  let subtotal = toNumber quantity * unitPrice
  let discount = if quantity >= bulk then subtotal * rate else 0.0
  format (subtotal - discount)
  where
  bulk = 10
  rate = 0.15
  format amount = "€" <> show amount

main :: Effect Unit
main = do
  argv <- args
  for_ [ 1, 10 + length argv, 20 ] \q -> log (price q 2.5)
```

```go
func main() {
	argv := os.Args()
	for _, quantity := range []int32{1, 10 + int32(len(argv)), 20} {
		subtotal := float64(quantity) * 2.5
		var discount float64
		if quantity >= 10 {
			discount = subtotal * 0.15
		} else {
			discount = 0.0
		}
		console.Print("€" + prim.ShowNumber(subtotal-discount))
	}
}
```

`let` and `where` are the same thing to Go: a local variable when the value is used more than once,
nothing when it's a constant or used once. The helper `format` was written in place.

## Effects are statements, and a `Ref` is a variable

```purescript
main :: Effect Unit
main = do
  argv <- args
  total <- Ref.new 0
  for_ (1 .. (length argv + 4)) \i -> do
    Ref.modify_ (_ + i) total
    current <- Ref.read total
    log ("running total: " <> show current)
  final <- Ref.read total
  when (final > 5) do
    log "that's a lot"
```

```go
func main() {
	argv := os.Args()
	var total int32 = 0
	step, count := array.RangeSteps(1, int32(len(argv))+4)
	for index := range count {
		i := 1 + int32(index)*step
		total += i
		console.Print("running total: " + strconv.Itoa(int(total)))
	}
	if total > 5 {
		console.Print("that's a lot")
	}
}
```

```
running total: 1
running total: 3
running total: 6
running total: 10
that's a lot
```

An `Effect` block is a list of Go statements that run in order: no thunks, no bind. A `Ref` that
doesn't escape is a local variable, and `for_` over a range is a counting loop that never builds
the array.

## `main` and console output

`main :: Effect Unit` is Go's `func main()`, and `log` from `Effect.Console` is `console.Print`,
which writes the line to standard output. If `main` runs an `Aff`, the program waits for it to
finish before it exits; see [Aff and threads](libraries.md#aff-runs-on-fibers).
