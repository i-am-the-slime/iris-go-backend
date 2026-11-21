# Loops, arrays and memory

How array pipelines, folds and mutable arrays turn into Go loops. As in [the basics](basics.md),
the examples read `length argv` so that the compiler can't work out the result ahead of time.

## A pipeline is one loop

```purescript
main :: Effect Unit
main = do
  argv <- args
  let words = map (\i -> "item" <> show i) (1 .. (length argv + 20))
  let total = words
        # map String.length
        # filter (_ > 5)
        # foldl (+) 0
  log (show total)
```

```go
func main() {
	argv := os.Args()
	step, count := array.RangeSteps(1, int32(len(argv))+20)
	var accumulator int32 = 0
	for index := range count {
		i := 1 + int32(index)*step
		value := codepoints.Length("item" + strconv.Itoa(int(i)))
		if value > 5 {
			accumulator += value
		}
	}
	console.Print(strconv.Itoa(int(accumulator)))
}
```

The range, both `map`s, the `filter` and the `foldl` run in a single loop, and none of the four
arrays in between is ever built. An array that's only read once by the next step doesn't need to
exist.

Not every pipeline fuses: in the [`Maybe` and `Either`](basics.md#maybe-and-either) example,
`map parse numbers` is built as an array before `for_` loops over it.

## Appending to an accumulator changes it in place

```purescript
evens :: Array Int -> Array Int
evens = foldl (\acc n -> if n `mod` 2 == 0 then snoc acc n else acc) []

digits :: Array Int -> String
digits = foldl (\acc n -> acc <> show n <> ",") ""

main :: Effect Unit
main = do
  argv <- args
  let numbers = 1 .. (length argv + 10)
  log (show (evens numbers))
  log (digits numbers)
```

```go
func main() {
	argv := os.Args()
	numbers := array.RangeInt32(1, int32(len(argv))+10)
	accumulator := []int32{}
	accumulator = slices.Clip(accumulator)
	for _, n := range numbers {
		if prim.IntMod(n, 2) == 0 {
			accumulator = array.Bounded(append(accumulator, n))
		}
	}
	console.Print(string(show.AppendShowArrayInt(nil, accumulator)))
	accumulator2 := []byte("")
	for _, n := range numbers {
		accumulator2 = strconv.AppendInt(accumulator2, int64(n), 10)
		accumulator2 = append(accumulator2, ","...)
	}
	built := string(accumulator2)
	console.Print(built)
}
```

`snoc` copies its array, so a fold of `snoc`s would copy the whole array at every step. Nothing but
the fold ever sees `acc`, though, so Iris appends to it with Go's `append`. In the same way, a
string that a fold only appends to grows in a `[]byte` and becomes a string once, at the end.

## Data that nothing else holds is reused

```purescript
data Tree = Leaf | Node Tree Int Tree

insert :: Int -> Tree -> Tree
insert x = case _ of
  Leaf -> Node Leaf x Leaf
  Node left y right
    | x < y -> Node (insert x left) y right
    | x > y -> Node left y (insert x right)
    | otherwise -> Node left y right

main :: Effect Unit
main = do
  argv <- args
  let tree = foldl (flip insert) Leaf (map (\i -> (i * 37) `mod` 101) (1 .. (length argv + 100)))
  log (show (size tree))
```

```go
func main() {
	argv := os.Args()
	step, count := array.RangeSteps(1, int32(len(argv))+100)
	accumulator := sharedTreeLeaf
	for index := range count {
		i := 1 + int32(index)*step
		a := prim.IntMod(i*37, 101)
		accumulator = insertReusing(a, accumulator)
	}
	console.Print(strconv.Itoa(int(size(accumulator))))
}

func insertReusing(x int32, value *Tree) *Tree {
	if value == sharedTreeLeaf {
		return &Tree{Node0: sharedTreeLeaf, Node1: x, Node2: sharedTreeLeaf}
	}
	left := value.Node0
	y := value.Node1
	right := value.Node2
	if x < y {
		field := insertReusing(x, left)
		value.Node0 = field
		value.Node1 = y
		value.Node2 = right
		return value
	}
	if x > y {
		field := insertReusing(x, right)
		value.Node0 = left
		value.Node1 = y
		value.Node2 = field
		return value
	}
	value.Node0 = left
	value.Node1 = y
	value.Node2 = right
	return value
}
```

Each tree in the fold is dropped as soon as the next one is built, so `insert` can overwrite the
nodes it takes apart instead of allocating new ones. Iris writes a second version of `insert` that
does that, and calls it where the old tree is dead. A tree you still hold elsewhere gets the plain
`insert`, which copies.

Binding the whole node, as in `node@(Node left y right) … -> node`, keeps the plain version: the
node escapes as it is.

## A record accumulator lives in one variable per field

```purescript
type Moments = { count :: Number, sum :: Number, sumOfSquares :: Number }

moments :: Array Number -> Moments
moments = foldl step { count: 0.0, sum: 0.0, sumOfSquares: 0.0 }
  where
  step m x = m { count = m.count + 1.0, sum = m.sum + x, sumOfSquares = m.sumOfSquares + x * x }

main :: Effect Unit
main = do
  argv <- args
  let samples = map toNumber (1 .. (length argv + 1000))
  let m = moments samples
  let mean = m.sum / m.count
  log ("mean " <> show mean <> ", variance " <> show (m.sumOfSquares / m.count - mean * mean))
```

```go
func main() {
	argv := os.Args()
	step, count := array.RangeSteps(1, int32(len(argv))+1000)
	var accumulatorCount float64 = 0.0
	var accumulatorSum float64 = 0.0
	var accumulatorSumOfSquares float64 = 0.0
	for index := range count {
		i := 1 + int32(index)*step
		x := float64(i)
		accumulatorCount += 1.0
		accumulatorSum += x
		accumulatorSumOfSquares += x * x
	}
	mean := accumulatorSum / accumulatorCount
	console.Print("mean " + prim.ShowNumber(mean) + ", variance " + prim.ShowNumber(accumulatorSumOfSquares/accumulatorCount-mean*mean))
}
```

The record never exists. Each field is a variable of its own, which Go can keep in a register, and
the update `m { … }` is three assignments.

A record that a tail-recursive function passes to itself is still a struct, updated as a copy:

```purescript
type Body = { x :: Number, y :: Number, vx :: Number, vy :: Number }

simulate :: Int -> Body -> Body
simulate steps body
  | steps <= 0 = body
  | otherwise = simulate (steps - 1) (body { x = body.x + body.vx, y = body.y + body.vy, vy = body.vy - 9.81 })
```

```go
func simulate(steps int32, body shared.Body) shared.Body {
	for {
		if steps <= 0 {
			return body
		}
		updated := body
		updated.X = body.X + body.Vx
		updated.Y = body.Y + body.Vy
		updated.Vy = body.Vy - 9.81
		steps, body = steps-1, updated
	}
}
```

## Number crunching runs on SIMD vectors

```purescript
main :: Effect Unit
main = do
  argv <- args
  let prices = map toNumber (1 .. (length argv + 1000))
  let withTax = map (\p -> p * 1.19) prices
  let total = foldl (+) 0.0 withTax
  log (show (length withTax) <> " prices, total " <> show total)
```

`main.go`:

```go
func main() {
	argv := os.Args()
	step, count := array.RangeSteps(1, int32(len(argv))+1000)
	mapped := make([]float64, count)
	for index := range count {
		i := 1 + int32(index)*step
		p := float64(i)
		mapped[index] = p * 1.19
	}
	console.Print(strconv.Itoa(len(mapped)) + " prices, total " + prim.ShowNumber(foldLanes(mapped, 0.0)))
}
```

`main_neon.go`:

```go
//go:build goexperiment.simd && arm64

func foldLanes(xs []float64, initial float64) float64 {
	acc0 := archsimd.BroadcastFloat64x2(math.Copysign(0, -1))
	acc1, acc2, acc3 := acc0, acc0, acc0
	const step = 2
	i := 0
	for ; i < len(xs)-4*step+1; i += 4 * step {
		x0 := archsimd.LoadFloat64x2(xs[i : i+step])
		acc0 = acc0.Add(x0)
		x1 := archsimd.LoadFloat64x2(xs[i+step : i+2*step])
		acc1 = acc1.Add(x1)
		x2 := archsimd.LoadFloat64x2(xs[i+2*step : i+3*step])
		acc2 = acc2.Add(x2)
		x3 := archsimd.LoadFloat64x2(xs[i+3*step : i+4*step])
		acc3 = acc3.Add(x3)
	}
	acc0 = acc0.Add(acc1).Add(acc2.Add(acc3))
	var lanes [2]float64
	acc0.Store(lanes[:])
	accumulator := initial
	for _, lane := range lanes[:step] {
		accumulator = accumulator + lane
	}
	for ; i < len(xs); i++ {
		x := xs[i]
		accumulator = accumulator + x
	}
	return accumulator
}
```

`withTax` is used twice, so it's built, and the `foldl (+)` over it is a kernel of its own. Next to
`main.go` you get one file per target: `main_neon.go` for arm64, `main_vector.go` for wasm, and
`main_scalar.go`, a plain loop, for everything else or when `GOEXPERIMENT=simd` is off.
`iris run --go` turns the experiment on for you.

A vector adds up several elements at a time, so a `Number` sum can differ from JavaScript's in its
last digits. [Sums over vectors](../go-output.md#sums-over-vectors) says which folds and maps run
on vectors and when the results differ.

## `ST` arrays are slices you index directly

```purescript
swap :: forall r a. Int -> Int -> STArray r a -> ST r Unit
swap i j array = do
  x <- STArray.peek i array
  y <- STArray.peek j array
  case x, y of
    Just a, Just b -> do
      _ <- STArray.poke i b array
      _ <- STArray.poke j a array
      pure unit
    _, _ -> pure unit

reverseInPlace :: Array Int -> Array Int
reverseInPlace xs = STArray.run do
  array <- STArray.thaw xs
  let n = length xs
  ST.for 0 (n / 2) \i -> swap i (n - 1 - i) array
  pure array

main :: Effect Unit
main = do
  argv <- args
  log (show (reverseInPlace (1 .. (length argv + 7))))
```

```go
func main() {
	argv := os.Args()
	xs := array.RangeInt32(1, int32(len(argv))+7)
	array2 := array.Thaw(xs)()
	n := int32(len(xs))
	end := prim.IntDiv(n, 2)
	elements := *array2
	for i := int32(0); i < end; i++ {
		j := n - 1 - i
		var peeked maybe.Int
		if int(i) < len(elements) {
			peeked = maybe.Int(elements[i])
		} else {
			peeked = maybe.NoInt
		}
		var peeked2 maybe.Int
		if j >= 0 && int(j) < len(elements) {
			peeked2 = maybe.Int(elements[j])
		} else {
			peeked2 = maybe.NoInt
		}
		if peeked != maybe.NoInt && peeked2 != maybe.NoInt {
			if int(i) < len(elements) {
				elements[i] = int32(peeked2)
			}
			if j >= 0 && int(j) < len(elements) {
				elements[j] = int32(peeked)
			}
		}
	}
	performed := array.UnsafeFreeze(array2)()
	console.Print(string(show.AppendShowArrayInt(nil, performed)))
}
```

`thaw` copies the array once. After that `peek` is a bounds test and an index, `poke` is a bounds
test and an assignment, and `ST.for` is a `for` loop.

When a missing element has a default instead, all four accesses share one bounds test:

```purescript
reverseInPlace :: Array Int -> Array Int
reverseInPlace xs = STArray.run do
  array <- STArray.thaw xs
  let n = length xs
  let peekOr0 i = fromMaybe 0 <$> STArray.peek i array
  ST.for 0 (n / 2) \i -> do
    let j = n - 1 - i
    x <- peekOr0 i
    y <- peekOr0 j
    _ <- STArray.poke i y array
    STArray.poke j x array
  pure array
```

```go
	for i := int32(0); i < end; i++ {
		j := n - 1 - i
		var i2 int32
		var i3 int32
		if int(i) < len(elements) && j >= 0 && int(j) < len(elements) {
			i2 = elements[i]
			i3 = elements[j]
			elements[i] = i3
			elements[j] = i2
		} else {
			within := int(i) < len(elements)
			if within {
				i2 = elements[i]
			} else {
				i2 = 0
			}
			within2 := j >= 0 && int(j) < len(elements)
			if within2 {
				i3 = elements[j]
			} else {
				i3 = 0
			}
			if int(i) < len(elements) {
				elements[i] = i3
			}
			if j >= 0 && int(j) < len(elements) {
				elements[j] = i2
			}
		}
	}
```

When both indices are in bounds, which is every time here, the swap is four plain accesses that Go
knows are in bounds. The `else` branch keeps the exact behaviour for an index out of bounds.
