module Fun.Language where

import Prelude

import Data.Array (head, uncons, (:))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_, sum)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Map as Map
import Data.String (joinWith)
import Data.Tuple.Nested ((/\), type (/\))
import Effect (Effect)
import Effect.Console (log)

infixr 5 appendWithDash as <->
infixl 6 subtractTwice as |-|
infix 4 roughlyEqual as ~=

appendWithDash :: String -> String -> String
appendWithDash left right = left <> "-" <> right

subtractTwice :: Int -> Int -> Int
subtractTwice a b = a - 2 * b

roughlyEqual :: Number -> Number -> Boolean
roughlyEqual a b = (a - b) < 0.01 && (b - a) < 0.01

data Shape
  = Circle Number
  | Rectangle { width :: Number, height :: Number }
  | Polygon (Array (Number /\ Number))

describe :: Shape -> String
describe = case _ of
  Circle radius
    | radius <= 0.0 -> "degenerate circle"
    | radius > 100.0 -> "huge circle"
    | otherwise -> "circle " <> show radius
  Rectangle { width, height }
    | width == height -> "square " <> show width
  Rectangle rect@{ width: _ } -> "rect " <> show rect.width <> "x" <> show rect.height
  Polygon [] -> "empty polygon"
  Polygon [ _ ] -> "point"
  Polygon [ a, b ] -> "segment " <> show a <> show b
  Polygon points
    | Just { head: first } <- uncons points
    , first == (0.0 /\ 0.0) -> "polygon from origin with " <> show (Array.length points)
    | otherwise -> "polygon with " <> show (Array.length points)

lookupAll :: Map.Map String Int -> Array String -> String
lookupAll table keys = joinWith "," (keys <#> describeKey)
  where
  describeKey key
    | Just value <- Map.lookup key table
    , value > 10 = key <> ":big"
    | Just value <- Map.lookup key table = key <> ":" <> show value
    | otherwise = key <> ":missing"

type Transformer = forall a. Array a -> Array a

applyToBoth :: Transformer -> Array Int /\ Array String -> Array Int /\ Array String
applyToBoth transform (numbers /\ words) = transform numbers /\ transform words

applyIdentityTwice :: (forall a. a -> a) -> Int /\ String
applyIdentityTwice f = f 1 /\ f "one"

maybeToArray :: Maybe ~> Array
maybeToArray = case _ of
  Just a -> [ a ]
  Nothing -> []

hoistBoth :: forall f g. (f ~> g) -> f Int -> f String -> g Int /\ g String
hoistBoth nat a b = nat a /\ nat b

type Operations f =
  { wrap :: forall a. a -> f a
  , combine :: f Int -> f Int -> f Int
  , label :: String
  }

arrayOps :: Operations Array
arrayOps = { wrap: \a -> [ a ], combine: (<>), label: "array" }

maybeOps :: Operations Maybe
maybeOps = { wrap: Just, combine: \a b -> (+) <$> a <*> b, label: "maybe" }

runOperations :: forall f. Show (f Int) => Operations f -> String
runOperations { wrap, combine, label } = label <> " " <> show (combine (wrap 1) (wrap 2))

sumWithLocalAnnotations :: Array Int -> Int
sumWithLocalAnnotations numbers = do
  let doubled :: Array Int
      doubled = numbers <#> (_ * 2)
  let total = sum doubled
  total + offset
  where
  offset :: Int
  offset = helper 3
    where
    helper :: Int -> Int
    helper n = n * innerConstant
      where
      innerConstant = 10

firstTwo :: Array Int -> String
firstTwo = case _ of
  [ a, b ] -> "exactly " <> show (a + b)
  all@[ _, _, _ ] -> "three " <> show all
  other -> "other " <> show (head other)

recordUpdate :: { name :: String, age :: Int } -> { name :: String, age :: Int }
recordUpdate person = person { age = person.age + 1, name = person.name <> "!" }

nestedUpdate :: { outer :: { inner :: Int, keep :: String } } -> { outer :: { inner :: Int, keep :: String } }
nestedUpdate record = record { outer { inner = record.outer.inner * 2 } }

classify :: Int -> String
classify n
  | n < 0 = "negative"
  | n == 0 = "zero"
  | even n, n > 100 = "big even"
  | even n = "even"
  | otherwise = "odd"

even :: Int -> Boolean
even x = x `mod` 2 == 0

ifThenElse :: Int -> String
ifThenElse n = if n > 5 then "big" else if n > 2 then "medium" else "small"

charPatterns :: Char -> String
charPatterns = case _ of
  'a' -> "letter a"
  '\n' -> "newline"
  _ -> "other"

stringPatterns :: String -> Int
stringPatterns = case _ of
  "one" -> 1
  "two" -> 2
  "" -> 0
  _ -> -1

numberPatterns :: Number -> String
numberPatterns = case _ of
  0.0 -> "zero"
  1.5 -> "one and a half"
  _ -> "something"

booleanPatterns :: Boolean -> Boolean -> String
booleanPatterns true true = "both"
booleanPatterns true _ = "first"
booleanPatterns _ true = "second"
booleanPatterns false false = "neither"

main :: Effect Unit
main = do
  log $ "a" <-> "b" <-> "c"
  log $ show (10 |-| 2 |-| 1)
  log $ show (1.0 ~= 1.001) <> show (1.0 ~= 1.1)
  for_ shapes (describe >>> log)
  log $ lookupAll (Map.fromFoldable [ "a" /\ 5, "b" /\ 20 ]) [ "a", "b", "c" ]
  log $ show (applyToBoth Array.reverse ([ 1, 2, 3 ] /\ [ "x", "y" ]))
  log $ show (applyToBoth (Array.take 1) ([ 1, 2, 3 ] /\ [ "x", "y" ]))
  log $ show (applyIdentityTwice identity)
  log $ show (hoistBoth maybeToArray (Just 1) Nothing)
  log $ runOperations arrayOps
  log $ runOperations maybeOps
  log $ show (sumWithLocalAnnotations [ 1, 2, 3 ])
  log $ firstTwo [ 1, 2 ]
  log $ firstTwo [ 1, 2, 3 ]
  log $ firstTwo [ 9 ]
  log $ firstTwo []
  log $ show (recordUpdate { name: "ann", age: 41 })
  log $ show (nestedUpdate { outer: { inner: 21, keep: "k" } })
  log $ show (map classify [ -1, 0, 7, 8, 200 ])
  log $ show (map ifThenElse [ 1, 3, 9 ])
  log $ show (map charPatterns [ 'a', '\n', 'z' ])
  log $ show (map stringPatterns [ "one", "two", "", "x" ])
  log $ show (map numberPatterns [ 0.0, 1.5, 2.0, -0.0 ])
  log $ show [ booleanPatterns true true, booleanPatterns true false, booleanPatterns false true, booleanPatterns false false ]
  log $ show (1 : 2 : [ 3 ])
  log $ show (fromMaybe 0 (Array.index [ 1, 2 ] 5))
  let { x, y: renamed } = { x: 1, y: 2 }
  log $ show (x + renamed)
  let swap (a /\ b) = b /\ a
  log $ show (swap (1 /\ "s"))
  case Right 5 :: Either String Int of
    Left err -> log err
    Right n | n > 3 -> log "big right"
    Right _ -> log "small right"
  where
  shapes =
    [ Circle 0.0, Circle 500.0, Circle 2.5, Rectangle { width: 2.0, height: 2.0 }, Rectangle { width: 2.0, height: 3.0 }
    , Polygon [], Polygon [ 1.0 /\ 1.0 ], Polygon [ 1.0 /\ 1.0, 2.0 /\ 2.0 ], Polygon [ 0.0 /\ 0.0, 1.0 /\ 0.0, 1.0 /\ 1.0 ]
    , Polygon [ 5.0 /\ 0.0, 1.0 /\ 0.0, 1.0 /\ 1.0 ]
    ]
