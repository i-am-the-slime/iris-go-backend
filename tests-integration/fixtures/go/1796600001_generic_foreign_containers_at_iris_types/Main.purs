module Main where

import Prelude

import Data.Array (foldl)
import Data.Function.Uncurried (runFn2, runFn3)
import Data.Maybe (Maybe(..), maybe)
import Effect (Effect)
import Repeated (Repeated, describe, empty, freeze, indexOrImpl, length, snocImpl)

type Inner = { a :: Int, b :: String }

type Outer = { name :: String, inner :: Inner, tags :: Array Inner }

collect :: forall a. Array a -> Repeated a
collect = foldl (runFn2 snocImpl) empty

indexOr :: forall a. a -> Int -> Repeated a -> a
indexOr = runFn3 indexOrImpl

main :: Effect (Array String)
main = do
  let inners = collect [ { a: 1, b: "one" }, { a: 2, b: "two" } ]
  let outers = collect [ { name: "outer", inner: { a: 3, b: "three" }, tags: freeze inners } ]
  let rows = collect [ [ { a: 4, b: "four" } ], [] ]
  let maybes = collect [ Just { a: 5, b: "five" }, Nothing ]
  let outer = indexOr { name: "none", inner: { a: 0, b: "" }, tags: [] } 0 outers
  pure
    [ show (map _.a (freeze inners))
    , show (length outers)
    , outer.name <> outer.inner.b <> show (map _.a outer.tags)
    , show (map (map _.a) (freeze rows))
    , show (map (maybe "" _.b) (freeze maybes))
    , describe (indexOr { a: 0, b: "" } 1 inners)
    , describe 7
    ]
