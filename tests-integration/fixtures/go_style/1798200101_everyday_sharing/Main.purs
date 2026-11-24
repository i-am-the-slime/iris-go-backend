module Fun.Sharing where

import Prelude

import Control.Monad.ST as ST
import Data.Array (cons, snoc, insertAt, updateAt, modifyAt, deleteAt, reverse, sort, sortBy, nub, zipWith, zip, (..), foldl, concatMap, filter, uncons, unsnoc, slice, take, drop, length, replicate, mapWithIndex, foldr, groupBy, catMaybes, mapMaybe, range)
import Data.Array.NonEmpty as NonEmpty
import Data.Array.ST as STArray
import Data.Foldable (for_, sum)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple.Nested ((/\))
import Effect (Effect, forE)
import Effect.Console (log)
import Effect.Ref as Ref

type Point = { x :: Int, y :: Int, tags :: Array String }

main :: Effect Unit
main = do
  let base = [ 1, 2, 3 ]
  let withFour = snoc base 4
  let withFive = snoc base 5
  let withSix = snoc withFour 6
  let withSeven = snoc withFour 7
  log $ show [ base, withFour, withFive, withSix, withSeven ]
  let grown = foldl snoc [] (1 .. 5)
  let branchA = snoc grown 100
  let branchB = snoc grown 200
  log $ show [ grown, branchA, branchB ]
  let consed = cons 0 base
  let consed2 = cons (-1) base
  log $ show [ consed, consed2, base ]
  let appended = base <> [ 9 ]
  let appended2 = base <> [ 8 ]
  log $ show [ appended, appended2 ]
  let built = foldl (\acc n -> acc <> [ n ]) [] (1 .. 4)
  let builtA = built <> [ 10 ]
  let builtB = built <> [ 20 ]
  log $ show [ built, builtA, builtB ]
  log $ show [ fromMaybe [] (updateAt 0 99 base), base, fromMaybe [] (modifyAt 1 (_ * 10) base), fromMaybe [] (insertAt 1 7 base), fromMaybe [] (deleteAt 0 base), base ]
  let sorted = sort [ 3, 1, 2 ]
  let original = [ 3, 1, 2 ]
  let sortedOriginal = sort original
  log $ show [ sorted, original, sortedOriginal, reverse original, original ]
  log $ show (sortBy (comparing negate) original) <> show original
  let sliced = slice 1 3 [ 10, 20, 30, 40 ]
  let slicedGrown = snoc sliced 99
  let slicedGrown2 = snoc sliced 77
  log $ show [ sliced, slicedGrown, slicedGrown2 ]
  let taken = take 2 [ 10, 20, 30, 40 ]
  log $ show [ snoc taken 1, snoc taken 2, taken ]
  let dropped = drop 1 [ 10, 20, 30 ]
  log $ show [ snoc dropped 1, snoc dropped 2, dropped ]
  case uncons [ 1, 2, 3 ] of
    Just { head, tail } -> log $ show [ [ head ], snoc tail 8, snoc tail 9, tail ]
    Nothing -> pure unit
  case unsnoc [ 1, 2, 3 ] of
    Just { init, last } -> log $ show [ [ last ], snoc init 8, snoc init 9, init ]
    Nothing -> pure unit
  let thawed = ST.run do
        arr <- STArray.thaw base
        _ <- STArray.push 42 arr
        _ <- STArray.poke 0 100 arr
        STArray.unsafeFreeze arr
  log $ show [ thawed, base ]
  let frozenTwice = STArray.run do
        arr <- STArray.new
        for_ (1 .. 3) \i -> STArray.push i arr
        pure arr
  log $ show [ snoc frozenTwice 4, snoc frozenTwice 5, frozenTwice ]
  let point = { x: 1, y: 2, tags: [ "a" ] }
  let moved = point { x = 10 }
  let tagged = point { tags = snoc point.tags "b" }
  let tagged2 = point { tags = snoc point.tags "c" }
  log $ show [ point, moved, tagged, tagged2 ]
  let points = [ point, moved ]
  let shifted = points <#> \p -> p { y = p.y + 1 }
  log $ show points <> show shifted
  closures <- Ref.new []
  forE 0 3 \i -> Ref.modify_ (_ <> [ \_ -> i * 10 ]) closures
  fns <- Ref.read closures
  log $ show (fns <#> (_ $ unit))
  let lazyClosures = (0 .. 3) <#> \i -> \_ -> i * i
  log $ show (lazyClosures <@> unit)
  let nested = (1 .. 3) <#> \i -> (1 .. i) <#> \j -> \_ -> i * 10 + j
  log $ show (nested <#> map (_ $ unit))
  log $ show (zipWith (+) [ 1, 2, 3 ] [ 10, 20 ]) <> show (zip [ 1, 2 ] [ "a", "b", "c" ])
  log $ show (nub [ 3, 1, 3, 2, 1 ])
  log $ show (concatMap (\n -> replicate n n) [ 1, 2, 3 ])
  log $ show (mapWithIndex (\i n -> i * n) [ 5, 6, 7 ])
  log $ show (foldr (\n acc -> acc <> show n) "" (1 .. 5))
  log $ show (groupBy (\a b -> a `mod` 2 == b `mod` 2) [ 1, 3, 2, 4, 5 ] <#> NonEmpty.toArray)
  log $ show (catMaybes [ Just 1, Nothing, Just 3 ]) <> show (mapMaybe (\n -> if n > 1 then Just (n * 2) else Nothing) [ 1, 2, 3 ])
  log $ show (1 .. 0) <> show (5 .. 1) <> show (range 0 0)
  log $ show (sum (1 .. 1000000))
  log $ show (length (foldl snoc [] (1 .. 100000)))
  let pairs = (1 .. 3) <#> \i -> i /\ show i
  log $ show pairs
