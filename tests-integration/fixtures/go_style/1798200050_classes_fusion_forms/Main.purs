module T.Fuse where

import Prelude

import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Array as Array
import Data.Foldable (foldMap, foldl, foldr, sum, length, any, all, maximum)
import Data.FunctorWithIndex (mapWithIndex)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (un)
import Data.String as String
import Data.String.Pattern (Pattern(..))
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Unfoldable (unfoldr)
import Data.List as List
import Effect (Effect)
import Effect.Console (log)

text :: String
text = "the quick brown fox jumps over the lazy dog the fox barks and the dog runs over hills"

-- form 1: pipeline
form1 :: String -> Array (String /\ Int)
form1 input = input # String.split (Pattern " ") # Array.filter (_ /= "") <#> String.toUpper # map (\w -> w /\ 1) # Map.fromFoldableWith (+) # Map.toUnfoldable # Array.sortWith (\(w /\ n) -> negate n /\ w) # Array.take 5

-- form 2: where clauses with fold
form2 :: String -> Array (String /\ Int)
form2 input = top5 counts
  where
  words = String.split (Pattern " ") input # Array.filter (not <<< String.null)
  counts = foldl bump Map.empty (map String.toUpper words)
  bump table word = Map.alter (Just <<< maybe1) word table
  maybe1 = case _ of
    Nothing -> 1
    Just n -> n + 1
  top5 table = Map.toUnfoldable table # Array.sortBy byCountThenWord # Array.take 5
  byCountThenWord (w1 /\ n1) (w2 /\ n2) = compare n2 n1 <> compare w1 w2

-- form 3: foldMap with Additive Map semigroup
form3 :: String -> Array (String /\ Int)
form3 input = input # String.split (Pattern " ") # Array.mapMaybe nonEmptyUpper # foldMap (\w -> Map.singleton w (Additive 1)) # map (un Additive) # Map.toUnfoldable # Array.sortWith ranking # Array.slice 0 5
  where
  nonEmptyUpper w = if w == "" then Nothing else Just (String.toUpper w)
  ranking (w /\ n) = (-n) /\ w

-- form 4: ST
form4 :: String -> Array (String /\ Int)
form4 input = ST.run do
  ref <- STRef.new Map.empty
  ST.foreach (String.split (Pattern " ") input) \w ->
    when (w /= "") do
      void (STRef.modify (Map.insertWith (+) (String.toUpper w) 1) ref)
  table <- STRef.read ref
  pure (Map.toUnfoldable table # Array.sortWith (\(w /\ n) -> (-n) /\ w) # Array.take 5)



main :: Effect Unit
main = do
  let results = [ form1 text, form2 text, form3 text, form4 text ]
  results <#> show # Array.intercalate "\n" # log
  log (show (Array.nub results # Array.length))
  -- fusion-ish chains
  let nums = Array.range 1 30
  log (show (nums <#> (_ * 3) # Array.filter (\n -> n `mod` 2 == 0) <#> (_ + 1) # Array.take 4))
  log (show (nums # Array.mapMaybe (\n -> if n `mod` 7 == 0 then Just (n * n) else Nothing) # sum))
  log (show (Array.zipWith (/\) nums (Array.reverse nums) # Array.filter (\(a /\ b) -> a > b) # Array.take 3))
  log (show (nums # mapWithIndex (\i n -> i * n) # foldlWithIndex (\i acc n -> acc + i + n) 0))
  log (show (nums # Array.concatMap (\n -> if n < 4 then [ n, -n ] else []) # Array.sort))
  log (show (unfoldr (\n -> if n > 100 then Nothing else Just (n /\ (n * 2))) 1 :: Array Int))
  log (show (nums # Array.dropWhile (_ < 25) # Array.takeWhile (_ < 28) # foldr Array.cons []))
  log (show (any (_ > 29) nums) <> show (all (_ > 0) nums) <> show (maximum (nums <#> negate)))
  log (show (Array.foldr (\n acc -> show n <> acc) "" (Array.slice 2 6 nums)))
  log (show (nums # Array.partition (\n -> n `mod` 3 == 0) # \{ yes, no } -> Array.length yes /\ Array.length no))
  log (show (Array.span (_ < 3) nums # _.init) <> show (Array.scanl (+) 0 [ 1, 2, 3 ]) <> show (Array.scanr (+) 0 [ 1, 2, 3 ]))
  log (show (Array.groupAllBy (comparing (_ `mod` 3)) [ 1, 2, 3, 4, 5, 6 ] <#> Array.fromFoldable))
  log (show (Array.zip [ 1, 2, 3 ] [ "a", "b" ] # Array.unzip))
  log (show (Array.foldM (\acc n -> if n > 0 then Just (acc + n) else Nothing) 0 [ 1, 2, 3 ]))
  log (show (Array.insertBy (comparing negate) 5 [ 9, 7, 3, 1 ]) <> show (Array.intersect [ 1, 2, 3 ] [ 2, 3, 4 ]) <> show (Array.difference [ 1, 2, 2, 3 ] [ 2 ]) <> show (Array.union [ 1, 2 ] [ 2, 3 ]))
  log (show (Array.updateAt 1 'x' [ 'a', 'b' ]) <> show (Array.modifyAt 5 identity [ 1 ]) <> show (Array.deleteAt 0 [ 1, 2 ]) <> show (Array.insertAt 1 0 [ 1, 2 ]) <> show (Array.alterAt 0 (const Nothing) [ 1, 2 ]))
  log (show (Array.findIndex (_ > 10) nums) <> show (Array.findLastIndex (_ < 10) nums) <> show (Array.elemIndex 5 nums) <> show (Array.find (_ > 100) nums))
  log (show (Array.sortBy (comparing snd <> comparing fst) [ 3 /\ 'a', 1 /\ 'b', 2 /\ 'a' ]))
