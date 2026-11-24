module T.Perf where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, sum)
import Data.Map as Map
import Data.Set as Set
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Foreign.Object as Object

type Row = { id :: Int, name :: String, score :: Number, tags :: Array String }

pseudo :: Int -> Int
pseudo n = (n * 1103515245 + 12345) `mod` 1000003


main :: Effect Unit
main = do
  let rows = Array.range 1 200000 <#> \i -> { id: i, name: "user" <> show (pseudo i `mod` 997), score: 0.5 * (if pseudo i > 500000 then 1.0 else -1.0), tags: [ show (i `mod` 3) ] }
  let sorted = Array.sortWith (\r -> r.name /\ r.id) rows
  log (show (Array.take 3 sorted <#> _.id))
  let byName = foldl (\m r -> Map.insertWith (+) r.name 1 m) Map.empty rows
  log (show (Map.size byName) <> show (Map.lookup "user5" byName))
  let obj = foldl (\o r -> Object.alter (\old -> Just (r.score + fromMaybe 0.0 old)) r.name o) Object.empty rows
  log (show (Object.size obj) <> show (Object.lookup "user5" obj))
  let updated = rows <#> _ { score = 1.0 } <#> (\r -> r { tags = Array.snoc r.tags "x" })
  log (show (sum (updated <#> _.score)) <> show (Array.length (Array.concatMap _.tags updated)))
  let set = Set.fromFoldable (rows <#> _.name)
  log (show (Set.size set))
  let joined = rows # Array.take 50000 <#> _.name # String.joinWith ","
  log (show (String.length joined) <> show (Array.length (String.split (String.Pattern ",") joined)))
  log (show (Array.foldl (\acc r -> acc + r.id `mod` 7) 0 rows))
  log (show (fromMaybe 0 (Array.last (Array.nub (rows <#> \r -> r.id `mod` 1000)))))
