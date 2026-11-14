module Bench.Generic.YogaJson where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)
import Yoga.JSON (readJSON, writeJSON)

hypothesis :: String
hypothesis = "yoga-json writeJSON and readJSON of a large record structure: JS uses the engine's native JSON, Go walks a Foreign tree of any"

type Item =
  { id :: Int
  , name :: String
  , price :: Number
  , tags :: Array String
  , parent :: Maybe Int
  , dimensions :: { width :: Number, height :: Number }
  }

main :: Effect Unit
main = benchmark { size: 15000, workload }

workload :: Int -> String
workload n = do
  let items = map item (1 .. n)
  let encoded = writeJSON items
  case readJSON encoded of
    Right (decoded :: Array Item) -> show (CodeUnits.length encoded) <> " " <> show (Array.length decoded) <> " " <> show (map _.name (Array.last decoded))
    Left errors -> show errors
  where
  item i =
    { id: i
    , name: "item \"" <> show i <> "\" ✓"
    , price: 0.25 * (toNumber' i)
    , tags: map (\j -> "t" <> show j) (0 .. (i `mod` 4))
    , parent: if i `mod` 3 == 0 then Nothing else Just (i / 2)
    , dimensions: { width: 1.5, height: 2.0 }
    }

  toNumber' i = if i `mod` 2 == 0 then 3.0 else 7.5
