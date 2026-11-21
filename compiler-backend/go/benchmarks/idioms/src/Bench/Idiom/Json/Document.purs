module Bench.Idiom.Json.Document
  ( Document
  , Item
  , document
  , checksum
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..), maybe)
import Data.String.CodeUnits as CodeUnits

-- | The shape both JSON benchmarks read and write: an array of nested records
-- | with strings (some escaped, some non-ASCII), numbers, arrays and an
-- | optional field.
type Document = { owner :: String, version :: Int, items :: Array Item }

type Item =
  { id :: Int
  , name :: String
  , price :: Number
  , tags :: Array String
  , dims :: { w :: Number, h :: Number }
  , note :: Maybe String
  }

document :: Int -> Document
document size = { owner: "bench \"owner\" naïve", version: 3, items: map item (Array.range 0 (size - 1)) }
  where
  item i =
    { id: i
    , name: "item-" <> show i <> "-" <> CodeUnits.take (i `mod` 17) "abcdefghijklmnopqrstuvwxyz"
    , price: toNumber (i `mod` 1000) / 8.0
    , tags: map (tag i) (Array.range 0 (i `mod` 4))
    , dims: { w: toNumber (i `mod` 50) + 0.5, h: toNumber (i `mod` 30) * 2.25 }
    , note: if i `mod` 7 == 0 then Just ("line\nbreak\t\"q\" café " <> show i) else Nothing
    }
  tag i j = "t" <> show ((i + j) `mod` 13)

-- | Sums what was read so that both sides must decode every field.
checksum :: Document -> Int
checksum doc = foldl step doc.version doc.items
  where
  step total it = total
    + it.id
    + CodeUnits.length it.name
    + floor (it.price * 8.0)
    + Array.length it.tags
    + foldl (\n t -> n + CodeUnits.length t) 0 it.tags
    + floor (it.dims.w * 2.0 + it.dims.h * 4.0)
    + maybe 0 CodeUnits.length it.note
