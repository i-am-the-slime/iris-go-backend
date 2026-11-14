module Bench.Generic.Argonaut where

import Prelude

import Bench.Harness (benchmark)
import Data.Argonaut.Core (stringify)
import Data.Argonaut.Decode (decodeJson, parseJson, printJsonDecodeError)
import Data.Argonaut.Encode (encodeJson)
import Data.Array ((..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)

hypothesis :: String
hypothesis = "argonaut encodeJson and decodeJson of records go through Json, an opaque foreign type that Go represents as any"

type Item =
  { id :: Int
  , name :: String
  , tags :: Array String
  , parent :: Maybe Int
  }

main :: Effect Unit
main = benchmark { size: 15000, workload }

workload :: Int -> String
workload n = do
  let items = map item (1 .. n)
  let encoded = stringify (encodeJson items)
  case parseJson encoded >>= decodeJson of
    Right (decoded :: Array Item) -> show (CodeUnits.length encoded) <> " " <> show (Array.length decoded) <> " " <> show (map _.name (Array.last decoded))
    Left problem -> printJsonDecodeError problem
  where
  item i =
    { id: i
    , name: "item " <> show i
    , tags: map (\j -> "t" <> show j) (0 .. (i `mod` 4))
    , parent: if i `mod` 3 == 0 then Nothing else Just (i / 2)
    }
