module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, for_, maximum)
import Data.Maybe (fromMaybe)
import Effect (Effect, foreachE)
import Journal (log)
import Type.Proxy (Proxy(..))

type Point = { x :: Int, y :: Int, label :: String }

type Field message = { number :: Int, wireType :: Int, write :: message -> Effect Unit }

type Codec message = { wireTypes :: Array Int, write :: message -> Effect Unit }

-- | A codec worked out from a list of numbered fields, the way a derived protobuf codec is: the
-- | table of wire types and the writers in the order of their numbers are known when it compiles.
codecOf :: Proxy Point -> Codec Point
codecOf proxy = { wireTypes, write }
  where
  fields = fieldsOf proxy
  wireTypes = foldl noted (Array.replicate (largest + 1) (-1)) fields
  largest = fields <#> _.number # maximum # fromMaybe 0
  noted table { number, wireType } = Array.updateAt number wireType table # fromMaybe table
  inOrder = fields # Array.sortWith _.number
  write point = foreachE inOrder \field -> field.write point

fieldsOf :: Proxy Point -> Array (Field Point)
fieldsOf _ = Array.cons label ([ x ] <> [ y ])
  where
  label = numbered 3 2 \point -> log point.label
  x = numbered 1 0 \point -> log (show point.x)
  y = numbered 2 0 \point -> log (show point.y)

numbered :: forall message. Int -> Int -> (message -> Effect Unit) -> Field message
numbered number wireType write = { number, wireType, write }

main :: Effect Unit
main = do
  log (show codec.wireTypes)
  for_ points codec.write
  where
  codec = codecOf Proxy
  points = Array.range 1 3 <#> \n -> { x: n, y: n * n, label: "point " <> show n }
