module Main where

import Prelude

import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref as Ref
import Foreign.Object (Object)
import Foreign.Object as Object

countWords :: Array String -> Object Int
countWords = foldl (\counts word -> Object.alter (Just <<< maybe 1 (_ + 1)) word counts) Object.empty
  where
  maybe default f = case _ of
    Just value -> f value
    Nothing -> default

type Window = { start :: Int, seen :: Map Int Int }

slide :: Array Int -> Window
slide = foldl step { start: 0, seen: Map.empty }
  where
  step window x = do
    let
      start = case Map.lookup x window.seen of
        Just at -> max window.start at
        Nothing -> window.start
    { start, seen: Map.insert x (start + 1) window.seen }

main :: Effect Unit
main = do
  words <- Ref.new [ "a", "b", "a" ]
  numbers <- Ref.new [ 3, 1, 3, 2 ]
  counts <- countWords <$> Ref.read words
  window <- slide <$> Ref.read numbers
  output <- Ref.new (Object.size counts + window.start + Map.size window.seen)
  Ref.write 0 output
