module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Foreign.Object as Object
import Foreign.Object.ST as STObject

-- | Prints a line.
foreign import log :: String -> Effect Unit

main :: Effect Unit
main = do
  log "-- array-index keys come first, the others in the order they were first set"
  let keys = [ "b", "a", "2", "1", "b", "10", "c" ]
  let numbered = Object.fromFoldable (Array.mapWithIndex (\index key -> key /\ index) keys)
  log (show (Object.keys numbered))
  log (show (Object.values numbered))
  log "-- counted words"
  let counted = Object.fromFoldableWith (+) (keys <#> \key -> key /\ 1)
  log (show (Object.toUnfoldable counted :: Array _))
  log "-- an object filled in ST, then grown and shrunk"
  let filled = Object.runST do
        object <- STObject.new
        for_ (Array.range 1 12) \n -> STObject.poke (show (n `mod` 7)) n object
        pure object
  log (show (Object.toUnfoldable (Object.delete "3" (Object.insert "x" 0 filled)) :: Array _))
  log (show (Object.size filled) <> " " <> show (Object.lookup "5" filled))
  log "-- nothing to fill"
  log (show (Object.keys (Object.fromFoldable ([] :: Array _) :: Object.Object Int)))
