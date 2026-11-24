module Main where

import Prelude

import Control.Monad.ST as ST
import Data.Array.ST as STArray
import Foreign.Object as Object
import Foreign.Object.ST as STObject

-- | The ST primitives perform their action when called: `array.Thaw(numbers)`, not a thunk
-- | called at once.
doubled :: Array Int -> Array Int
doubled numbers = ST.run do
  array <- STArray.thaw numbers
  _ <- STArray.push 0 array
  STArray.unsafeFreeze array

-- | So do Foreign.Object.ST's: `object.New[int32]()` and `object.Poke("a", 1, table)`.
counts :: Object.Object Int
counts = Object.runST do
  table <- STObject.new
  _ <- STObject.poke "a" 1 table
  _ <- STObject.poke "b" 2 table
  pure table

-- | Showing a whole array is one call that returns the string: `show.ArrayInt(numbers)`.
main :: Array String
main =
  [ show (doubled [ 1, 2 ])
  , show (Object.keys counts)
  , show [ true, false ]
  ]
