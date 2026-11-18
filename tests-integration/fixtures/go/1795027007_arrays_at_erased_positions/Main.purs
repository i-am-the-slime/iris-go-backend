module Main where

import Prelude

import Data.Foldable (sum)
import Unsafe.Coerce (unsafeCoerce)

data Hidden

hide :: forall a. a -> Hidden
hide = unsafeCoerce

reveal :: forall a. Hidden -> a
reveal = unsafeCoerce

numbers :: Array Hidden
numbers = [ hide [ 1, 2 ], hide [ 3 ] ]

words :: Array Hidden
words = [ hide [ "a", "b" ] ]

main :: Array Int
main = map (\hidden -> sum (reveal hidden :: Array Int)) numbers <> map (\hidden -> 0 * sum (map (const 1) (reveal hidden :: Array String))) words
