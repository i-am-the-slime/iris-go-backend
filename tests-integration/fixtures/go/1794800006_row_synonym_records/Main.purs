module Main where

import Prelude

import Data.Array as Array

type Padding r = ( spaceBefore :: Boolean, spaceAfter :: Boolean | r )
type TokValue v r = ( value :: v | r )

printLine :: forall r m. Monoid m => m -> Array (Record (Padding (TokValue m r))) -> m
printLine space = _.value <<< Array.foldl folder { value: mempty, space: false }
  where
  folder { value, space: spaced } { spaceBefore, spaceAfter, value: token } =
    { value: value <> (if spaced && spaceBefore then space else mempty) <> token
    , space: spaceAfter
    }

main :: String
main = printLine " "
  [ { spaceBefore: false, spaceAfter: true, value: "a", kind: 1 }
  , { spaceBefore: true, spaceAfter: false, value: "b", kind: 2 }
  ]
