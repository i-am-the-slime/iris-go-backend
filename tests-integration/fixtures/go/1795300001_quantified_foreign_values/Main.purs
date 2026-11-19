module Main where

import Prelude

import Data.Array (length)
import Effect (Effect)
import Optional
  ( absent
  , emptyArray
  , emptySwappedPair
  , newCounter
  , pairSize
  , present
  , swappedPair
  , withDefault
  )

-- | A quantified foreign value without arguments is a generic Go function without parameters,
-- instantiated at its quantifiers in their declared order and called; an effectful one is
-- instantiated and performed.
main :: Effect (Array String)
main = do
  counter <- newCounter
  let later = newCounter
  again <- later
  pure
    [ show [ withDefault 1 absent, withDefault 1 (present 2) ]
    , withDefault "fallback" absent
    , show (length (emptyArray :: Array String))
    , show [ pairSize (swappedPair 1 "one"), pairSize (emptySwappedPair :: _ String Int) ]
    , show (withDefault 3 counter)
    , show (withDefault true again)
    ]
