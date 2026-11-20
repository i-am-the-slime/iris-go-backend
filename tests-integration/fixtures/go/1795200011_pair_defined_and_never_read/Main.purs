module Main where

import Prelude

import Control.Monad.ST (run)
import Data.Array.ST as STArray
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)
import Data.String (Pattern(..), stripPrefix)

-- stripPrefix splits its string in two. A poke at a constant negative index
-- stores nothing, so neither half is read: the definition of the pair must
-- go rather than become `_, _ :=`, which defines nothing.
stored :: Array String -> Array String
stored strings = run do
  array <- STArray.thaw strings
  _ <- STArray.poke (-2) (fromMaybe "none" (stripPrefix (Pattern ",") (foldl (\_ s -> s) ",a" strings))) array
  STArray.unsafeFreeze array

main :: Array String
main = stored [ ",b", "c" ]
