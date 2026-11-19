module Main where

import Prelude

import Control.Monad.ST (ST, for, run)
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Array.ST.Partial as Partial
import Data.Maybe (Maybe(..), fromMaybe)
import Partial.Unsafe (unsafePartial)

doubled :: forall region. STArray region Int -> ST region Int
doubled array = do
  size <- STArray.length array
  for 0 size \i -> do
    x <- STArray.peek i array
    void (STArray.poke i (2 * fromMaybe 0 x) array)
  pure size

bumpedLast :: forall region. STArray region Int -> ST region Boolean
bumpedLast array = do
  size <- STArray.length array
  last <- unsafePartial (Partial.peek (size - 1) array)
  unsafePartial (Partial.poke (size - 1) (last + 1) array)
  STArray.poke size 0 array

labelled :: forall region. STArray region String -> ST region (Maybe String)
labelled array = STArray.peek 1 array >>= case _ of
  Just name -> pure (Just ("#" <> name))
  Nothing -> pure Nothing

main :: Array Int
main = run do
  array <- STArray.thaw [ 1, 2, 3 ]
  size <- doubled array
  grown <- bumpedLast array
  names <- STArray.thaw [ "a", "b" ]
  label <- labelled names
  elements <- STArray.unsafeFreeze array
  pure (elements <> [ size, if grown then 1 else 0, if label == Just "#b" then 1 else 0 ])
