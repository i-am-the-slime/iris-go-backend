module Repro.ExistsStream where

import Prelude

import Data.Exists (Exists, mkExists, runExists)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

data StreamF a s = StreamF s (s -> Maybe (a /\ s))

countdown :: Int -> Exists (StreamF Int)
countdown n = mkExists (StreamF n \s -> if s <= 0 then Nothing else Just (s /\ (s - 1)))

toArray :: forall a. Exists (StreamF a) -> Array a
toArray = runExists \(StreamF seed next) -> go next seed
  where
  go :: forall s. (s -> Maybe (a /\ s)) -> s -> Array a
  go next seed = case next seed of
    Nothing -> []
    Just (a /\ rest) -> [ a ] <> go next rest

main :: Effect Unit
main = log (show (toArray (countdown 3)))
