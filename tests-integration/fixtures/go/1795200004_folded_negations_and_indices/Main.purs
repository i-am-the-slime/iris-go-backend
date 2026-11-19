module Main where

import Prelude

import Data.Array as Array
import Data.Lazy as Lazy
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Effect (Effect)

negated :: Int
negated = negate (Lazy.force (Lazy.defer \_ -> (-1)))

twiceNegated :: Number -> Number
twiceNegated x = negate (negate x)

-- | The index folds to a negative constant that Go rejects in an index expression even in a
-- branch that cannot run.
missing :: Maybe Int
missing = maybe (Array.index [] (Lazy.force (Lazy.defer \_ -> (-1)))) (\_ -> Nothing) (Array.index [] 0)

main :: Effect Int
main = pure (negated + negate (-1) + fromMaybe 10 missing + (if twiceNegated 2.0 == 2.0 then 100 else 0))
