module Repro.NewtypeEndoUnwrap where

import Prelude

import Data.Foldable (foldMap)
import Data.Monoid.Endo (Endo(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = log (show (unwrap (foldMap (\x -> Endo (\acc -> acc * 10 + x)) [ 1, 2, 3 ]) 0))
