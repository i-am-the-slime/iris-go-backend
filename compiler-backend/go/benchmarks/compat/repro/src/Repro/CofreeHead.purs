module Repro.CofreeHead where

import Prelude

import Control.Comonad.Cofree (Cofree, deferCofree, head, tail)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)

countdown :: Int -> Cofree Maybe Int
countdown n = deferCofree \_ -> n /\ (if n <= 0 then Nothing else Just (countdown (n - 1)))

main :: Effect Unit
main = do
  log (show (head (countdown 3)))
  log (show (map head (tail (countdown 3))))
