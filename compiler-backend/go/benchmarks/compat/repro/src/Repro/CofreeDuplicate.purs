module Repro.CofreeDuplicate where

import Prelude

import Control.Comonad (duplicate, extract)
import Control.Comonad.Cofree (Cofree, deferCofree, head)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)

countdown :: Int -> Cofree Maybe Int
countdown n = deferCofree \_ -> n /\ (if n <= 0 then Nothing else Just (countdown (n - 1)))

main :: Effect Unit
main = log (show (head (extract (duplicate (countdown 3)))))
