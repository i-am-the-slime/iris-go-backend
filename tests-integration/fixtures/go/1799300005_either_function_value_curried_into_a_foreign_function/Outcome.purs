module Outcome (outcomeImpl) where

import Data.Either (Either)
import Effect.Uncurried (EffectFn3)

foreign import outcomeImpl :: EffectFn3 (Int -> String -> Either String Int) (Either String Int) Boolean (Either String Int)
