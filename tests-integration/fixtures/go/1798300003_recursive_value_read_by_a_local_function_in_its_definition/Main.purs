module Main where

import Prelude

import Effect (Effect)
import Journal (log)

data Step = Emit Int (Unit -> Step) | Stop

andThen :: Step -> (Unit -> Step) -> Step
andThen step next = go step
  where
  go (Emit value rest) = Emit value \_ -> go (rest unit)
  go Stop = next unit

take :: Int -> Step -> Array Int
take 0 _ = []
take _ Stop = []
take count (Emit value rest) = [ value ] <> take (count - 1) (rest unit)

main :: Effect Unit
main = log (show (take 5 ones))
  where
  ones = andThen (Emit 1 \_ -> Stop) \_ -> ones
