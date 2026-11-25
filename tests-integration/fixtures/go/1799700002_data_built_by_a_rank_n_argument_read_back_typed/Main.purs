module Main where

import Prelude

import Effect (Effect)
import Journal (count, log)

newtype Box a = Box a

derive instance Functor Box

data Await a = Await (Int -> a)

data Emit a = Emit Int a

data Pair a b = Pair a b

unbox :: forall a. Box a -> a
unbox (Box value) = value

awaitEmitted :: forall b c d. (b -> c -> d) -> Await b -> Emit c -> Box d
awaitEmitted combine (Await await) (Emit emitted rest) = Box (combine (await emitted) rest)

shout :: (forall b c d. (b -> c -> d) -> Await b -> Emit c -> Box d) -> Pair Int String -> Box (Unit -> String)
shout zap = go
  where
  go (Pair times name)
    | times > 0 = map (\pair _ -> unbox (go pair) unit) (zap Pair (Await (_ - 1)) (Emit times (name <> "!")))
    | otherwise = Box \_ -> name

main :: Effect Unit
main = do
  times <- count
  log (unbox (shout awaitEmitted (Pair times "apples")) unit)
