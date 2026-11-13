module Main where

import Prelude


newtype Reader r a = Reader (r -> a)

runReader :: forall r a. Reader r a -> r -> a
runReader (Reader f) = f

describe :: Int -> String
describe count = runReader (asks _.name) { name: "x" } <> show (runReader (asks _.size) { size: count })
  where
  asks = Reader

pairs :: String
pairs = twice (_ + 1) 1 # show # append (twice not true # show)
  where
  twice :: forall a. (a -> a) -> a -> a
  twice f = f <<< f

joined :: String
joined = render 3 <> render "y"
  where
  render :: forall a. Show a => a -> String
  render value = "<" <> show value <> ">"

countdown :: Int -> String
countdown start = show (go show start []) <> show (go identity start [])
  where
  go :: forall a. (Int -> a) -> Int -> Array a -> Array a
  go f n accumulated
    | n <= 0 = accumulated
    | otherwise = go f (n - 1) (accumulated <> [ f n ])

main :: Array String
main = [ describe 2, pairs, joined, countdown 3 ]
