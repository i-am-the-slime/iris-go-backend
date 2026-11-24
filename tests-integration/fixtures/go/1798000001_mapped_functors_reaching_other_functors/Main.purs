module Main where

import Prelude

import Data.Foldable (foldl)
import Data.Int (toNumber)

newtype Pull a = Pull (Unit -> a)

instance Functor Pull where
  map change (Pull run) = Pull \_ -> change (run unit)

data Step a = Done | Emit (Array a) (Stream a)

newtype Stream a = Stream (Pull (Step a))

instance Functor Stream where
  map change stream = mapChunks (map change) stream

mapChunks :: forall a b. (Array a -> Array b) -> Stream a -> Stream b
mapChunks change (Stream pull) = Stream (pull <#> changeStep)
  where
  changeStep Done = Done
  changeStep (Emit chunk rest) = Emit (change chunk) (mapChunks change rest)

range :: Int -> Int -> Stream Int
range from to
  | from >= to = Stream (Pull \_ -> Done)
  | otherwise = Stream (Pull \_ -> Emit [ from, from + 1 ] (range (from + 2) to))

fold :: forall a b. (b -> a -> b) -> b -> Stream a -> b
fold step initial (Stream (Pull run)) = case run unit of
  Done -> initial
  Emit chunk rest -> fold step (foldl step initial chunk) rest

main :: Array String
main =
  [ show (range 0 10 <#> toNumber <#> (_ * 1.5) # fold (+) 0.0)
  , range 0 4 <#> show <#> ("tick " <> _) # fold (\text tick -> text <> tick <> ";") ""
  ]
