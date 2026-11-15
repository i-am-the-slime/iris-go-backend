module Main where

import Prelude

import Data.Lazy (Lazy, defer, force)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)

newtype Stream a = Stream (Lazy (Tuple a (Maybe (Stream a))))

countdown :: Int -> Stream Int
countdown n = Stream (defer \_ -> Tuple n (if n <= 0 then Nothing else Just (countdown (n - 1))))

head :: forall a. Stream a -> a
head (Stream cell) = fst (force cell)

tail :: forall a. Stream a -> Maybe (Stream a)
tail (Stream cell) = snd (force cell)

tails :: forall a. Stream a -> Stream (Stream a)
tails stream = Stream (defer \_ -> Tuple stream (map tails (tail stream)))

main :: Array String
main = [ show (head (countdown 3)), show (map head (tail (countdown 3))), show (head (head (tails (countdown 2)))) ]
