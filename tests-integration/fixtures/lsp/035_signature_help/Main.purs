module Main where

data Maybe a = Just a | Nothing

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe _ (Just a) = a
fromMaybe a Nothing = a

map :: forall a b. (a -> b) -> Array a -> Array b
map _ _ = []

life :: Int
life = 42

check :: Int
check = fromMaybe life Nothing
--               &

check2 :: Array Int
check2 = map life []
--           &
