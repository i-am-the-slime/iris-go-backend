module Main where

data Maybe a = Just a | Nothing

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe _ (Just a) = a
fromMaybe a Nothing = a

apply :: forall a b. (a -> b) -> a -> b
apply f a = f a

infixr 0 apply as #

fart :: String
fart = "Heinz"

-- space-triggered: source line has trailing space
ex1 :: String
ex1 = do
  let fallback = "fb"
  Just "Hello" # fromMaybe 
--                          !
