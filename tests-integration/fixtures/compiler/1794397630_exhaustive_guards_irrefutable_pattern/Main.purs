module Main where

data Maybe a = Just a | Nothing

newtype Wrapped = Wrapped { inner :: Int }

data Pair a b = Pair a b

wrap :: Int -> Wrapped
wrap inner = Wrapped { inner }

pair :: forall a. a -> Pair a a
pair a = Pair a a

newtypeGuard :: Maybe Int -> Int
newtypeGuard = case _ of
  Just n | Wrapped { inner } <- wrap n -> inner
  Nothing -> 0

singleConstructorGuard :: Maybe Int -> Int
singleConstructorGuard = case _ of
  Just n | Pair a _ <- pair n -> a
  Nothing -> 0

recordGuard :: Maybe Int -> Int
recordGuard = case _ of
  Just n | { value } <- { value: n } -> value
  Nothing -> 0

refutableGuard = case _ of
  Just n | Just m <- Just n -> m
  Nothing -> 0
