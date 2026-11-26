module Main where

import Prelude

import Type.Proxy (Proxy(..))

class Count :: Type -> Constraint
class Count n where
  count :: Proxy n -> Int

class Count n <= Positive n

data One
data Twice n
data Succ n

instance Count One where
  count _ = 1

instance Count n => Count (Twice n) where
  count _ = 2 * count (Proxy :: Proxy n)

instance Count n => Count (Succ n) where
  count _ = 1 + count (Proxy :: Proxy n)

instance Positive One
instance Count n => Positive (Twice n)
instance Count n => Positive (Succ n)

reifyPositive :: forall r. Int -> (forall n. Positive n => Proxy n -> r) -> r
reifyPositive 1 use = use (Proxy :: Proxy One)
reifyPositive wanted use = case wanted `mod` 2 of
  0 -> reifyPositive (wanted / 2) twice
  _ -> reifyPositive (wanted - 1) succ
  where
  twice :: forall m. Positive m => Proxy m -> r
  twice _ = use (Proxy :: Proxy (Twice m))

  succ :: forall m. Positive m => Proxy m -> r
  succ _ = use (Proxy :: Proxy (Succ m))

reifyCount :: forall r. Int -> (forall n. Count n => Proxy n -> r) -> r
reifyCount wanted use = reifyPositive wanted use

reifyComposed :: forall r. Int -> (forall n. Count n => Proxy n -> r) -> r
reifyComposed 1 use = use (Proxy :: Proxy One)
reifyComposed wanted use = reifyComposed (wanted - 1) (use <<< succeeded)
  where
  succeeded :: forall m. Proxy m -> Proxy (Succ m)
  succeeded _ = Proxy

described :: forall n. Count n => Proxy n -> String
described proxy = "counted " <> show (count proxy)

main :: Array String
main =
  ([ 1, 6, 37, 1000 ] <#> \wanted -> show (reifyPositive wanted count))
    <> [ reifyCount 12 described, show (reifyComposed 5 count) ]
