module Main where

import Prelude
import Data.Exists (Exists, mkExists, runExists)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Unfoldable1 (class Unfoldable1, unfoldr1)
import Effect (Effect)
import Journal (log)

type Step a b = b -> Tuple a (Maybe b)

data Call a b = Call (Step a b) b

newtype Generated a = Generated (Exists (Call a))

instance Unfoldable1 Generated where
  unfoldr1 f seed = Generated (mkExists (Call f seed))

unwrapped :: forall a r. (forall b. Step a b -> b -> r) -> Generated a -> r
unwrapped f (Generated e) = runExists (\(Call g seed) -> f g seed) e

run :: forall u a. Unfoldable1 u => Generated a -> u a
run = unwrapped eRun
  where
  eRun :: forall b. Step a b -> b -> u a
  eRun f seed = unfoldr1 f seed

once :: forall a. a -> Generated a
once a = unfoldr1 (const (Tuple a Nothing)) unit

listed :: Int -> Array Int
listed = run <<< once

main :: Effect Unit
main = log (show (listed 9))
