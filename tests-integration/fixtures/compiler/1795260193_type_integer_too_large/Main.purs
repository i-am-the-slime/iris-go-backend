module Main where

import Prim.Int (class Add, class Mul)
import Type.Proxy (Proxy(..))

literal :: Proxy 170141183460469231731687303715884105728
literal = Proxy

addOverflow :: forall sum. Add 170141183460469231731687303715884105727 1 sum => Proxy sum
addOverflow = Proxy

mulOverflow
  :: forall product
   . Mul 100_000_000_000_000_000_000 100_000_000_000_000_000_000 product
  => Proxy product
mulOverflow = Proxy

forceSolve =
  { addOverflow
  , mulOverflow
  }
