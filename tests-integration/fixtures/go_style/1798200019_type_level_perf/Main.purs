module TL.Perf where

import Prelude

import Data.Array as Array
import Data.Variant (Variant, inj, match)
import Effect (Effect)
import Effect.Console (log)
import Heterogeneous.Folding (class Folding, hfoldl)
import Record.Studio (mapRecord)
import Type.Proxy (Proxy(..))

type Op = Variant (add :: Int, mul :: Int, neg :: Unit, label :: String)

step :: Int -> Op -> Int
step acc = match
  { add: \n -> acc + n
  , mul: \n -> (acc * n) `mod` 1000003
  , neg: \_ -> negate acc
  , label: \s -> acc + 1
  }

data Sum = Sum
instance Folding Sum Int Int Int where
  folding Sum acc n = acc + n

main :: Effect Unit
main = do
  let ops = Array.range 1 2000000 <#> \i -> case i `mod` 4 of
        0 -> inj (Proxy @"add") i
        1 -> inj (Proxy @"mul") 3
        2 -> inj (Proxy @"neg") unit
        _ -> inj (Proxy @"label") "x"
  log (show (Array.foldl step 1 ops))
  let records = Array.range 1 300000 <#> \i -> { a: i, b: i * 2, c: i `mod` 7 }
  log (show (Array.foldl (\acc r -> acc + hfoldl Sum 0 (mapRecord (_ + 1) r)) 0 records))
