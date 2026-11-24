module T.NumShow where

import Prelude

import Data.Array as Array
import Data.Int as Int
import Data.Number as Number
import Data.Number.Format as Format
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log (show (Array.range 1 200 <#> \i -> Int.toNumber i / 7.0))
  log (show (Array.range 1 60 <#> \i -> Number.pow 2.0 (Int.toNumber i) + 0.5))
  log (show [ 0.000001, 0.0000001, 1.0e-6, 123.0e-20, 1.0e15, 1.0e16, 1.0e17, 9007199254740993.0, 4.35, 0.1 + 0.7 ])
  log (show ([ 3.14159, 1.0e21, 0.000123, -2.5, 1234.5 ] <#> \n -> [ Format.toStringWith (Format.fixed 2) n, Format.toStringWith (Format.precision 3) n, Format.toStringWith (Format.exponential 2) n, Format.toString n ]))
