module Main where

import Prelude

type Ops = { double :: Int -> Int, describe :: Int -> String }

opsForLeft :: Ops
opsForLeft = { double: \n -> n * 2, describe: \n -> "n = " <> show n }

opsForRight :: Ops
opsForRight = { double: \n -> n * 2, describe: \n -> "n = " <> show n }

useOps :: Ops -> Array Int -> Array String
useOps ops values = map (\value -> ops.describe (ops.double value)) values

main :: Array String
main = useOps opsForLeft [ 1, 2 ] <> useOps opsForRight [ 3 ]
