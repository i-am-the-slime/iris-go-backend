module Main where

import Prelude

import Data.Foldable (sum)
import Effect (Effect)
import Journal (log)
import Foreign.Object (Object)
import Foreign.Object as Object
import Unsafe.Coerce (unsafeCoerce)

type Scores = { alice :: Int, bob :: Int, carol :: Int }

asRecord :: Object Int -> Scores
asRecord = unsafeCoerce

scoresOf :: Int -> Scores
scoresOf n = { alice: n, bob: n * 2, carol: n * 3 }

main :: Effect Unit
main = do
  let scores = Object.fromHomogeneous (scoresOf 4)
  log (show (asRecord scores).bob)
  log (show (asRecord (scores <#> (_ * 10))))
  log (show (Object.size scores))
  log (show (sum scores))
  log (show (Object.keys scores))
