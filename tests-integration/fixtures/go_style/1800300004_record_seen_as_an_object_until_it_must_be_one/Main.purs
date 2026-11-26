module Main where

import Prelude

import Data.Foldable (sum)
import Effect (Effect)
import Effect.Console (log, logShow)
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
  logShow (asRecord scores).bob
  logShow (asRecord (scores <#> (_ * 10)))
  logShow (Object.size scores)
  logShow (sum scores)
  log (show (Object.keys scores))
