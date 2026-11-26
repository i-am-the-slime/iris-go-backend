module Main where

import Prelude

import Data.Foldable (sum)
import Data.Homogeneous.Record (fromHomogeneous, get, homogeneous, modify)
import Effect (Effect)
import Effect.Console (log)

type Scores = { alice :: Int, bob :: Int, carol :: Int }

scores :: Scores
scores = { alice: 3, bob: 5, carol: 8 }

main :: Effect Unit
main = do
  let homogeneousScores = homogeneous scores
  log (show (fromHomogeneous (homogeneousScores <#> (_ * 10))))
  log (show (get homogeneousScores _.bob))
  log (show (fromHomogeneous (modify homogeneousScores _ { alice = 7 })))
  log (show (sum homogeneousScores))
  log (show ((fromHomogeneous (homogeneousScores <#> show)) :: { alice :: String, bob :: String, carol :: String }))
