module Fun.Compose where

import Prelude

import Data.Array (filter, length, reverse, take)
import Data.Foldable (sum)
import Data.Int (toNumber)
import Data.String (joinWith, toUpper)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  let numbers = [ 5, 3, 8, 1, 9, 2 ]
  log $ show (pipelineRight numbers)
  log $ show (pipelineLeft numbers)
  log $ show (pipelineEta numbers)
  log $ show (pipelineLet numbers)
  log $ show (pipelineTopLevel numbers)
  log $ shout "hello" 
  log $ shoutPointFree "hello"
  log $ show (flip (-) 1 10)
  log $ show (map (flip div 3) [ 10, -10, 7 ])
  log $ show (map (_ `div` 2) [ 10, -10, 7, -7 ])
  log $ show (map (_ `mod` 3) [ 10, -10, 7, -7 ])
  log $ show (map (10 `div` _) [ 3, -3, 4 ])
  log $ show (map (const 7) numbers)
  log $ show (map (const <@> 7) numbers)
  log $ show (numbers <#> (_ - 1) >>> (_ * 2) >>> show >>> (_ <> "x"))
  log $ show (numbers <#> ((_ <> "x") <<< show <<< (_ * 2) <<< (_ - 1)))
  log $ show (eightSteps 3)
  log $ show (eightStepsBack 3)
  log $ show (eightStepsEta 3)
  log $ show (average numbers)
  log $ show (applyAll [ (_ + 1), (_ * 2), negate, identity, const 0 ] 5)
  where
  shout = toUpper >>> (_ <> "!")
  shoutPointFree = (_ <> "!") <<< toUpper

pipelineRight :: Array Int -> String
pipelineRight = filter (_ > 2) >>> map (_ * 10) >>> reverse >>> take 3 >>> map show >>> joinWith ","

pipelineLeft :: Array Int -> String
pipelineLeft = joinWith "," <<< map show <<< take 3 <<< reverse <<< map (_ * 10) <<< filter (_ > 2)

pipelineEta :: Array Int -> String
pipelineEta numbers = numbers # filter (_ > 2) # map (_ * 10) # reverse # take 3 # map show # joinWith ","

pipelineLet :: Array Int -> String
pipelineLet numbers = do
  let bigOnes = filter (_ > 2) numbers
  let scaled = bigOnes <#> (_ * 10)
  let firstThree = take 3 (reverse scaled)
  joinWith "," (firstThree <#> show)

pipelineTopLevel :: Array Int -> String
pipelineTopLevel numbers = joinWith "," (firstThree (scaled (bigOnes numbers)) <#> show)
  where
  bigOnes = filter isBig
    where
    isBig n = n > threshold
    threshold = 2
  scaled :: Array Int -> Array Int
  scaled = map (_ * 10)
  firstThree :: forall a. Array a -> Array a
  firstThree = reverse >>> take 3

eightSteps :: Int -> String
eightSteps = (_ + 1) >>> (_ * 2) >>> (_ - 3) >>> negate >>> (_ `mod` 7) >>> show >>> (_ <> "!") >>> toUpper

eightStepsBack :: Int -> String
eightStepsBack = toUpper <<< (_ <> "!") <<< show <<< (_ `mod` 7) <<< negate <<< (_ - 3) <<< (_ * 2) <<< (_ + 1)

eightStepsEta :: Int -> String
eightStepsEta n = n # (_ + 1) # (_ * 2) # (_ - 3) # negate # (_ `mod` 7) # show # (_ <> "!") # toUpper

average :: Array Int -> Number
average numbers = toNumber (sum numbers) / toNumber (length numbers)

applyAll :: Array (Int -> Int) -> Int -> Array Int
applyAll functions n = functions <@> n
