module T.MM.Main where

import Prelude

import Data.Array as Array
import Effect (Effect)
import Effect.Console (log)
import T.MM.Classes (heaviest, pretty, summary, tagOf)
import T.MM.Types (Basket(..), Fruit(..))

main :: Effect Unit
main = do
  let fruits = [ Apple 2, Pear { ripeness: 0.75 }, Apple 1, Pear { ripeness: 0.25 } ]
  log (heaviest fruits)
  log (heaviest [ Basket fruits, Basket [ Apple 9 ] ])
  log (heaviest [ 3, 9, -1 ])
  log (heaviest ([] :: Array Int))
  log (tagOf @Fruit <> tagOf @Basket <> tagOf @Int)
  fruits # Array.sort <#> pretty # show # log
  fruits <#> summary # show # log
  log (show fruits)
