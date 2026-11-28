module Main where

import Prelude

import Control.Monad.List.Trans (ListT, nil, take, zipWith, zipWith')
import Control.Monad.List.Trans as ListT
import Data.Array as Array
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- zips of lists of unequal lengths stop at the shorter"
  log (show (collect (zipWith (+) (counted 3) (counted 5))))
  log (show (collect (zipWith (+) (counted 4) (counted 2))))
  log (show (collect (zipWith (+) (counted 0) (counted 2))))
  log (show (collect (zipWith (\a b -> a * 10 + b) (counted 3) nil)))
  log "-- zips whose step runs in the monad"
  log (show (collect (zipWith' (\a b -> pure (a - b)) (counted 4) (counted 6))))
  log (show (collect (take 2 (zipWith (+) (counted 5) (counted 5)))))
  log "-- zips in the array monad"
  log (show (ListT.foldl (flip Array.cons) [] (zipWith (+) (countedIn 3) (countedIn 2))))
  where
  counted :: Int -> ListT Identity Int
  counted n = take n (ListT.iterate (_ + 1) 1)
  countedIn :: Int -> ListT Array Int
  countedIn n = take n (ListT.iterate (_ + 1) 1)
  collect :: ListT Identity Int -> Array Int
  collect list = un Identity (ListT.foldl (flip Array.cons) [] list) # Array.reverse
