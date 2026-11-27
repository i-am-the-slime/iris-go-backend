module Fun.SharedProductMaps where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a pair taken apart twice: both see the map it was made with"
  log (takenApartTwice 5)
  log (takenApartTwice 2)
  log "-- pairs of one map kept in an array"
  log (show (keptInAnArray 4 <#> \(Tuple n table) -> n /\ Map.keys table))
  log "-- a pair that is shown or compared"
  log (show (counted 3))
  log (show (counted 3 == counted 3) <> " " <> show (counted 3 == counted 4))
  log "-- a pair inside a Maybe"
  log (show (Map.keys <<< snd <$> maybePaired 6))
  log "-- a function handed on as a value and also called by a loop"
  let tables = Array.range 1 3 <#> \n -> Map.singleton n n
  log (show (tables <#> (countAll [ 1, 2 ] 0 >>> Map.toUnfoldable) :: Array (Array (Int /\ Int))))
  log (show (Map.toUnfoldable (foldl (\table n -> countAll [ n, n + 1 ] 0 table) Map.empty (Array.range 1 6)) :: Array (Int /\ Int)))
  log "-- a pair whose map is read in order inside the function that made it"
  log (show (Map.keys (fst (orderedPair 7))))

counted :: Int -> Int /\ Map Int Int
counted n = n /\ countAll (Array.range 1 n) 0 Map.empty

takenApartTwice :: Int -> String
takenApartTwice n = do
  let pair = counted n
  let grown = case pair of Tuple _ table -> Map.insert 100 1 table
  let size = case pair of Tuple _ table -> Map.size table
  show size <> " " <> show (Map.keys grown) <> " " <> show (Map.keys (snd pair))

keptInAnArray :: Int -> Array (Int /\ Map Int Int)
keptInAnArray n = do
  let table = countAll (Array.range 1 n) 0 Map.empty
  [ Tuple 1 (Map.insert 50 1 table), Tuple 2 (Map.delete 1 table), Tuple 3 table ]

maybePaired :: Int -> Maybe (Int /\ Map Int Int)
maybePaired n = if n > 3 then Just (counted n) else Nothing

orderedPair :: Int -> Map Int Int /\ Array Int
orderedPair n = do
  let table = countAll (Array.range 1 n) 0 Map.empty
  table /\ Array.fromFoldable (Map.keys table)

-- | Counts the numbers from a position on, one at a time.
countAll :: Array Int -> Int -> Map Int Int -> Map Int Int
countAll numbers position table = case Array.index numbers position of
  Nothing -> table
  Just number -> countAll numbers (position + 1) (Map.insertWith (+) number 1 table)
