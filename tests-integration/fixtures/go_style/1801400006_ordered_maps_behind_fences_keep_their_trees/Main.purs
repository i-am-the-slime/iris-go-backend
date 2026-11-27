module Fun.OrderedFences where

import Prelude

import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Array as Array
import Data.Foldable (foldl, for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Map.Internal (Map(..), showTree)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref
import Unsafe.Coerce (unsafeCoerce)

main :: Effect Unit
main = do
  log "-- a queue whose tree the program takes apart"
  log (show (rootKey (drained 15)) <> " " <> show (Map.findMin (drained 15)))
  log "-- a queue shown as the tree it is"
  log (showTree (labelled 7))
  log "-- a queue coerced to another map type on the way"
  log (show (coercedOnTheWay 12))
  log "-- a queue kept in a mutable cell"
  cell <- Ref.new (Map.empty :: Map String Int)
  for_ (Array.range 1 12) \n -> do
    Ref.modify_ (Map.insert (show ((n * 7) `mod` 13)) n) cell
    when (n `mod` 3 == 0) do
      queue <- Ref.read cell
      case Map.findMin queue of
        Just { key } -> Ref.modify_ (Map.delete key) cell
        Nothing -> pure unit
  final <- Ref.read cell
  log (show (Map.findMin final) <> show (Map.findMax final) <> show (Map.size final))
  log "-- a queue kept in an ST cell"
  log (show (inSTCell 20))

drained :: Int -> Map Int Int
drained count = go (foldl (\map n -> Map.insert ((n * 5) `mod` 31) n map) Map.empty (Array.range 1 count))
  where
  go map = case Map.findMin map of
    Just { key } | Map.size map > count / 2 -> go (Map.delete key map)
    _ -> map

rootKey :: Map Int Int -> Int
rootKey = case _ of
  Node _ _ key _ _ _ -> key
  Leaf -> -1

labelled :: Int -> Map Int String
labelled count = foldl step Map.empty (Array.range 1 count)
  where
  step map n = case Map.findMax map of
    Just { key } | n `mod` 3 == 0 -> Map.insert (n * 2) (show n) (Map.delete key map)
    _ -> Map.insert (n * 2) (show n) map

newtype Score = Score Int

coercedOnTheWay :: Int -> Array (Maybe Int)
coercedOnTheWay count = (foldl step { seen: [], map: Map.empty } (Array.range 1 count)).seen
  where
  step { seen, map } n = do
    let grown = Map.insert ((n * 3) `mod` 7) (Score n) map
    let asInts = unsafeCoerce grown :: Map Int Int
    { seen: Array.snoc seen (_.key <$> Map.findMin asInts), map: Map.delete (n `mod` 7) grown }

inSTCell :: Int -> Array Int
inSTCell count = ST.run do
  cell <- STRef.new (Map.empty :: Map Char Int)
  taken <- STRef.new []
  ST.for 0 count \n -> do
    _ <- STRef.modify (Map.insert (letter n) n) cell
    when (n `mod` 4 == 3) do
      queue <- STRef.read cell
      case Map.findMin queue of
        Just { key, value } -> do
          _ <- STRef.modify (Map.delete key) cell
          void (STRef.modify (_ <> [ value ]) taken)
        Nothing -> pure unit
  STRef.read taken
  where
  letter n = case Array.index [ 'q', 'w', 'e', 'r', 't', 'y' ] (n `mod` 6) of
    Just found -> found
    Nothing -> 'x'
