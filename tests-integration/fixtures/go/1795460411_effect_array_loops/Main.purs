module Main (main) where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Array ((..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (class Foldable, foldM, foldl, foldr, for_, sequence_, traverse_)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex, foldlWithIndex, foldrWithIndex, forWithIndex_, traverseWithIndex_)
import Data.Maybe (Maybe(..))
import Data.Traversable (for, traverse)
import Effect (Effect)
import Journal (log)
import Effect.Exception (message, throw, try)
import Effect.Ref as Ref
import Data.Tuple.Nested ((/\))
import Foreign.Object as Object

main :: Effect Unit
main = do
  traversals
  failures
  folds
  log "st"
  log (show (stOrder [ 3, 1, 2 ]))
  log (show (stIndexed [ 10, 20, 30 ]))
  log (show (stTraverse [ 1, 2, 3 ]))
  log (show (stFold [ 1, 2, 3 ]))
  large

traversals :: Effect Unit
traversals = do
  log "for_ effect"
  for_ [ 1, 2, 3 ] \x -> log (show x)
  log "traverse_ effect"
  traverse_ (\x -> log ("t" <> show x)) [ "a", "b" ]
  log "forWithIndex_ effect"
  forWithIndex_ [ "x", "y", "z" ] \index value -> log (show index <> value)
  log "traverseWithIndex_ effect"
  traverseWithIndex_ (\index value -> log (show (index * value))) [ 5, 6 ]
  log "for effect"
  doubled <- for [ 1, 2, 3 ] \x -> do
    log ("visit " <> show x)
    pure (x * 2)
  log (show doubled)
  log "traverse effect"
  shown <- traverse (\x -> show x <$ log ("see " <> show x)) [ 7, 8 ]
  log (show shown)
  log "foldM effect"
  total <- foldM (\accumulator x -> (accumulator + x) <$ log ("add " <> show x)) 0 [ 1, 2, 3, 4 ]
  log (show total)
  arrayTotal <- Array.foldM (\accumulator x -> (accumulator * 10 + x) <$ log ("digit " <> show x)) 0 [ 4, 2 ]
  log (show arrayTotal)
  log "sequence_ effect"
  sequence_ [ log "first", log "second", log "third" ]
  log "nested"
  for_ [ 1, 2 ] \outer -> for_ [ "a", "b" ] \inner -> log (show outer <> inner)
  log "empty"
  for_ ([] :: Array Int) \x -> log (show x)
  emptied <- for ([] :: Array Int) \x -> pure (x + 1)
  log (show emptied)

failures :: Effect Unit
failures = do
  log "throws midway"
  visited <- Ref.new []
  outcome <- try do
    for_ [ 1, 2, 3, 4 ] \x -> do
      Ref.modify_ (_ <> [ x ]) visited
      when (x == 3) (throw "three")
  seen <- Ref.read visited
  log (either message (const "no error") outcome <> " after " <> show seen)
  traversed <- Ref.new []
  traverseOutcome <- try do
    for [ 1, 2, 3 ] \x -> do
      Ref.modify_ (_ <> [ x ]) traversed
      when (x == 2) (throw "two")
      pure x
  traversedSeen <- Ref.read traversed
  log (either message show traverseOutcome <> " after " <> show traversedSeen)
  where
  either :: forall a b c. (a -> c) -> (b -> c) -> Either a b -> c
  either onLeft onRight = case _ of
    Left value -> onLeft value
    Right value -> onRight value

folds :: Effect Unit
folds = do
  log "range"
  for_ (1 .. 4) \x -> log ("r" <> show x)
  log "maybe"
  for_ (Just 9) \x -> log ("just " <> show x)
  for_ (Nothing :: Maybe Int) \x -> log ("nothing " <> show x)
  log "wrapped"
  forWithIndex_ (Wrapped [ "p", "q" ]) \index value -> log (value <> show index)
  traverse_ (\x -> log ("w" <> show x)) (Wrapped [ 4, 5 ])
  wrappedTotal <- foldM (\accumulator x -> (accumulator - x) <$ log ("minus " <> show x)) 100 (Wrapped [ 1, 10 ])
  log (show wrappedTotal)
  log "stops early"
  foldr (\x rest -> if x == 3 then pure unit else log ("upto " <> show x) *> rest) (pure unit) [ 1, 2, 3, 4, 5 ]
  log "reversed"
  foldr (\x rest -> rest *> log ("back " <> show x)) (pure unit) [ 1, 2, 3 ]
  log "left fold"
  foldl (\before x -> before *> log ("left " <> show x)) (log "seed") [ 1, 2 ]
  log "object"
  log (show (Object.lookup "a" (Object.fromFoldableWith (+) [ "a" /\ 1, "b" /\ 2, "a" /\ 30 ])))

large :: Effect Unit
large = do
  log "large"
  log (show (stSum (Array.replicate 1000000 1)))
  incremented <- for (Array.replicate 1000000 2) \x -> pure (x + 1)
  log (show (Array.length incremented))
  counter <- Ref.new 0
  for_ (Array.replicate 1000000 3) \x -> Ref.modify_ (_ + x) counter
  log =<< show <$> Ref.read counter
  largeFold <- foldM (\accumulator x -> pure (accumulator + x)) 0 (Array.replicate 1000000 1)
  log (show largeFold)
  wrappedCounter <- Ref.new 0
  forWithIndex_ (Wrapped (Array.replicate 1000000 1)) \index x -> Ref.modify_ (_ + index * x) wrappedCounter
  log =<< show <$> Ref.read wrappedCounter

newtype Wrapped a = Wrapped (Array a)

derive newtype instance Foldable Wrapped

instance FoldableWithIndex Int Wrapped where
  foldrWithIndex f initial (Wrapped array) = foldrWithIndex f initial array
  foldlWithIndex f initial (Wrapped array) = foldlWithIndex f initial array
  foldMapWithIndex f (Wrapped array) = foldMapWithIndex f array

stOrder :: Array Int -> Array Int
stOrder values = ST.run do
  seen <- STRef.new []
  for_ values \x -> void (STRef.modify (_ <> [ x ]) seen)
  traverse_ (\x -> void (STRef.modify (_ <> [ x * 100 ]) seen)) values
  STRef.read seen

stIndexed :: Array Int -> Array Int
stIndexed values = ST.run do
  seen <- STRef.new []
  forWithIndex_ values \index x -> void (STRef.modify (_ <> [ index + x ]) seen)
  STRef.read seen

stTraverse :: Array Int -> Array String
stTraverse values = ST.run do
  counter <- STRef.new 0
  for values \x -> do
    count <- STRef.modify (_ + 1) counter
    pure (show count <> ":" <> show x)

stFold :: Array Int -> Int
stFold values = ST.run (foldM step 1 values)
  where
  step :: forall r. Int -> Int -> ST r Int
  step accumulator x = pure (accumulator * 2 + x)

stSum :: Array Int -> Int
stSum values = ST.run do
  total <- STRef.new 0
  for_ values \x -> void (STRef.modify (_ + x) total)
  sequence_ (values <#> \_ -> pure unit)
  STRef.read total
