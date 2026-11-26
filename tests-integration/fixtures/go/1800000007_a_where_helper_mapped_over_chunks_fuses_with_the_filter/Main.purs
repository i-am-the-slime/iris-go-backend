module Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref as Ref
import Journal (log)

newtype Fallible a = Fallible (Unit -> Effect (Either String a))

run :: forall a. Fallible a -> Effect (Either String a)
run (Fallible action) = action unit

instance Functor Fallible where
  map f (Fallible action) = Fallible \context -> map (map f) (action context)

instance Apply Fallible where
  apply = ap

instance Applicative Fallible where
  pure value = Fallible \_ -> pure (Right value)

instance Bind Fallible where
  bind (Fallible action) next = Fallible \context -> do
    result <- action context
    case result of
      Left problem -> pure (Left problem)
      Right value -> run (next value)

instance Monad Fallible

lift :: forall a. Effect a -> Fallible a
lift action = Fallible \_ -> Right <$> action

data Step = Emit (Array Int) | End

newtype Stream = Stream (Fallible (Fallible Step))

range :: Int -> Int -> Stream
range from to = Stream do
  next <- lift (Ref.new from)
  pure do
    start <- lift (Ref.read next)
    if start >= to then pure End
    else do
      let stop = min to (start + 64)
      lift (Ref.write stop next)
      pure (Emit (Array.range start (stop - 1)))

mapStream :: (Int -> Int) -> Stream -> Stream
mapStream f (Stream open) = Stream do
  pull <- open
  pure (pull <#> case _ of
    Emit chunk -> Emit (map f chunk)
    End -> End)

empty :: Stream
empty = Stream (pure (pure End))

take :: Int -> Stream -> Stream
take count (Stream open)
  | count <= 0 = empty
  | otherwise = Stream do
      pull <- open
      remaining <- lift (Ref.new count)
      pure do
        wanted <- lift (Ref.read remaining)
        if wanted <= 0 then pure End
        else do
          pulled <- pull
          case pulled of
            End -> pure End
            Emit chunk -> do
              let taken = Array.take wanted chunk
              lift (Ref.write (wanted - Array.length taken) remaining)
              pure (Emit taken)

filterStream :: (Int -> Boolean) -> Stream -> Stream
filterStream keep (Stream open) = Stream do
  pull <- open
  pure (pull <#> case _ of
    Emit chunk -> Emit (Array.filter keep chunk)
    End -> End)

forEach :: (Int -> Fallible Unit) -> Stream -> Fallible Unit
forEach f (Stream open) = do
  pull <- open
  foldPulled f pull

foldPulled :: (Int -> Fallible Unit) -> Fallible Step -> Fallible Unit
foldPulled f pull = do
  pulled <- pull
  case pulled of
    End -> pure unit
    Emit chunk -> do
      eachIn chunk f
      foldPulled f pull

eachIn :: Array Int -> (Int -> Fallible Unit) -> Fallible Unit
eachIn chunk f = from 0
  where
  from index = case Array.index chunk index of
    Nothing -> pure unit
    Just element -> do
      f element
      from (index + 1)

oddTriplesSent :: Int -> Effect Int
oddTriplesSent count = do
  sent <- Ref.new 0
  _ <- run (range 0 count # filterStream odd # mapStream tripled # take (count / 4) # forEach \n -> lift (Ref.modify_ (_ + n) sent))
  Ref.read sent
  where
  tripled number = number * 3
  odd number = number `mod` 2 == 1

main :: Effect Unit
main = do
  total <- oddTriplesSent 1000
  log (show total)
