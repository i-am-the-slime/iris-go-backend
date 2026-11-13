module Main where

import Prelude

import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Control.Monad.State (State, execState, modify_)
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.String as String

type Interpreter m =
  { emit :: Int -> m Unit
  , measure :: String -> m Int
  }

newtype Scene a = Scene (forall m. Monad m => Interpreter m -> m a)

instance Functor Scene where
  map f (Scene run) = Scene \interpreter -> f <$> run interpreter

instance Apply Scene where
  apply (Scene f) (Scene value) = Scene \interpreter -> f interpreter <*> value interpreter

instance Applicative Scene where
  pure value = Scene \_ -> pure value

instance Bind Scene where
  bind (Scene run) next = Scene \interpreter -> do
    value <- run interpreter
    interpret interpreter (next value)

instance Monad Scene

interpret :: forall m a. Monad m => Interpreter m -> Scene a -> m a
interpret interpreter (Scene program) = program interpreter

emit :: Int -> Scene Unit
emit value = Scene \interpreter -> interpreter.emit value

measure :: String -> Scene Int
measure text = Scene \interpreter -> interpreter.measure text

program :: Scene Int
program = do
  width <- measure "hello"
  emit width
  emit (width * 2)
  pure (width + 1)

recorded :: Int
recorded = ST.run do
  total <- STRef.new 0
  result <- interpret
    { emit: \value -> void (STRef.modify (_ + value) total)
    , measure: \text -> pure (String.length text)
    }
    program
  sum <- STRef.read total
  pure (sum + result)

counted :: Int
counted = execState (interpret { emit: \_ -> modify_ (_ + 1), measure: \_ -> pure 3 } program) 0

measured :: Int
measured = un Identity (interpret { emit: \_ -> pure unit, measure: \text -> Identity (String.length text) } program)

main :: Array Int
main = [ recorded, counted, measured ]
