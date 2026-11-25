module Main where

import Prelude

import Boundary (keepImpl, repeatImpl)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Effect (Effect)
import Effect.Ref as Ref
import Journal (log)

check :: Int -> ExceptT String Effect Int
check n
  | n > 2 = throwError ("too many: " <> show n)
  | otherwise = pure (n * 10)

main :: Effect Unit
main = do
  calls <- Ref.new 0
  let
    next = do
      n <- Ref.modify (_ + 1) calls
      runExceptT (check n)
  repeated <- repeatImpl 4 next
  log (show repeated)
  handler <- keepImpl check
  chained <- runExceptT (handler 1 >>= \a -> handler (a - 9))
  log (show chained)
  failed <- runExceptT (handler 5)
  log (show failed)
