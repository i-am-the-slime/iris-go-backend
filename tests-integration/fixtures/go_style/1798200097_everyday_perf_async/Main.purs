module Fun.PerfAsync where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Control.Monad.State (StateT, evalStateT, modify_, get)
import Data.Array ((..))
import Data.Foldable (for_)
import Effect (Effect, foreachE)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Ref as Ref
import Yoga.Om (Om)
import Yoga.Om as Om

affLoop :: Int -> Aff Int
affLoop n = tailRecM step 0
  where
  step i
    | i >= n = pure (Done i)
    | otherwise = pure (Loop (i + 1))

omLoop :: Int -> Om {} () Int
omLoop n = tailRecM step 0
  where
  step i
    | i >= n = pure (Done i)
    | otherwise = pure (Loop (i + 1))

omBindLoop :: Int -> Int -> Om {} () Int
omBindLoop acc n
  | n <= 0 = pure acc
  | otherwise = do
      next <- pure (acc + 1)
      omBindLoop next (n - 1)

stateLoop :: Int -> StateT Int Effect Int
stateLoop n = tailRecM step 0
  where
  step i
    | i >= n = get <#> Done
    | otherwise = modify_ (_ + 1) $> Loop (i + 1)

main :: Effect Unit
main = do
  ref <- Ref.new 0
  foreachE (1 .. 3000000) \i -> Ref.modify_ (_ + i) ref
  Ref.read ref >>= show >>> log
  evalStateT (stateLoop 3000000) 0 >>= show >>> log
  launchAff_ do
    a <- affLoop 5000000
    log (show a) # liftEffect
    b <- omLoop 3000000 # Om.runOm {} { exception: \_ -> pure (-1) }
    log (show b) # liftEffect
    c <- omBindLoop 0 1000000 # Om.runOm {} { exception: \_ -> pure (-1) }
    log (show c) # liftEffect
