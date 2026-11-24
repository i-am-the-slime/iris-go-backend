module Fun.Async where

import Prelude

import Control.Monad.Error.Class (throwError, try, catchError)
import Control.Monad.Reader (ask, asks)
import Control.Monad.Rec.Class (Step(..), tailRecM)
import Control.Parallel (parTraverse, parallel, sequential)
import Data.Array (range)
import Data.Either (Either(..), either)
import Data.Foldable (for_, foldM)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Data.Traversable (for, traverse)
import Effect (Effect)
import Effect.Aff (Aff, delay, launchAff_, attempt, forkAff, joinFiber, message)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception (error)
import Effect.Ref as Ref
import Yoga.Om (Om)
import Yoga.Om as Om

type Context = { multiplier :: Int, label :: String }

scaleBy :: Int -> Om Context () Int
scaleBy n = asks _.multiplier <#> (_ * n)

describeScaled :: Int -> Om Context () String
describeScaled n = do
  { label } <- ask
  scaled <- scaleBy n
  pure (label <> show scaled)

describeChain :: Int -> Om Context () String
describeChain n = scaleBy n <#> (_ + 1) <#> (_ * 2) <#> show <#> (_ <> "!")

describeChainMap :: Int -> Om Context () String
describeChainMap n = map (_ <> "!") (map show (map (_ * 2) (map (_ + 1) (scaleBy n))))

failing :: Int -> Om Context (notFound :: String) Int
failing n
  | n > 2 = Om.throw { notFound: "too big " <> show n }
  | otherwise = pure n

countLoopOm :: Int -> Om Context () Int
countLoopOm limit = tailRecM step 0
  where
  step i
    | i >= limit = pure (Done i)
    | otherwise = pure (Loop (i + 1))

countLoopAff :: Int -> Aff Int
countLoopAff limit = tailRecM step 0
  where
  step i
    | i >= limit = pure (Done i)
    | otherwise = pure (Loop (i + 1))

recursiveAff :: Int -> Int -> Aff Int
recursiveAff acc n
  | n <= 0 = pure acc
  | otherwise = do
      next <- pure (acc + n)
      recursiveAff next (n - 1)

main :: Effect Unit
main = launchAff_ do
  first <- pure 3 <#> (_ + 1) <#> (_ * 2) <#> show :: Aff String
  log first # liftEffect
  second <- map show (map (_ * 2) (map (_ + 1) (pure 3 :: Aff Int)))
  log second # liftEffect
  third <- (pure 3 :: Aff Int) # map (_ + 1) # map (_ * 2) # map show
  log third # liftEffect
  delay (Milliseconds 5.0)
  results <- for [ 3, 1, 2 ] \n -> do
    delay (Milliseconds (toMillis n))
    pure (n * 10)
  log (show results) # liftEffect
  parallelResults <- parTraverse (\n -> delay (Milliseconds (toMillis (4 - n))) $> n * 100) [ 1, 2, 3 ]
  log (show parallelResults) # liftEffect
  order <- Ref.new [] # liftEffect
  fiberA <- forkAff do
    delay (Milliseconds 20.0)
    Ref.modify_ (_ <> [ "a" ]) order # liftEffect
  fiberB <- forkAff do
    delay (Milliseconds 5.0)
    Ref.modify_ (_ <> [ "b" ]) order # liftEffect
  joinFiber fiberA
  joinFiber fiberB
  Ref.read order >>= show >>> log # liftEffect
  applied <- sequential ((+) <$> parallel (pure 1) <*> parallel (delay (Milliseconds 3.0) $> 2))
  log (show applied) # liftEffect
  failed <- attempt (throwError (error "aff boom") :: Aff Int)
  log (either message show failed) # liftEffect
  caught <- catchError (throwError (error "inner") <#> (_ + 1) <#> show) (\err -> pure (message err <> " handled"))
  log caught # liftEffect
  counted <- countLoopAff 1000000
  log (show counted) # liftEffect
  recursed <- recursiveAff 0 100000
  log (show recursed) # liftEffect
  folded <- foldM (\acc n -> pure (acc + n) :: Aff Int) 0 (range 1 100000)
  log (show folded) # liftEffect
  let context = { multiplier: 7, label: "x=" }
  omResults <- for [ 1, 2 ] \n -> describeScaled n # Om.runOm context { exception: \e -> pure (message e) }
  log (show omResults) # liftEffect
  chainResults <- traverse (describeChain >>> Om.runOm context { exception: \e -> pure (message e) }) [ 1, 2 ]
  log (show chainResults) # liftEffect
  chainResults2 <- traverse (describeChainMap >>> Om.runOm context { exception: \e -> pure (message e) }) [ 1, 2 ]
  log (show chainResults2) # liftEffect
  handled <- for [ 1, 5 ] \n -> failing n <#> show # Om.runOm context
    { exception: \e -> pure ("exception " <> message e)
    , notFound: \text -> pure ("notFound " <> text)
    }
  log (show handled) # liftEffect
  omLoop <- countLoopOm 1000000 # Om.runOm context { exception: \_ -> pure (-1) }
  log (show omLoop) # liftEffect
  omParallel <- Om.inParallel [ scaleBy 1, Om.delay (Milliseconds 5.0) *> scaleBy 2, scaleBy 3 ] # Om.runOm context { exception: \_ -> pure [] }
  log (show omParallel) # liftEffect
  omRace <- Om.race [ Om.delay (Milliseconds 30.0) *> pure "slow", Om.delay (Milliseconds 1.0) *> pure "fast" ] # Om.runOm context { exception: \_ -> pure "err" }
  log omRace # liftEffect
  omFatal <- (Om.fatal "fatal!" :: Om Context () Int) <#> show # Om.runOm context { exception: \e -> pure (message e) }
  log omFatal # liftEffect
  omTry <- (try (failing 9) <#> case _ of
    Left _ -> "left"
    Right n -> show n) # Om.runOm context { exception: \e -> pure (message e), notFound: \_ -> pure "unhandled" }
  log omTry # liftEffect
  where
  toMillis n = 2.0 * (n # toNumberInt)
  toNumberInt :: Int -> Number
  toNumberInt = case _ of
    1 -> 1.0
    2 -> 2.0
    3 -> 3.0
    _ -> 0.0
