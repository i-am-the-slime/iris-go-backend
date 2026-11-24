module TL.OmCtx where

import Prelude

import Control.Monad.Reader.Class (asks)
import Control.Parallel (parallel, sequential)
import Data.Either (Either(..))
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Aff (Aff, throwError, error, Fiber, joinFiber)
import Effect.Aff as Aff
import Effect.Class.Console (log)
import Yoga.Om (Om, expandCtx, expand, fromAff, inParallel, race, delay, launchOm, runOm, runReader, sequenceOmRecord, widenCtx, throw, runOmRecord)

getName :: forall err. Om { name :: String } err String
getName = asks _.name

getPort :: forall err. Om { port :: Int } err Int
getPort = asks _.port

failing :: forall err. Om { port :: Int } (portBad :: Int | err) Int
failing = do
  port <- getPort
  throw { portBad: port }

describe :: Om { name :: String, port :: Int } () String
describe = do
  name <- getName # expandCtx
  port <- getPort # expandCtx
  pure (name <> ":" <> show port)

withExtra :: Om {} () String
withExtra = getName # widenCtx { name: "extra" } <#> (_ <> "!")

slow :: forall err. Int -> String -> Om { name :: String } err String
slow ms label = delay (Milliseconds (show ms # const (toNumber ms))) $> label
  where
  toNumber n = if n == 0 then 0.0 else 1.0 * (if n > 10 then 20.0 else 1.0)

affFail :: Om {} () Int
affFail = fromAff (throwError (error "aff failed"))

main :: Effect Unit
main = do
  fiber <- launchOm { name: "srv", port: 80 } { exception: \e -> pure ("exc " <> Aff.message e) } describe
  Aff.launchAff_ do
    first <- joinFiber fiber
    log first
    r1 <- runOm {} { exception: \_ -> pure "exc" } withExtra
    log r1
    r2 <- runOm { port: 7, other: unit } { exception: \_ -> pure (-1), portBad: \p -> pure (p * 100) } ((failing :: Om { port :: Int } (portBad :: Int) Int) # expand :: Om { port :: Int, other :: Unit } (portBad :: Int) Int)
    log (show r2)
    all <- runOm { name: "par" } { exception: \_ -> pure [] } (inParallel [ slow 20 "a", slow 1 "b", getName ])
    log (show all)
    winner <- runOm { name: "race" } { exception: \_ -> pure "none" } (race [ slow 50 "slowpoke", slow 1 "fast" ])
    log winner
    afail <- runOm {} { exception: \e -> pure (-7) } affFail
    log (show afail)
    record <- runOm { name: "rec", port: 1 } { exception: \_ -> pure { name: "?", port: -1 } } (sequenceOmRecord { name: (getName :: Om { name :: String } () String), port: (getPort :: Om { port :: Int } () Int) })
    log (show record)
    record2 <- runOmRecord { name: "rec2", port: 2 } { exception: \_ -> pure { n: "?", p: -1 } } { n: (getName :: Om { name :: String } () String), p: (getPort :: Om { port :: Int } () Int) }
    log (show record2)
    either <- runReader { port: 3 } failing
    log (case either of
      Left _ -> "left"
      Right n -> show n)
