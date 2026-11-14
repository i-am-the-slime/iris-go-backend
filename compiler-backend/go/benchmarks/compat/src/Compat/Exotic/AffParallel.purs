module Compat.Exotic.AffParallel where

import Prelude

import Control.Parallel (parTraverse, parallel, sequential)
import Control.Alt ((<|>))
import Data.Either (Either(..))
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Aff (Aff, attempt, delay, forkAff, joinFiber, killFiber, launchAff_, makeAff, nonCanceler, supervise, try, throwError, bracket, finally)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception (error, message)

work :: Int -> Aff Int
work n = do
  delay (Milliseconds (toNumber' n))
  pure (n * n)
  where
  toNumber' k = if k == 3 then 3.0 else if k == 2 then 2.0 else 1.0

callback :: Int -> Aff Int
callback n = makeAff \done -> do
  done (Right (n + 1))
  pure nonCanceler

main :: Effect Unit
main = launchAff_ do
  results <- parTraverse work [ 3, 1, 2 ]
  log (show results) # liftEffect
  winner <- sequential (parallel (delay (Milliseconds 20.0) $> "slow") <|> parallel (delay (Milliseconds 1.0) $> "fast"))
  log winner # liftEffect
  fiber <- forkAff (work 2)
  joined <- joinFiber fiber
  log (show joined) # liftEffect
  box <- AVar.empty
  _ <- forkAff (delay (Milliseconds 2.0) *> AVar.put "from fiber" box)
  taken <- AVar.take box
  log taken # liftEffect
  failed <- attempt (throwError (error "boom") :: Aff Int)
  log (either' failed) # liftEffect
  sleeper <- forkAff (delay (Milliseconds 1000.0) *> liftEffect (log "never"))
  killFiber (error "cancelled") sleeper
  value <- bracket (pure 10) (\_ -> liftEffect (log "released")) (\n -> pure (n + 1))
  log (show value) # liftEffect
  _ <- try (finally (liftEffect (log "finaliser")) (pure unit))
  next <- callback 41
  log (show next) # liftEffect
  supervised <- supervise (pure "supervised")
  log supervised # liftEffect
  where
  either' = case _ of
    Left e -> "caught " <> message e
    Right n -> show n
