module Fun.EffectValues where

import Prelude

import Data.Array (replicate, (..))
import Data.Foldable (sequence_, for_, traverse_, foldl)
import Data.Maybe (Maybe(..))
import Data.Traversable (sequence)
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref
import Effect.Ref (Ref)
import Effect.Unsafe (unsafePerformEffect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)

type Actions = { increment :: Effect Int, report :: Effect Unit, reset :: Effect Unit }

makeActions :: Ref Int -> Actions
makeActions ref =
  { increment: Ref.modify (_ + 1) ref
  , report: Ref.read ref >>= \n -> log ("count " <> show n)
  , reset: Ref.write 0 ref
  }

globalCounter :: Ref Int
globalCounter = unsafePerformEffect (Ref.new 100)

bumpGlobal :: Effect Int
bumpGlobal = Ref.modify (_ + 1) globalCounter

loggedValue :: Int -> Effect Int
loggedValue n = do
  log ("computing " <> show n)
  pure (n * 2)

main :: Effect Unit
main = do
  ref <- Ref.new 0
  let increment = Ref.modify (_ + 1) ref
  _ <- increment
  _ <- increment
  third <- increment
  log (show third)
  let actions = makeActions ref
  sequence_ (replicate 3 actions.increment)
  actions.report
  actions.reset
  actions.report
  let logs = (1 .. 3) <#> \i -> log ("action " <> show i)
  log "built logs"
  sequence_ logs
  sequence_ logs
  let maybeEffect = Just (log "inside maybe")
  for_ maybeEffect identity
  for_ maybeEffect identity
  results <- sequence [ loggedValue 1, loggedValue 2 ]
  log (show results)
  let twice action = action *> action
  twice (log "twice")
  let composed = foldl (*>) (pure unit) (replicate 3 (Ref.modify_ (_ * 2) ref))
  Ref.write 1 ref
  composed
  composed
  Ref.read ref >>= show >>> log
  a <- bumpGlobal
  b <- bumpGlobal
  log (show [ a, b ])
  when false (log "never")
  unless false (log "unless")
  let deferred = whereEffect
  log "before deferred"
  deferred
  deferred
  traverse_ identity [ log "t1", log "t2" ]
  let affAction = liftEffect (log "aff action") :: Aff Unit
  launchAff_ (affAction *> affAction)
  where
  whereEffect = log "where effect"
