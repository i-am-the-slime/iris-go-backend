module Main where

import Prelude

import Effect (Effect)
import Effect.Uncurried (mkEffectFn3, runEffectFn2, runEffectFn3)
import Server (Routes, installHooks, log, serve)

routes :: Routes
routes =
  { handle: mkEffectFn3 \name body reply -> do
      log (name <> ": " <> body)
      reply ("thanks " <> name)
  , add: \a b -> a * 10 + b
  , each: [ \a b -> log (a <> b), \a b -> log (b <> a) ]
  , settings: { greeting: \word name -> word <> ", " <> name }
  }

main :: Effect Unit
main = do
  runEffectFn3 routes.handle "bob" "yo" log
  log (show (routes.add 3 4))
  log (routes.settings.greeting "hi" "bob")
  serve routes
  hooks <- installHooks
  runEffectFn2 (hooks.route "carol") "hey" log
  log (show (hooks.fold \a b -> a * 10.0 + b))
