module Main where

import Prelude

import Effect (Effect)
import Effect.Ref as Ref
import Lifted (Action(..), combineImpl, guardedImpl, modifyImpl, performImpl)

main :: Effect (Array String)
main = do
  seen <- Ref.new ""
  let record label = Ref.modify_ (_ <> label) seen
  performImpl (record "performed ")
  guardedImpl (\_ -> Action (record "handled ")) (Action (record "guarded "))
  combineImpl (\_ _ -> unit) (record "left ") (record "right ")
  combineImpl identity (pure (\_ -> unit)) (record "argument ")
  modifyImpl (\n -> n + 1) (\_ -> unit)
  counted <- performImpl (pure 7)
  log <- Ref.read seen
  pure [ log, show counted ]
