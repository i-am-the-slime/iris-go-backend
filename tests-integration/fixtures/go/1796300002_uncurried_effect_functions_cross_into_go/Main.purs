module Main where

import Prelude

import Effect (Effect)
import Effect.Ref as Ref
import Effect.Uncurried (mkEffectFn1, mkEffectFn2, mkEffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)
import Routes (builtIn, call, noReply, serve)

main :: Effect (Array String)
main = do
  seen <- Ref.new []
  let remember text = Ref.modify_ (_ <> [ text ]) seen
  call (mkEffectFn3 \first second _ -> remember (first <> second))
  serve
    { path: "/hello"
    , handle: mkEffectFn3 \name body _ -> remember (name <> ": " <> body)
    , done: mkEffectFn1 \path -> remember ("done " <> path)
    , prefixed: \prefix -> mkEffectFn2 \text _ -> remember (prefix <> text)
    }
  runEffectFn3 builtIn.handle "built" "in" noReply
  serve (builtIn { handle = mkEffectFn3 \name _ _ -> remember ("updated " <> name) })
  runEffectFn1 builtIn.done builtIn.path
  runEffectFn2 (builtIn.prefixed "q") "y" noReply
  let partly = builtIn.prefixed "r"
  runEffectFn2 partly "z" noReply
  let handle = builtIn.handle
  runEffectFn3 handle "kept" "aside" noReply
  case builtIn of
    { handle: matched } -> runEffectFn3 matched "matched" "too" noReply
  Ref.read seen
