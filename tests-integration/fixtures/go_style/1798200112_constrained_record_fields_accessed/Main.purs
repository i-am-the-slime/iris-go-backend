module Repro.R12 where

import Prelude

import Effect (Effect)
import Effect.Console (log)

type Renderer = { render :: forall a. Show a => a -> String }

bracketed :: Renderer
bracketed = { render: \a -> "[" <> show a <> "]" }

useRenderer :: Renderer -> String
useRenderer renderer = renderer.render 1 <> renderer.render "two"

main :: Effect Unit
main = log (useRenderer bracketed)
