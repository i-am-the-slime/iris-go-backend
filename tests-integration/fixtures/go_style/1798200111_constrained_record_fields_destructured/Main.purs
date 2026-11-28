module Repro.R11 where

import Prelude

import Effect (Effect)
import Effect.Console (log)

type Renderer = { render :: forall a. Show a => a -> String }

bracketed :: Renderer
bracketed = { render: \a -> "[" <> show a <> "]" }

useRenderer :: Renderer -> String
useRenderer { render } = render 1 <> render "two"

main :: Effect Unit
main = log (useRenderer bracketed)
