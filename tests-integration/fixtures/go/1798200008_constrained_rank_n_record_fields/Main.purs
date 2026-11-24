module Main where

import Prelude

type Renderer = { render :: forall a. Show a => a -> String }

bracketed :: Renderer
bracketed = { render: \a -> "[" <> show a <> "]" }

throughPun :: Renderer -> String
throughPun { render } = render 1 <> render "two"

throughAccess :: Renderer -> String
throughAccess renderer = renderer.render 1 <> renderer.render "two"

main :: Array String
main = [ throughPun bracketed, throughAccess bracketed ]
