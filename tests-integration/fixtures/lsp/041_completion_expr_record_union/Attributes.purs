module Yoga.React.DOM.Attributes where

import Yoga.React.DOM.Internal (CSS)

type BaseAttributes = BaseAttributesF ()

type BaseAttributesF :: Row Type -> Row Type
type BaseAttributesF r =
  ( className :: String
  , id :: String
  , title :: String
  , style :: CSS
  | r
  )
