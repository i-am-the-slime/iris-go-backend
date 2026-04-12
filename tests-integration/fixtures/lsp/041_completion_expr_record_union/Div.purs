module Yoga.React.DOM.HTML.Div where

import Yoga.React.DOM.Attributes (BaseAttributes)
import Yoga.React.DOM.Internal (FFIComponent, FFIComponent_)
import Unsafe.Coerce (unsafeCoerce)

div :: FFIComponent BaseAttributes
div _ _ = unsafeCoerce unit

div_ :: FFIComponent_ BaseAttributes
div_ _ = unsafeCoerce unit
