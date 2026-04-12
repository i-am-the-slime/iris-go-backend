module Main where

import Prelude hiding (div)
import Yoga.React.DOM.HTML (div)
import Yoga.React.DOM.Internal (JSX)

testDiv :: JSX
testDiv = div {  } ""
--            !^
