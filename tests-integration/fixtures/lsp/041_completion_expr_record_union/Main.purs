module Main where

import Prelude hiding (div)
import Yoga.React.DOM.HTML (div, div_)
import Yoga.React.DOM.Internal (JSX)

testDiv :: JSX
testDiv = div {  } ""
--            !^

testUsedFields :: JSX
testUsedFields = div { className: "x",  } ""
--                                     !^

testNoChildren :: JSX
testNoChildren = div_ {  }
--                    !^

openRowFn :: forall r. { name :: String, age :: String | r } -> String
openRowFn _ = ""

testOpenRow :: String
testOpenRow = openRowFn {  }
--                      !^

foreign import styleHelper :: { color :: String, display :: String } -> JSX

testNested :: JSX
testNested = div { style: styleHelper {  } } ""
--                                    !^
