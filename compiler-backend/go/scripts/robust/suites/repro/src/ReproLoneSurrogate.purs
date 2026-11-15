module ReproLoneSurrogate where
import Prelude
import Data.String.CodePoints as CP
import Data.String.CodeUnits as CU
import Effect (Effect)
import Effect.Console (log)
main :: Effect Unit
main = do
  log (show (CP.codePointAt 1 "a\xDC00z"))
  log (show (CU.length "a\xDC00z"))
  log (show (CU.toCharArray "a\xD800"))
