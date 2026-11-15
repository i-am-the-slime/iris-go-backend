module ReproSurrogateHalves where
import Prelude
import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Foldable (fold, foldMap)
import Data.String (Pattern(..), Replacement(..))
import Data.String as S
import Data.String.CodePoints as CP
import Data.String.CodeUnits as CU
import Effect (Effect)
import Effect.Console (log)
main :: Effect Unit
main = do
  let astral = "a𝐀b"
  let high = CU.take 2 astral
  let low = CU.drop 2 astral
  log (show (high <> low == astral))
  log (show (CU.length high) <> " " <> show (CU.length low))
  log (show (map fromEnum (CU.toCharArray high)))
  log (show (CP.length (high <> low)))
  log (show (fold [ high, "", low ] == astral))
  log (show (foldMap identity [ high, low ] == astral))
  log (show (S.joinWith "" [ high, low ] == astral))
  log (show (compare high astral) <> " " <> show (compare "\xDC00" "\xE000") <> " " <> show (compare "\xDC00" astral))
  log (show (CU.fromCharArray (CU.toCharArray astral) == astral))
  log (show (S.split (Pattern "\xD835") astral))
  log (show (S.replaceAll (Pattern "x") (Replacement "") ("\xD835x\xDC00") == "\x1D400"))
  log (show (CU.indexOf (Pattern "\xDC00") astral))
  log (show (Array.length (S.split (Pattern "") astral)))
  log (high <> "|" <> low)
  log ("lone: \xD800 and \xDFFF")
  log (show "\xD800")
