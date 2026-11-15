module ReproCaseMapping where
import Prelude
import Data.String (toLower, toUpper)
import Effect (Effect)
import Effect.Console (log)
-- Full Unicode case mappings: SpecialCasing's one-to-many mappings and Final_Sigma.
main :: Effect Unit
main = do
  log (toUpper "straße ﬁ ŉ ǰ ΐ ᾳ")
  log (toLower "İstanbul ΟΔΟΣ ΣΟΦΟΣ. ΑΣ́")
  log (toUpper "plain ascii" <> toLower "PLAIN ASCII")
