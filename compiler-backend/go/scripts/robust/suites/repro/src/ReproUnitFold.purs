module ReproUnitFold where
import Prelude
import Data.Map as Map
import Data.Tuple (Tuple)
import Effect (Effect)
import Effect.Console (log)
main :: Effect Unit
main = log (show (Map.isEmpty (Map.fromFoldable ([] :: Array (Tuple Unit Unit)))))
