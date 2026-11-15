module ReproFromFoldable1 where
import Prelude
import Data.Array.NonEmpty as NEA
import Data.String.NonEmpty.CodeUnits as NESCU
import Effect (Effect)
import Effect.Console (log)
main :: Effect Unit
main = log (show (NESCU.fromFoldable1 (NEA.cons' 'a' ['b'])))
