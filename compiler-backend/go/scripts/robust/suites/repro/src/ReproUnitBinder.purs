module ReproUnitBinder where
import Prelude
import Effect (Effect)
import Effect.Console (log)
check :: forall a. Eq a => { actual :: a, expected :: a } -> Effect Unit
check { actual, expected } = unless (actual == expected) (log "differ")
main :: Effect Unit
main = do
  actual <- pure unit
  check { actual, expected: unit }
