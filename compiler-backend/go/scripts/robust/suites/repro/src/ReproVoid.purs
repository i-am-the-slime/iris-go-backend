module ReproVoid where
import Prelude
import Data.Either (Either(..))
import Data.Void (Void)
import Effect (Effect)
import Effect.Console (log)
check :: forall a. Eq a => Show a => { actual :: a, expected :: a } -> Effect Unit
check { actual, expected } = unless (actual == expected) (log (show actual))
main :: Effect Unit
main = check { actual: Left 1 :: Either Int Void, expected: Left 1 }
