module ReproObjectAnnotation where
import Prelude
import Effect (Effect)
import Effect.Console (log)
import Foreign.Object as O
main :: Effect Unit
main = log (show ((O.singleton :: forall a. String -> a -> O.Object a) "k" 1))
