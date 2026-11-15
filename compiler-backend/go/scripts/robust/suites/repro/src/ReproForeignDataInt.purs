module ReproForeignDataInt where
import Prelude
import Effect (Effect)
import Effect.Console (log)
foreign import data Box :: Type -> Type
foreign import makeBox :: forall a. a -> Box a
foreign import eqBoxImpl :: forall a. (a -> a -> Boolean) -> Box a -> Box a -> Boolean
instance Eq a => Eq (Box a) where
  eq = eqBoxImpl eq
main :: Effect Unit
main = log (show ([makeBox 1] == [makeBox 1]))
