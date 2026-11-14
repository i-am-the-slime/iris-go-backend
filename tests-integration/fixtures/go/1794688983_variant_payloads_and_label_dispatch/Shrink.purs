module Record.Studio.Shrink (shrink) where

import Prelude
import Prim.Row (class Union)
import Prim.RowList as RL
import Data.Symbol (class IsSymbol, reflectSymbol)
import Type.Proxy (Proxy(..))

foreign import shrinkImpl :: forall r1 r2. Array String -> Record r1 -> Record r2

class Keys :: RL.RowList Type -> Constraint
class Keys list where
  keysOf :: Proxy list -> Array String

instance Keys RL.Nil where
  keysOf _ = []

instance (IsSymbol label, Keys rest) => Keys (RL.Cons label a rest) where
  keysOf _ = [ reflectSymbol (Proxy :: Proxy label) ] <> keysOf (Proxy :: Proxy rest)

shrink :: forall a b r list. Union b r a => RL.RowToList b list => Keys list => { | a } -> { | b }
shrink = shrinkImpl (keysOf (Proxy :: Proxy list))
