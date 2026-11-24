module TL.Chains where

import Prelude

import Data.Symbol (class IsSymbol, reflectSymbol)
import Effect (Effect)
import Effect.Console (log)
import Prim.Boolean (True, False)
import Type.Data.Boolean (class IsBoolean, reflectBoolean)
import Type.Proxy (Proxy(..))

class Is2xxStatus (label :: Symbol) (is2xx :: Boolean) | label -> is2xx

instance Is2xxStatus "ok" True
else instance Is2xxStatus "created" True
else instance Is2xxStatus "noContent" True
else instance Is2xxStatus label False

is2xx :: forall @label b. Is2xxStatus label b => IsBoolean b => Boolean
is2xx = reflectBoolean (Proxy :: Proxy b)

describeStatus :: forall @label b. IsSymbol label => Is2xxStatus label b => IsBoolean b => String
describeStatus = reflectSymbol (Proxy @label) <> " is2xx=" <> show (is2xx @label)

-- chain over Type with catch-all and a method
class Describe a where
  describe :: Proxy a -> String

instance Describe Int where
  describe _ = "Int"
else instance Describe String where
  describe _ = "String"
else instance Describe a => Describe (Array a) where
  describe _ = "Array of " <> describe (Proxy :: Proxy a)
else instance Describe a where
  describe _ = "something else"

describeType :: forall @a. Describe a => String
describeType = describe (Proxy @a)

-- chain with value-level method dispatching on runtime value type
class Render a where
  render :: a -> String

instance Render String where
  render s = "\"" <> s <> "\""
else instance Show a => Render a where
  render = show

-- chain producing a Symbol (ToLabel style)
class ToLabel :: Type -> Symbol -> Constraint
class ToLabel labelOrCode label | labelOrCode -> label

instance ToLabel (Proxy 200) "ok"
else instance ToLabel (Proxy 404) "notFound"
else instance ToLabel (Proxy label) label

labelOf :: forall @labelOrCode label. ToLabel (Proxy labelOrCode) label => IsSymbol label => String
labelOf = reflectSymbol (Proxy @label)

-- type-level If via chain
class IfThenElse (cond :: Boolean) (t :: Symbol) (e :: Symbol) (out :: Symbol) | cond t e -> out
instance IfThenElse True t e t
instance IfThenElse False t e e

successOrError :: forall @label b out. Is2xxStatus label b => IfThenElse b "success" "error" out => IsSymbol out => String
successOrError = reflectSymbol (Proxy @out)

main :: Effect Unit
main = do
  log (describeStatus @"ok")
  log (describeStatus @"created")
  log (describeStatus @"noContent")
  log (describeStatus @"notFound")
  log (describeStatus @"")
  log (show (is2xx @"teapot"))
  log (describeType @Int)
  log (describeType @(Array (Array String)))
  log (describeType @Boolean)
  log (describeType @(Array Number))
  log (render "hi")
  log (render 42)
  log (render [ 1, 2 ])
  log (labelOf @200)
  log (labelOf @404)
  log (labelOf @"created")
  log (successOrError @"ok")
  log (successOrError @"badRequest")
  [ "a", "b" ] <#> render # show # log
