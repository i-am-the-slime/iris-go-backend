module T.Vta where

import Prelude

import Data.Array as Array
import Data.Enum (class BoundedEnum, enumFromTo, toEnum, cardinality, Cardinality(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))
import Data.Reflectable (class Reflectable, reflectType)

allValues :: forall @a. BoundedEnum a => Array a
allValues = enumFromTo bottom top

countValues :: forall @a. BoundedEnum a => Int
countValues = un Cardinality (cardinality :: Cardinality a)

fieldLabel :: forall @l. IsSymbol l => String
fieldLabel = reflectSymbol (Proxy @l)

labelled :: forall @l a. IsSymbol l => Show a => a -> String
labelled value = fieldLabel @l <> "=" <> show value

twoLabels :: forall @l1 @l2. IsSymbol l1 => IsSymbol l2 => String
twoLabels = fieldLabel @l1 <> "+" <> fieldLabel @l2

reflectInt :: forall @n. Reflectable n Int => Int
reflectInt = reflectType (Proxy @n)

class Describe :: forall k. k -> Constraint
class Describe a where
  describeP :: Proxy a -> String

instance Describe Int where describeP _ = "Int"
instance Describe "sym" where describeP _ = "the symbol"
instance Describe Maybe where describeP _ = "Maybe (HKT)"
instance Describe a => Describe (Array a) where describeP _ = "Array of " <> describe @a

describe :: forall @a. Describe a => String
describe = describeP (Proxy @a)

main :: Effect Unit
main = do
  log (show (allValues @Boolean) <> show (countValues @Boolean) <> show (Array.length (allValues @Char)))
  log (show (mempty @(Array Int)) <> show (bottom @Int) <> show (top @Char # \c -> c == top) <> show @Int 5 <> show (pure @Maybe 1))
  log (show (toEnum @Char 65) <> show (toEnum @Boolean 2))
  log (fieldLabel @"name" <> labelled @"age" 42 <> labelled @"tags" [ "a" ] <> twoLabels @"x" @"y")
  log (show (reflectInt @42 + reflectInt @(-3)))
  log (describe @Int <> ", " <> describe @"sym" <> ", " <> describe @Maybe <> ", " <> describe @(Array (Array Int)))
  log (show (map (_ + 1) (1 /\ 2)))
