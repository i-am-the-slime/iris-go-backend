module TL.RankN where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Reflectable (class Reflectable, reflectType)
import Effect (Effect)
import Effect.Console (log)
import Prim.Int as Int
import Prim.Boolean (True, False)
import Type.Data.Boolean (class And, class Or, class Not, class IsBoolean, reflectBoolean)
import Prim.Ordering (Ordering, LT, EQ, GT)
import Prim.Symbol as Symbol
import Type.Proxy (Proxy(..))

-- Existential via rank-N
newtype Showable = Showable (forall r. (forall a. Show a => a -> r) -> r)

mkShowable :: forall a. Show a => a -> Showable
mkShowable a = Showable \k -> k a

showShowable :: Showable -> String
showShowable (Showable run) = run show

-- Rank-N record of polymorphic functions
type NatTrans = { apply :: forall a. Array a -> Maybe a }

useNat :: NatTrans -> String
useNat nat = show (nat.apply [ 1, 2 ]) <> show (nat.apply [ "x" ]) <> show (nat.apply ([] :: Array Boolean))

-- Class computing a type via fundep and returning a value of it
class DefaultFor (key :: Symbol) (out :: Type) | key -> out where
  defaultFor :: Proxy key -> out

instance DefaultFor "port" Int where
  defaultFor _ = 8080
else instance DefaultFor "host" String where
  defaultFor _ = "localhost"
else instance DefaultFor "tags" (Array String) where
  defaultFor _ = [ "a", "b" ]
else instance DefaultFor key Unit where
  defaultFor _ = unit

defaultOf :: forall @key out. DefaultFor key out => out
defaultOf = defaultFor (Proxy @key)

-- Typelevel booleans
both :: forall @a @b c. And a b c => IsBoolean c => Boolean
both = reflectBoolean (Proxy @c)

either_ :: forall @a @b c. Or a b c => IsBoolean c => Boolean
either_ = reflectBoolean (Proxy @c)

negated :: forall @a c. Not a c => IsBoolean c => Boolean
negated = reflectBoolean (Proxy @c)

-- Symbol comparison
class ShowOrdering (o :: Ordering) where
  showOrdering :: Proxy o -> String

instance ShowOrdering LT where
  showOrdering _ = "LT"

instance ShowOrdering EQ where
  showOrdering _ = "EQ"

instance ShowOrdering GT where
  showOrdering _ = "GT"

compareSymbols :: forall @a @b o. Symbol.Compare a b o => ShowOrdering o => String
compareSymbols = showOrdering (Proxy @o)

-- Int arithmetic
timesPlus :: forall @a @b @c m out. Int.Mul a b m => Int.Add m c out => Reflectable out Int => Int
timesPlus = reflectType (Proxy @out)

compareInts :: forall @a @b o. Int.Compare a b o => ShowOrdering o => String
compareInts = showOrdering (Proxy @o)

intToSym :: forall @n s. Int.ToString n s => IsSymbol s => String
intToSym = reflectSymbol (Proxy @s)

-- Peano-ish recursion: factorial at type level
class Factorial (n :: Int) (out :: Int) | n -> out
instance Factorial 0 1
else instance (Int.Add pred 1 n, Factorial pred predFact, Int.Mul n predFact out) => Factorial n out

factorialOf :: forall @n out. Factorial n out => Reflectable out Int => Int
factorialOf = reflectType (Proxy @out)

-- Local polymorphic constrained helper used at two types
describePair :: Int -> String -> String
describePair n s = render n <> " & " <> render s
  where
  render :: forall a. Show a => a -> String
  render a = "<" <> show a <> ">"

main :: Effect Unit
main = do
  [ mkShowable 1, mkShowable "two", mkShowable [ true ], mkShowable (Just 2.5) ] <#> showShowable # show # log
  log (useNat { apply: Array.head })
  log (useNat { apply: Array.last })
  log (show (defaultOf @"port"))
  log (defaultOf @"host")
  log (show (defaultOf @"tags"))
  log (show (defaultOf @"anything"))
  log (show [ both @True @True, both @True @False, either_ @False @True, negated @True, negated @False ])
  log (compareSymbols @"apple" @"banana")
  log (compareSymbols @"b" @"a")
  log (compareSymbols @"same" @"same")
  log (show (timesPlus @6 @7 @0))
  log (show (timesPlus @3 @(-4) @2))
  log (compareInts @(-3) @2)
  log (intToSym @(-12))
  log (show (factorialOf @5))
  log (describePair 3 "x")
