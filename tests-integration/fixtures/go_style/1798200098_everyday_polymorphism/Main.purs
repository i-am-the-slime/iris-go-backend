module Fun.Poly where

import Prelude

import Data.Array ((..))
import Data.Foldable (foldMap, intercalate)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Tuple.Nested ((/\), type (/\))
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Prim.RowList as RL
import Data.Reflectable (class Reflectable, reflectType)

newtype Showable = Showable (forall r. (forall a. Show a => a -> r) -> r)

showable :: forall a. Show a => a -> Showable
showable value = Showable \consume -> consume value

renderShowable :: Showable -> String
renderShowable (Showable run) = run show

type Renderer = { render :: forall a. Show a => a -> String, prefix :: String }

bracketed :: Renderer
bracketed = { render: \a -> "[" <> show a <> "]", prefix: "b:" }

useRenderer :: Renderer -> String
useRenderer { render, prefix } = prefix <> render 1 <> render "two" <> render (Just 3.0)

class Shout a where
  shout :: a -> String

instance Shout Int where
  shout n = show n <> "!"
else instance Shout String where
  shout s = s <> "!!"
else instance Show a => Shout a where
  shout a = "generic " <> show a

class Container f where
  describeAll :: forall a. Show a => f a -> String

instance Container Array where
  describeAll items = intercalate "," (items <#> show)

instance Container Maybe where
  describeAll = case _ of
    Just a -> "just " <> show a
    Nothing -> "nothing"

class Keys :: RL.RowList Type -> Constraint
class Keys list where
  keys :: Proxy list -> Array String

instance Keys RL.Nil where
  keys _ = []

instance (IsSymbol label, Keys tail) => Keys (RL.Cons label value tail) where
  keys _ = [ reflectSymbol (Proxy :: Proxy label) ] <> keys (Proxy :: Proxy tail)

recordKeys :: forall row list. RL.RowToList row list => Keys list => { | row } -> Array String
recordKeys _ = keys (Proxy :: Proxy list)

sizeOf :: forall @n. Reflectable n Int => Int
sizeOf = reflectType (Proxy :: Proxy n)

pairWith :: forall a b. Show a => Show b => a -> b -> String
pairWith a b = helper a <> "/" <> helper b
  where
  helper :: forall x. Show x => x -> String
  helper x = "<" <> show x <> ">"

localPolymorphism :: Int -> String
localPolymorphism n = do
  let twice :: forall a. (a -> a) -> a -> a
      twice f = f >>> f
  let wrap :: forall a. a -> Array a
      wrap a = [ a ]
  let describe :: forall a. Show a => a -> String
      describe a = show a <> "#" <> show n
  describe (twice (_ + 1) n) <> describe (twice (_ <> "x") "s") <> describe (wrap true) <> describe (wrap (wrap n))

closureFactory :: Int -> Array (Int -> Int)
closureFactory base = (1 .. 3) <#> makeAdder
  where
  makeAdder offset = \x -> x + offset + base

recursiveLocal :: Int -> Array Int
recursiveLocal n = go n []
  where
  go 0 acc = acc
  go k acc = go (k - 1) (acc <> [ k * multiplier ])
  multiplier = n

recursiveLet :: Int -> Int
recursiveLet n = do
  let
    fib :: Int -> Int
    fib k
      | k < 2 = k
      | otherwise = fib (k - 1) + fib (k - 2)
  fib n

mutualWhere :: Int -> Boolean
mutualWhere n = isEven n
  where
  isEven 0 = true
  isEven k = isOdd (k - 1)
  isOdd 0 = false
  isOdd k = isEven (k - 1)

showBoth :: forall a b. Show a => Show b => Either a b -> a /\ b -> String
showBoth either (a /\ b) = case either of
  Left l -> show l <> show a
  Right r -> show r <> show b

polyCompose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
polyCompose g f = g <<< f

constrainedPipeline :: forall a. Show a => Ord a => Array a -> String
constrainedPipeline = map show >>> intercalate "|" >>> (_ <> "!")

main :: Effect Unit
main = do
  log $ foldMap renderShowable [ showable 1, showable "s", showable [ true ], showable (Just 'c') ]
  log "skipped"
  log "skipped"
  log $ shout 1 <> shout "s" <> shout true <> shout [ 1.5 ]
  log $ describeAll [ 1, 2 ] <> describeAll (Just "x") <> describeAll (Nothing :: Maybe Int)
  log $ show (recordKeys { zeta: 1, alpha: "a", mid: true })
  log $ show (sizeOf @42)
  log $ pairWith 1 "a"
  log $ localPolymorphism 5
  log $ show (closureFactory 100 <@> 1)
  log $ show (recursiveLocal 4)
  log $ show (recursiveLet 20)
  log $ show (mutualWhere 10001)
  log $ showBoth (Left 1 :: Either Int String) (2 /\ "b") <> showBoth (Right "r" :: Either Int String) (2 /\ "b")
  log $ polyCompose show (_ + 1) 41
  log $ constrainedPipeline [ 3, 1 ] <> constrainedPipeline [ "b", "a" ]
