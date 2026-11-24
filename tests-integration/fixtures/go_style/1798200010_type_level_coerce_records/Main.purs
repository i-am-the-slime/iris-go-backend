module TL.Coerce where

import Prelude

import Data.Function.Uncurried (Fn2, Fn3, mkFn2, mkFn3, runFn2, runFn3)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, un, wrap)
import Data.Variant (Variant, inj, match, expand)
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, mkEffectFn1, mkEffectFn2, mkEffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)
import Record as Record
import Safe.Coerce (coerce)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

newtype User = User { name :: String, age :: Int }

derive instance Newtype User _
derive newtype instance Show User

newtype Wrapped a = Wrapped a

derive instance Newtype (Wrapped a) _

type Narrow = { name :: String }
type Wide = { name :: String, age :: Int, email :: String }

narrowRecord :: Wide -> Narrow
narrowRecord = unsafeCoerce

widenVariant :: Variant (a :: Int) -> Variant (a :: Int, b :: String)
widenVariant = unsafeCoerce

showAB :: Variant (a :: Int, b :: String) -> String
showAB = match { a: \i -> "a=" <> show i, b: \s -> "b=" <> s }

addEffect :: EffectFn2 Int Int Int
addEffect = mkEffectFn2 \a b -> pure (a + b)

concat3 :: EffectFn3 String String String String
concat3 = mkEffectFn3 \a b c -> pure (a <> b <> c)

pureAdd :: Fn2 Int Int Int
pureAdd = mkFn2 (+)

pureTriple :: Fn3 Int String Boolean String
pureTriple = mkFn3 \i s b -> show i <> s <> show b

counterIncrement :: Ref.Ref Int -> EffectFn1 Int Unit
counterIncrement ref = mkEffectFn1 \n -> Ref.modify_ (_ + n) ref

-- record of functions coerced to a smaller record
type Api = { greet :: String -> String, shout :: String -> String }

api :: Api
api = { greet: \n -> "hi " <> n, shout: \n -> n <> "!" }

-- newtype over record coerced from record via unsafeCoerce
userFromRecord :: { name :: String, age :: Int } -> User
userFromRecord = unsafeCoerce

-- coerce Array of newtypes
unwrapAll :: Array (Wrapped Int) -> Array Int
unwrapAll = coerce

-- unsafeCoerce a function taking a wide record to take a narrow
greetUser :: { name :: String } -> String
greetUser r = "Hello, " <> r.name

main :: Effect Unit
main = do
  let wide = { name: "Ann", age: 30, email: "a@x" } :: Wide
  log (narrowRecord wide).name
  log (show (narrowRecord wide # _.name))
  log (greetUser (unsafeCoerce wide))
  log (showAB (widenVariant (inj (Proxy @"a") 5)))
  log (showAB (expand (inj (Proxy @"a") 6 :: Variant (a :: Int))))
  sum <- runEffectFn2 addEffect 20 22
  log (show sum)
  joined <- runEffectFn3 concat3 "a" "b" "c"
  log joined
  log (show (runFn2 pureAdd 1 2))
  log (runFn3 pureTriple 7 "x" true)
  ref <- Ref.new 0
  runEffectFn1 (counterIncrement ref) 5
  runEffectFn1 (counterIncrement ref) 6
  Ref.read ref >>= show >>> log
  let user = userFromRecord { name: "Bob", age: 41 }
  log (show user)
  log (show (un User user).age)
  log (show (unwrapAll [ Wrapped 1, Wrapped 2 ]))
  let narrowApi = unsafeCoerce api :: { greet :: String -> String }
  log (narrowApi.greet "you")
  let unrun = runEffectFn2 addEffect :: Int -> Int -> Effect Int
  roundTrip <- runEffectFn2 (mkEffectFn2 unrun) 1 1
  log (show roundTrip)
  log (show (runFn2 (mkFn2 (runFn2 pureAdd)) 3 4))
  let wrappedUser = wrap { name: "C", age: 1 } :: User
  log (show wrappedUser)
  log (show (Record.get (Proxy @"age") (unsafeCoerce wrappedUser :: { age :: Int })))
  log (show (unsafeCoerce (Just 5) :: Maybe Int))
