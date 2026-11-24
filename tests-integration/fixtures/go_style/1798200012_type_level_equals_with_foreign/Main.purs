module TL.Equals where

import Prelude

import Control.Monad.Reader.Class (ask, asks, local)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class.Console (log)
import Prim.TypeError (class Fail, class Warn, Text, Beside, Quote)
import Type.Equality (class TypeEquals, to, from)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)
import Yoga.Om (Om, runOm)

class Summable a where
  total :: a -> Int

instance TypeEquals elem Int => Summable (Array elem) where
  total xs = go 0 0
    where
    go acc i = case indexInt i of
      Nothing -> acc
      Just n -> go (acc + n) (i + 1)
    indexInt i = if i < arrLength then Just (to (unsafeIndexArr xs i)) else Nothing
    arrLength = lengthArr xs

foreign import lengthArr :: forall a. Array a -> Int
foreign import unsafeIndexArr :: forall a. Array a -> Int -> a

class HasDefault a where
  defaultValue :: a

instance HasDefault Int where
  defaultValue = 0
else instance HasDefault String where
  defaultValue = ""
else instance Fail (Beside (Text "No default for ") (Quote a)) => HasDefault a where
  defaultValue = unsafeCoerce unit

class Deprecated a where
  oldName :: a -> String

instance Warn (Text "oldName is deprecated") => Deprecated Int where
  oldName = show

type Repo = { findUser :: Int -> Maybe String, prefix :: String }

lookupName :: Int -> Om { repo :: Repo, depth :: Int } () String
lookupName userId = do
  { repo: { findUser, prefix }, depth } <- ask
  findLater <- asks _.repo.findUser
  nested <- local (\ctx -> ctx { depth = ctx.depth + 1 }) (asks _.depth)
  pure case findUser userId, findLater (userId + 1) of
    Just name, Just next -> prefix <> name <> "," <> next <> " depth=" <> show depth <> "/" <> show nested
    _, _ -> "missing"

fromInt :: forall a. TypeEquals Int a => Int -> a
fromInt = to

main :: Effect Unit
main = launchAff_ do
  log (show (total [ 1, 2, 3, 4 ]))
  log (show (defaultValue :: Int))
  log (show (defaultValue :: String))
  log (oldName 5)
  log (show (fromInt 7 :: Int))
  log (show (from (5 :: Int) :: Int))
  let repo = { findUser: \i -> if i < 10 then Just ("u" <> show i) else Nothing, prefix: ">" }
  result <- runOm { repo, depth: 0 } { exception: \_ -> pure "exc" } (lookupName 3)
  log result
  result2 <- runOm { repo, depth: 0 } { exception: \_ -> pure "exc" } (lookupName 9)
  log result2
