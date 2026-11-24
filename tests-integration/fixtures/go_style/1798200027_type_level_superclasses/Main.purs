module TL.Super where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Effect (Effect)
import Effect.Console (log)
import Prim.Boolean (True)
import Prim.Ordering (LT)
import Type.Proxy (Proxy(..))

class Show a <= Pretty a where
  pretty :: a -> String

instance Pretty Int where
  pretty n = "#" <> show n
else instance Pretty a => Pretty (Maybe a) where
  pretty = case _ of
    Just a -> "some " <> pretty a
    Nothing -> "none"
else instance Show a => Pretty a where
  pretty a = "<" <> show a <> ">"

class Pretty a <= Fancy a where
  fancy :: a -> String

instance Fancy Int where
  fancy n = "*" <> pretty n <> "*" <> show n

useSuper :: forall a. Fancy a => a -> String
useSuper a = fancy a <> " | " <> pretty a <> " | " <> show a

reflectAll :: forall @s @b @o @n. Reflectable s String => Reflectable b Boolean => Reflectable o Ordering => Reflectable n Int => String
reflectAll = reflectType (Proxy @s) <> show (reflectType (Proxy @b)) <> show (reflectType (Proxy @o)) <> show (reflectType (Proxy @n))

main :: Effect Unit
main = do
  log (pretty 5)
  log (pretty (Just (Just 5)))
  log (pretty (Nothing :: Maybe Int))
  log (pretty "str")
  log (pretty [ 1.5 ])
  log (useSuper 3)
  log (reflectAll @"sym" @True @LT @(-9))
