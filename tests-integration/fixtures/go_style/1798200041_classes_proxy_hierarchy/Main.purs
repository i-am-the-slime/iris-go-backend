module T.ClassHier where

import Prelude

import Data.Array as Array
import Data.Ord (abs)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

class Describe a where
  describe :: a -> String

class Describe a <= Labelled a where
  label :: a -> String

class Labelled a <= Fancy a where
  decorate :: a -> String

fancyLine :: forall a. Fancy a => a -> String
fancyLine thing = label thing <> ": " <> describe thing <> " " <> decorate thing

newtype Cat = Cat String
data Shape = Circle Number | Square Int | Blob

instance Describe Cat where
  describe (Cat name) = "cat named " <> name
instance Labelled Cat where
  label _ = "CAT"
instance Fancy Cat where
  decorate cat = "~" <> describe cat <> "~"

instance Describe Shape where
  describe = case _ of
    Circle radius -> "circle r=" <> show radius
    Square side -> "square s=" <> show side
    Blob -> "blob"
instance Labelled Shape where
  label shape = "SHAPE(" <> describe shape <> ")"
instance Fancy Shape where
  decorate _ = "*"

instance Describe Int where
  describe n = "int " <> show n
instance Labelled Int where
  label n = if n < 0 then "NEG" else "POS"
instance Fancy Int where
  decorate n = Array.replicate (min 5 (abs n)) "!" # Array.fold

instance Describe a => Describe (Array a) where
  describe items = "[" <> (items <#> describe # Array.intercalate ", ") <> "]"
instance Labelled a => Labelled (Array a) where
  label items = items <#> label # Array.intercalate "|"
instance Fancy a => Fancy (Array a) where
  decorate items = items <#> decorate # Array.fold

instance Describe a => Describe (Maybe a) where
  describe = case _ of
    Nothing -> "nothing"
    Just a -> "just " <> describe a
instance (Describe a, Describe b) => Describe (a /\ b) where
  describe (a /\ b) = describe a <> " & " <> describe b

-- Proxy-based class with VTA helper
class HasName :: forall k. k -> Constraint
class HasName a where
  nameOf :: Proxy a -> String

instance HasName Cat where nameOf _ = "Cat"
instance HasName Shape where nameOf _ = "Shape"
instance HasName Int where nameOf _ = "Int"
instance HasName a => HasName (Array a) where nameOf _ = "Array " <> nameOf (Proxy :: _ a)

typeName :: forall @a. HasName a => String
typeName = nameOf (Proxy :: Proxy a)

-- polymorphic helper used at many types
twice :: forall a. Fancy a => a -> Array String
twice thing = [ fancyLine thing, fancyLine thing ] # Array.nub

main :: Effect Unit
main = do
  log (fancyLine (Cat "Tom"))
  log (fancyLine (Circle 1.5))
  log (fancyLine (Square (-3)))
  log (fancyLine (-7))
  log (fancyLine [ 1, -2, 3 ])
  log (fancyLine [ Circle 0.1, Blob ])
  log (fancyLine [ [ Cat "a" ], [ Cat "b", Cat "c" ] ])
  twice Blob # show # log
  twice 42 # show # log
  log (describe (Just [ 1, 2 ] /\ (Nothing :: Maybe Cat)))
  log (typeName @Cat <> " " <> typeName @(Array (Array Shape)) <> " " <> typeName @Int)
  let fancies = [ fancyLine 1, fancyLine (Cat "z"), fancyLine Blob ]
  fancies # Array.sort # show # log
