module T.ClassHierB where

-- same as ClassHier but uses where-clauses, explicit dictionaries via local helpers and point-free forms
import Prelude

import Data.Array as Array
import Data.Ord (abs)
import Data.Foldable (foldMap, intercalate)
import Data.Maybe (Maybe(..), maybe)
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
fancyLine = render
  where
  render thing = intercalate "" [ label thing, ": ", describe thing, " ", decorate thing ]

newtype Cat = Cat String
data Shape = Circle Number | Square Int | Blob

instance Describe Cat where
  describe (Cat name) = "cat named " <> name
instance Labelled Cat where
  label = const "CAT"
instance Fancy Cat where
  decorate = describe >>> \d -> "~" <> d <> "~"

instance Describe Shape where
  describe (Circle radius) = "circle r=" <> show radius
  describe (Square side) = "square s=" <> show side
  describe Blob = "blob"
instance Labelled Shape where
  label shape = "SHAPE(" <> describe shape <> ")"
instance Fancy Shape where
  decorate = const "*"

instance Describe Int where
  describe = show >>> ("int " <> _)
instance Labelled Int where
  label n | n < 0 = "NEG"
          | otherwise = "POS"
instance Fancy Int where
  decorate n = foldMap (const "!") (Array.range 1 (min 5 (abs n)) # Array.filter (_ > 0))

instance Describe a => Describe (Array a) where
  describe items = "[" <> intercalate ", " (map describe items) <> "]"
instance Labelled a => Labelled (Array a) where
  label = map label >>> intercalate "|"
instance Fancy a => Fancy (Array a) where
  decorate = foldMap decorate

instance Describe a => Describe (Maybe a) where
  describe = maybe "nothing" (describe >>> ("just " <> _))
instance (Describe a, Describe b) => Describe (a /\ b) where
  describe (a /\ b) = describe a <> " & " <> describe b

class HasName :: forall k. k -> Constraint
class HasName a where
  nameOf :: Proxy a -> String

instance HasName Cat where nameOf _ = "Cat"
instance HasName Shape where nameOf _ = "Shape"
instance HasName Int where nameOf _ = "Int"
instance HasName a => HasName (Array a) where nameOf _ = "Array " <> typeName @a

typeName :: forall @a. HasName a => String
typeName = nameOf (Proxy @a)

twice :: forall a. Fancy a => a -> Array String
twice thing = Array.nub (Array.replicate 2 (fancyLine thing))

main :: Effect Unit
main = do
  [ fancyLine (Cat "Tom"), fancyLine (Circle 1.5), fancyLine (Square (-3)), fancyLine (-7), fancyLine [ 1, -2, 3 ], fancyLine [ Circle 0.1, Blob ], fancyLine [ [ Cat "a" ], [ Cat "b", Cat "c" ] ] ]
    # Array.foldMap (\l -> l <> "\n") # Array.singleton # map (\s -> String' s) # \_ -> pure unit
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
  [ fancyLine 1, fancyLine (Cat "z"), fancyLine Blob ] # Array.sort # show # log

newtype String' = String' String
