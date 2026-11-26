module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, foldr, for_, maximum)
import Data.Generic.Rep (class Generic, Constructor, NoArguments, Sum(..), from)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Ord (comparing)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Tuple.Nested ((/\))
import Effect (Effect, foreachE)
import Effect.Console (log)
import Prim.Row as Row
import Prim.RowList as RowList
import Record as Record
import Type.Proxy (Proxy(..))

data Numbered :: Int -> Type -> Type
data Numbered number value

data Colour = Coral | Tang | Butter | Guac

derive instance Generic Colour _

type Cell = { x :: Numbered 1 Int, y :: Numbered 2 Int, colour :: Numbered 4 Colour, name :: Numbered 3 String }

type Writer message = { number :: Int, wireType :: Int, write :: message -> Effect Unit }

class Value value where
  wireTypeOf :: Proxy value -> Int
  shown :: value -> String

instance Value Int where
  wireTypeOf _ = 0
  shown = show

instance Value String where
  wireTypeOf _ = 2
  shown name = "\"" <> name <> "\""

instance Value Colour where
  wireTypeOf _ = 0
  shown colour = show (indexOf (from colour))

-- | The position of an enumeration's constructor, worked out from its generic representation.
class Indexed rep where
  indexOf :: rep -> Int
  countOf :: Proxy rep -> Int

instance Indexed (Constructor name NoArguments) where
  indexOf _ = 0
  countOf _ = 1

instance (Indexed left, Indexed right) => Indexed (Sum left right) where
  indexOf = case _ of
    Inl left -> indexOf left
    Inr right -> countOf (Proxy :: Proxy left) + indexOf right
  countOf _ = countOf (Proxy :: Proxy left) + countOf (Proxy :: Proxy right)

class Writers :: RowList.RowList Type -> Row Type -> Constraint
class Writers list plain | list -> plain where
  writersOf :: Proxy list -> Array (Writer (Record plain))

instance Writers RowList.Nil () where
  writersOf _ = []

else instance
  ( IsSymbol label
  , Reflectable number Int
  , Value value
  , Row.Cons label value tail plain
  , Row.Lacks label tail
  , Writers rest tail
  ) =>
  Writers (RowList.Cons label (Numbered number value) rest) plain where
  writersOf _ = Array.cons { number, wireType, write } (writersOf (Proxy :: Proxy rest) <#> widened)
    where
    number = reflectType (Proxy :: Proxy number)
    wireType = wireTypeOf (Proxy :: Proxy value)
    write message = log (reflectSymbol (Proxy :: Proxy label) <> " = " <> shown (Record.get (Proxy :: Proxy label) message))
    widened writer = writer { write = \message -> writer.write (Record.delete (Proxy :: Proxy label) message) }

-- | What a message's codec works out once: which wire type each number has, the writers in the
-- | order of their numbers and the largest number.
type Codec message = { wireTypes :: Array Int, largest :: Int, write :: message -> Effect Unit, numbers :: Array Int }

codecOf :: forall fields list plain. RowList.RowToList fields list => Writers list plain => Proxy (Record fields) -> Codec (Record plain)
codecOf _ = { wireTypes, largest, write, numbers }
  where
  writers = writersOf (Proxy :: Proxy list)
  largest = writers <#> _.number # maximum # fromMaybe 0
  wireTypes = foldl noted (Array.replicate (largest + 1) (-1)) writers
  noted table { number, wireType } = Array.updateAt number wireType table # fromMaybe table
  descending = writers # Array.sortBy (flip (comparing _.number))
  numbers = foldr (\{ number } numbered -> numbered <> [ number ]) [] descending
  write message = foreachE (Array.reverse descending) \writer -> writer.write message

main :: Effect Unit
main = do
  log (show codec.wireTypes)
  log (show codec.largest)
  log (show codec.numbers)
  log (show (Array.updateAt 9 1 codec.wireTypes))
  log (show (Array.mapWithIndex (\index wireType -> index /\ wireType) codec.wireTypes))
  for_ cells codec.write
  where
  codec = codecOf (Proxy :: Proxy Cell)
  cells = Array.range 0 3 <#> \n -> { x: n, y: n * 2, colour: colours n, name: "cell " <> show n }
  colours n = case n of
    0 -> Coral
    1 -> Tang
    2 -> Butter
    _ -> Guac
