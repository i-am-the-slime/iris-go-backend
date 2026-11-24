module TL.Builders where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant (Variant, case_, default, expand, inj, on, onMatch, match, prj)
import Effect (Effect)
import Effect.Console (log)
import Prim.Row as Row
import Prim.RowList as RL
import Record as Record
import Record.Builder (Builder)
import Record.Builder as Builder
import Type.Proxy (Proxy(..))

-- Fill Maybe fields from defaults
class FillDefaults (rl :: RL.RowList Type) (maybes :: Row Type) (defaults :: Row Type) (out :: Row Type) | rl -> out where
  fillDefaults :: Proxy rl -> Record maybes -> Record defaults -> Builder (Record ()) (Record out)

instance FillDefaults RL.Nil maybes defaults () where
  fillDefaults _ _ _ = identity

instance
  ( IsSymbol label
  , Row.Cons label (Maybe a) _m maybes
  , Row.Cons label a _d defaults
  , FillDefaults tail maybes defaults outTail
  , Row.Cons label a outTail out
  , Row.Lacks label outTail
  ) =>
  FillDefaults (RL.Cons label (Maybe a) tail) maybes defaults out where
  fillDefaults _ maybes defaults = fillDefaults (Proxy @tail) maybes defaults >>> Builder.insert (Proxy @label) chosen
    where
    chosen = Record.get (Proxy @label) maybes # fromMaybe (Record.get (Proxy @label) defaults)

withDefaults
  :: forall maybes rl defaults out
   . RL.RowToList maybes rl
  => FillDefaults rl maybes defaults out
  => Record defaults
  -> Record maybes
  -> Record out
withDefaults defaults maybes = Builder.buildFromScratch (fillDefaults (Proxy @rl) maybes defaults)

-- Sequence a record of Maybe into Maybe record
class SequenceMaybes (rl :: RL.RowList Type) (maybes :: Row Type) (out :: Row Type) | rl -> out where
  sequenceMaybes :: Proxy rl -> Record maybes -> Maybe (Builder (Record ()) (Record out))

instance SequenceMaybes RL.Nil maybes () where
  sequenceMaybes _ _ = Just identity

instance
  ( IsSymbol label
  , Row.Cons label (Maybe a) _m maybes
  , SequenceMaybes tail maybes outTail
  , Row.Cons label a outTail out
  , Row.Lacks label outTail
  ) =>
  SequenceMaybes (RL.Cons label (Maybe a) tail) maybes out where
  sequenceMaybes _ maybes = do
    rest <- sequenceMaybes (Proxy @tail) maybes
    value <- Record.get (Proxy @label) maybes
    pure (rest >>> Builder.insert (Proxy @label) value)

allPresent :: forall maybes rl out. RL.RowToList maybes rl => SequenceMaybes rl maybes out => Record maybes -> Maybe (Record out)
allPresent maybes = sequenceMaybes (Proxy @rl) maybes <#> Builder.buildFromScratch

-- Field names
class FieldNames (rl :: RL.RowList Type) where
  fieldNames :: Proxy rl -> Array String

instance FieldNames RL.Nil where
  fieldNames _ = []

instance (IsSymbol label, FieldNames tail) => FieldNames (RL.Cons label ty tail) where
  fieldNames _ = fieldNames (Proxy @tail) # Array.cons (reflectSymbol (Proxy @label))

fieldNamesOf :: forall @row rl. RL.RowToList row rl => FieldNames rl => Array String
fieldNamesOf = fieldNames (Proxy @rl)

-- Variant helpers with VTA
injAs :: forall @label a r1 r2. IsSymbol label => Row.Cons label a r1 r2 => a -> Variant r2
injAs = inj (Proxy @label)

onLabel :: forall @label a b r1 r2. IsSymbol label => Row.Cons label a r1 r2 => (a -> b) -> (Variant r1 -> b) -> Variant r2 -> b
onLabel = on (Proxy @label)

type Small = (circle :: Number, square :: Int)
type Big = (circle :: Number, square :: Int, label :: String)

describeBig :: Variant Big -> String
describeBig = case_
  # onLabel @"circle" (\r -> "circle r=" <> show r)
  # onLabel @"square" (\s -> "square s=" <> show s)
  # onLabel @"label" (\l -> "label " <> l)

describeWithOnMatch :: Variant Big -> String
describeWithOnMatch = onMatch
  { circle: \r -> "matched circle " <> show r }
  (default "other")

describeMatch :: Variant Small -> String
describeMatch = match { circle: \r -> "m circle " <> show r, square: \s -> "m square " <> show s }

main :: Effect Unit
main = do
  let config = withDefaults { port: 8080, host: "localhost", debug: false } { port: Just 3000, host: Nothing, debug: Just true }
  log (show config)
  log (show (allPresent { a: Just 1, b: Just "two" }))
  log (show (allPresent { a: Just 1, b: (Nothing :: Maybe String) }))
  log (show (fieldNamesOf @(zeta :: Int, alpha :: String, mid :: Boolean)))
  log (show (fieldNamesOf @()))
  let small = injAs @"square" 4 :: Variant Small
  let smallCircle = inj (Proxy :: Proxy "circle") 1.5 :: Variant Small
  let big = expand small :: Variant Big
  log (describeBig big)
  log (describeBig (expand smallCircle))
  log (describeBig (injAs @"label" "hello"))
  log (describeWithOnMatch big)
  log (describeWithOnMatch (expand smallCircle))
  log (describeMatch small)
  log (show small)
  log (show big)
  log (show (injAs @"label" "x" :: Variant Big))
  log (show (small == small))
  log (show (small == smallCircle))
  log (show (expand small == (injAs @"square" 4 :: Variant Big)))
  log (show (prj (Proxy @"square") small :: Maybe Int))
  log (show (prj (Proxy @"circle") small :: Maybe Number))
  log (show (compare small smallCircle))
  [ small, smallCircle ] <#> describeMatch # show # log
