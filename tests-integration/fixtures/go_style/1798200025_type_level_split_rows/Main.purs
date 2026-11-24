module TL.Split where

import Prelude

import Data.Array as Array
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant (Variant)
import Data.Variant as Variant
import Effect (Effect)
import Effect.Console (log)
import Prim.Boolean (True, False)
import Prim.Row as Row
import Prim.RowList as RL
import Record.Builder (Builder)
import Record.Builder as Builder
import Type.Proxy (Proxy(..))
import Data.Either (Either(..))

class Is2xxStatus (label :: Symbol) (is2xx :: Boolean) | label -> is2xx

instance Is2xxStatus "ok" True
else instance Is2xxStatus "created" True
else instance Is2xxStatus "noContent" True
else instance Is2xxStatus label False

class SplitResponse (respVariant :: Row Type) (successRow :: Row Type) (errorRow :: Row Type) | respVariant -> successRow errorRow

instance (RL.RowToList respVariant rl, SplitResponseRL rl successRow errorRow) => SplitResponse respVariant successRow errorRow

class SplitResponseRL (rl :: RL.RowList Type) (successRow :: Row Type) (errorRow :: Row Type) | rl -> successRow errorRow

instance SplitResponseRL RL.Nil () ()
instance (Is2xxStatus label is2xx, SplitResponseEntry is2xx label ty tail successRow errorRow) => SplitResponseRL (RL.Cons label ty tail) successRow errorRow

class SplitResponseEntry (is2xx :: Boolean) (label :: Symbol) (ty :: Type) (tail :: RL.RowList Type) (successRow :: Row Type) (errorRow :: Row Type) | is2xx label ty tail -> successRow errorRow

instance (SplitResponseRL tail successTail errorRow, Row.Cons label ty successTail successRow, Row.Lacks label successTail) => SplitResponseEntry True label ty tail successRow errorRow
instance (SplitResponseRL tail successRow errorTail, Row.Cons label ty errorTail errorRow, Row.Lacks label errorTail) => SplitResponseEntry False label ty tail successRow errorRow

-- Labels of a row
class RowLabels (rl :: RL.RowList Type) where
  rowLabels :: Proxy rl -> Array String

instance RowLabels RL.Nil where
  rowLabels _ = []

instance (IsSymbol label, RowLabels tail) => RowLabels (RL.Cons label ty tail) where
  rowLabels _ = Array.cons (reflectSymbol (Proxy @label)) (rowLabels (Proxy @tail))

labelsOf :: forall @row rl. RL.RowToList row rl => RowLabels rl => Array String
labelsOf = rowLabels (Proxy @rl)

type ApiResponse = (ok :: { id :: Int }, notFound :: String, created :: Int, badRequest :: Array String, noContent :: Unit)

splitLabels :: forall @row success error srl erl. SplitResponse row success error => RL.RowToList success srl => RowLabels srl => RL.RowToList error erl => RowLabels erl => { success :: Array String, error :: Array String }
splitLabels = { success: labelsOf @success, error: labelsOf @error }

-- Build handlers that convert error variant into full variant
class BuildErrorHandlers (rl :: RL.RowList Type) (respVariant :: Row Type) (handlers :: Row Type) | rl respVariant -> handlers where
  buildErrorHandlers :: Proxy rl -> Proxy respVariant -> Builder (Record ()) (Record handlers)

instance BuildErrorHandlers RL.Nil respVariant () where
  buildErrorHandlers _ _ = identity

instance
  ( IsSymbol label
  , Row.Cons label ty _r1 respVariant
  , BuildErrorHandlers tail respVariant tailHandlers
  , Row.Cons label (ty -> Variant respVariant) tailHandlers handlers
  , Row.Lacks label tailHandlers
  ) =>
  BuildErrorHandlers (RL.Cons label ty tail) respVariant handlers where
  buildErrorHandlers _ respProxy = buildErrorHandlers (Proxy :: Proxy tail) respProxy >>> Builder.insert (Proxy :: Proxy label) handler
    where
    handler :: ty -> Variant respVariant
    handler val = Variant.inj (Proxy :: Proxy label) val

widenError
  :: forall @respVariant success error errorRL handlers errorRL'
   . SplitResponse respVariant success error
  => RL.RowToList error errorRL
  => BuildErrorHandlers errorRL respVariant handlers
  => RL.RowToList handlers errorRL'
  => Variant.VariantMatchCases errorRL' error (Variant respVariant)
  => Row.Union error () error
  => Variant error
  -> Variant respVariant
widenError = Variant.match (Builder.buildFromScratch (buildErrorHandlers (Proxy @errorRL) (Proxy @respVariant)))

showResp :: Variant ApiResponse -> String
showResp = Variant.case_
  # Variant.on (Proxy @"ok") (\r -> "ok " <> show r.id)
  # Variant.on (Proxy @"notFound") (\s -> "notFound " <> s)
  # Variant.on (Proxy @"created") (\i -> "created " <> show i)
  # Variant.on (Proxy @"badRequest") (\xs -> "badRequest " <> show xs)
  # Variant.on (Proxy @"noContent") (\_ -> "noContent")

classify :: Variant ApiResponse -> Either String String
classify v = Left (showResp v)

main :: Effect Unit
main = do
  log (show (labelsOf @ApiResponse))
  let split = splitLabels @ApiResponse
  split # _.success # show # log
  split # _.error # show # log
  let err1 = Variant.inj (Proxy @"notFound") "user 7" :: Variant (notFound :: String, badRequest :: Array String)
  let err2 = Variant.inj (Proxy @"badRequest") [ "x", "y" ] :: Variant (notFound :: String, badRequest :: Array String)
  log (showResp (widenError @ApiResponse err1))
  log (showResp (widenError @ApiResponse err2))
  splitLabels @(a :: Int, ok :: Int, z :: Int) # _.error # show # log
