module TL.MiniHandler where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Reader.Class (ask)
import Data.Foldable (for_)
import Data.Symbol (class IsSymbol)
import Data.Variant (Variant)
import Data.Variant as Variant
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Aff as Aff
import Effect.Class.Console (log)
import Prim.Boolean (True, False)
import Prim.Row as Row
import Prim.RowList as RL
import Record.Unsafe.Union (unsafeUnion)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)
import Yoga.Om (Om, handleErrors', runOm)

newtype Response body = Response { status :: Int, body :: body }

instance Show body => Show (Response body) where
  show (Response r) = "Response " <> show r

class ToLabel :: Type -> Symbol -> Constraint
class ToLabel labelOrCode label | labelOrCode -> label

instance ToLabel (Proxy 200) "ok"
else instance ToLabel (Proxy 201) "created"
else instance ToLabel (Proxy 404) "notFound"
else instance ToLabel (Proxy 400) "badRequest"
else instance ToLabel (Proxy label) label

class Is2xxStatus (label :: Symbol) (b :: Boolean) | label -> b
instance Is2xxStatus "ok" True
else instance Is2xxStatus "created" True
else instance Is2xxStatus label False

class SplitResponse (respVariant :: Row Type) (successRow :: Row Type) (errorRow :: Row Type) | respVariant -> successRow errorRow
instance (RL.RowToList respVariant rl, SplitResponseRL rl successRow errorRow) => SplitResponse respVariant successRow errorRow

class SplitResponseRL (rl :: RL.RowList Type) (successRow :: Row Type) (errorRow :: Row Type) | rl -> successRow errorRow
instance SplitResponseRL RL.Nil () ()
instance (Is2xxStatus label is2xx, SplitResponseEntry is2xx label ty tail successRow errorRow) => SplitResponseRL (RL.Cons label ty tail) successRow errorRow

class SplitResponseEntry (is2xx :: Boolean) (label :: Symbol) (ty :: Type) (tail :: RL.RowList Type) (successRow :: Row Type) (errorRow :: Row Type) | is2xx label ty tail -> successRow errorRow
instance (SplitResponseRL tail successTail errorRow, Row.Cons label ty successTail successRow, Row.Lacks label successTail) => SplitResponseEntry True label ty tail successRow errorRow
instance (SplitResponseRL tail successRow errorTail, Row.Cons label ty errorTail errorRow, Row.Lacks label errorTail) => SplitResponseEntry False label ty tail successRow errorRow

respond
  :: forall @labelOrCode label body r1 r2 ctx err
   . ToLabel (Proxy labelOrCode) label
  => IsSymbol label
  => Row.Cons label (Response body) r1 r2
  => body
  -> Om ctx err (Variant r2)
respond body = pure (Variant.inj (Proxy @label) (Response { status: 0, body }))

reject
  :: forall @labelOrCode label body _r1 err _r2 ctx a
   . ToLabel (Proxy labelOrCode) label
  => IsSymbol label
  => Row.Cons label (Response body) _r1 err
  => Row.Cons label (Response body) _r2 (exception :: Aff.Error | err)
  => body
  -> Om ctx err a
reject body = throwError (Variant.inj (Proxy @label) (Response { status: 0, body }))

respondNow
  :: forall @labelOrCode label body r1 successRow err ctx a
   . ToLabel (Proxy labelOrCode) label
  => IsSymbol label
  => Row.Cons label (Response body) r1 successRow
  => body
  -> Om ctx (_respondNow :: Variant successRow | err) a
respondNow body = throwError (Variant.inj (Proxy @"_respondNow") (Variant.inj (Proxy @label) (Response { status: 0, body })))

newtype Handler (respVariant :: Row Type) (ctx :: Row Type) = Handler (Record ctx -> Int -> Aff (Variant respVariant))

handle
  :: forall respVariant successRow errorRow extraCtx
   . SplitResponse respVariant successRow errorRow
  => Row.Lacks "_respondNow" errorRow
  => Row.Lacks "userId" extraCtx
  => Om { userId :: Int | extraCtx } (_respondNow :: Variant successRow | errorRow) (Variant successRow)
  -> Handler respVariant extraCtx
handle om = Handler \deps -> unsafeCoerce \userId -> do
  let ctx = unsafeMerge deps { userId }
  runOm ctx { exception: Aff.throwError } do
    handleErrors' errorHandler (unsafeExpandVariant <$> om')
  where
  om' = handleErrors' respondNowHandler om
  respondNowHandler = Variant.on (Proxy @"_respondNow") pure throwError
  errorHandler = Variant.on (Proxy @"exception")
    (throwError <<< Variant.inj (Proxy @"exception"))
    (pure <<< unsafeExpandVariant)

unsafeMerge :: forall a b c. Record a -> Record b -> Record c
unsafeMerge = unsafeUnion

unsafeExpandVariant :: forall a b. Variant a -> Variant b
unsafeExpandVariant = unsafeCoerce

type UserResponses = (ok :: Response { name :: String }, created :: Response Int, notFound :: Response String, badRequest :: Response (Array String))

userHandler :: Handler UserResponses (greeting :: String)
userHandler = handle do
  { userId, greeting } <- ask
  when (userId == 0) do
    reject @400 [ "zero id" ]
  when (userId == 13) do
    respondNow @201 13
  if userId > 100 then reject @"notFound" ("no user " <> show userId)
  else respond @200 { name: greeting <> " user " <> show userId }

runHandler :: forall resp ctx. Handler resp ctx -> Record ctx -> Int -> Aff (Variant resp)
runHandler (Handler h) ctx userId = h ctx userId

showUserResponse :: Variant UserResponses -> String
showUserResponse = Variant.match
  { ok: \r -> "200 " <> show r
  , created: \r -> "201 " <> show r
  , notFound: \r -> "404 " <> show r
  , badRequest: \r -> "400 " <> show r
  }

main :: Effect Unit
main = launchAff_ do
  for_ [ 1, 0, 13, 101, 7 ] \userId -> do
    result <- runHandler userHandler { greeting: "hi" } userId
    log (showUserResponse result)
