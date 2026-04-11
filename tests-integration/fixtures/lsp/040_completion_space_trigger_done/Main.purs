module Main where

class Monad m <= MonadAsk r m | m -> r where
  ask :: m r

newtype Om ctx err a = Om (ctx -> a)

derive instance Functor (Om ctx err)

instance Apply (Om ctx err) where
  apply (Om f) (Om a) = Om \c -> f c (a c)

instance Applicative (Om ctx err) where
  pure a = Om \_ -> a

instance Bind (Om ctx err) where
  bind (Om a) f = Om \c -> case f (a c) of Om b -> b c

instance Monad (Om ctx err)

instance MonadAsk ctx (Om ctx err) where
  ask = Om \c -> c

-- Handler is a NEWTYPE — annotation can't be expanded to find `path`.
-- `path` is added by handleAuth and only visible through the Om context.
newtype Handler route (ctx :: Row Type) = Handler (Om (path :: { id :: String } | ctx) () String)

unHandler :: forall route ctx. Handler route ctx -> Om (path :: { id :: String } | ctx) () String
unHandler (Handler om) = om

handleAuth
  :: forall route ctx
   . (String -> Om (Record (path :: { id :: String }, authApi :: String | ctx)) () String)
  -> Handler route (authApi :: String | ctx)
handleAuth _ = Handler (Om \_ -> "")

type RowApply :: forall k. (Row k -> Row k) -> Row k -> Row k
type RowApply f a = f a

infixr 0 type RowApply as +

type BaseCtx r = (config :: String, db :: String | r)

type AuthCtx r = (authApi :: String | r)

-- Test 1: empty record binder — should show all 4 fields (path + authApi + config + db)
deleteTodoHandler :: Handler String (AuthCtx + BaseCtx + ())
deleteTodoHandler = handleAuth \_session -> do
  {  } <- ask
-- ^

-- Test 2: partial text "p" — should still show fields matching "p" (path, ...)
deleteTodoHandler2 :: Handler String (AuthCtx + BaseCtx + ())
deleteTodoHandler2 = handleAuth \_session -> do
  {p} <- ask
-- ^

-- Test 3: partial text "pa" — should still show fields matching "pa" (path)
deleteTodoHandler3 :: Handler String (AuthCtx + BaseCtx + ())
deleteTodoHandler3 = handleAuth \_session -> do
  {pa} <- ask
-- ^

-- Test 4: partial text "co" with spaces
deleteTodoHandler4 :: Handler String (AuthCtx + BaseCtx + ())
deleteTodoHandler4 = handleAuth \_session -> do
  { co } <- ask
--   ^

-- Test 5: named binder with corruption from ctx.config on next line
deleteTodoHandler5 :: Handler String (AuthCtx + BaseCtx + ())
deleteTodoHandler5 = handleAuth \_session -> do
  ctx@{  } <- ask
--     ^
  let x = ctx.config
  x

-- Test 6: dot trigger should also show all fields
deleteTodoHandler6 :: Handler String (AuthCtx + BaseCtx + ())
deleteTodoHandler6 = handleAuth \_session -> do
  ctx <- ask
  ctx.
--    #

-- Test 7: record accessor section `asks _.` should show record fields
class MonadAsk r m <= MonadReader r m | m -> r where
  local :: forall a. (r -> r) -> m a -> m a
  reader :: forall a. (r -> a) -> m a

instance MonadReader ctx (Om ctx err) where
  local f (Om g) = Om \c -> g (f c)
  reader f = Om \c -> f c

asks :: forall r m a. MonadAsk r m => (r -> a) -> m a
asks f = do
  r <- ask
  pure (f r)

deleteTodoHandler7 :: Handler String (AuthCtx + BaseCtx + ())
deleteTodoHandler7 = handleAuth \_session -> do
  x <- asks _.
--              #
  pure ""
