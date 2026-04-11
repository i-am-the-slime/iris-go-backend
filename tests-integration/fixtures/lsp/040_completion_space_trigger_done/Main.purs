module Main where

class Monad m <= MonadAsk r m | m -> r where
  ask :: m r

newtype Reader r a = Reader (r -> a)

derive instance Functor (Reader r)

instance Apply (Reader r) where
  apply (Reader f) (Reader a) = Reader \r -> f r (a r)

instance Applicative (Reader r) where
  pure a = Reader \_ -> a

instance Bind (Reader r) where
  bind (Reader a) f = Reader \r -> case f (a r) of Reader b -> b r

instance Monad (Reader r)

instance MonadAsk r (Reader r) where
  ask = Reader \r -> r

type Ctx = { path :: { id :: String }, db :: String }

handler :: Reader Ctx String
handler = do
  ctx <- ask
  ctx.
--    #

handler2 :: Reader Ctx String
handler2 = do
  ctx@{  } <- ask
--     ^

handler3 :: Reader Ctx String
handler3 = do
  {  } <- ask
-- ^
