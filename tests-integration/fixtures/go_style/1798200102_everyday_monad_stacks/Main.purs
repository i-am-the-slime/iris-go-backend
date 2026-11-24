module Fun.Stacks where

import Prelude

import Control.Apply (lift2)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, runReaderT, ask, asks)
import Control.Monad.State (StateT, runStateT, evalStateT, get, put, modify, modify_, State, runState, evalState)
import Control.Monad.Writer (WriterT, runWriterT, tell, Writer, runWriter)
import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Array ((..))
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.Traversable (traverse, for)
import Data.Foldable (for_, traverse_)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Console (log)

type App = ReaderT { step :: Int } (StateT Int (ExceptT String Effect))

tick :: App Int
tick = do
  { step } <- ask
  modify (_ + step)

tickTwice :: App (Array Int)
tickTwice = lift2 (\a b -> [ a, b ]) tick tick

tickApplicative :: App Int
tickApplicative = (+) <$> tick <*> tick

tickAdo :: App Int
tickAdo = ado
  a <- tick
  b <- tick
  in a * b

failAt :: Int -> App Int
failAt limit = do
  current <- get
  when (current > limit) (throwError ("over " <> show limit))
  pure current

countState :: Int -> State Int Int
countState limit = tailRecM step 0
  where
  step i
    | i >= limit = pure (Done i)
    | otherwise = do
        modify_ (_ + 1)
        pure (Loop (i + 1))

counterWriter :: Int -> Writer (Array String) Int
counterWriter n = do
  tell [ "start" ]
  results <- traverse (\i -> tell [ show i ] $> i * i) (1 .. n)
  tell [ "end" ]
  pure (runIdentityFold (+) 0 results)

runIdentityFold :: (Int -> Int -> Int) -> Int -> Array Int -> Int
runIdentityFold f z xs = evalState (traverse_ (\x -> modify_ (f x)) xs *> get) z

runApp :: forall a. Show a => App a -> Effect String
runApp app = do
  result <- runExceptT (runStateT (runReaderT app { step: 3 }) 10)
  pure case result of
    Left err -> "error: " <> err
    Right (value /\ state) -> show value <> " state=" <> show state

main :: Effect Unit
main = do
  runApp tick >>= log
  runApp tickTwice >>= log
  runApp tickApplicative >>= log
  runApp tickAdo >>= log
  runApp (traverse (const tick) (1 .. 4)) >>= log
  runApp (for (1 .. 4) \n -> tick <#> (_ * n)) >>= log
  runApp (tick *> tick *> failAt 12) >>= log
  runApp (tick *> failAt 100) >>= log
  runApp (tick <#> (_ + 1) <#> (_ * 2) <#> show) >>= log
  runApp (map show (map (_ * 2) tick)) >>= log
  runApp (liftEffect (log "inside") *> asks _.step) >>= log
  log $ show (runState (countState 1000000) 0)
  log $ show (runWriter (counterWriter 4))
  log $ show (runState ((/\) <$> modify (_ + 1) <*> modify (_ * 10)) 1)
  log $ show (runState (traverse (\n -> modify (_ + n)) (1 .. 5)) 0)
  w <- runWriterT (traverse_ (\n -> tell [ n ] *> liftEffect (log (show n))) [ 1, 2 ] :: WriterT (Array Int) Effect Unit)
  log (show w)
  s <- evalStateT (for (1 .. 3) \n -> modify (_ * n)) 1
  log (show s)
  t <- runStateT (lift2 (+) (modify (_ + 1)) (modify (_ + 1)) :: StateT Int Effect Int) 0
  log (show t)
