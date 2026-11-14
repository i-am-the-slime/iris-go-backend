module Compat.Exotic.Variants where

import Prelude

import Data.Functor.Variant (VariantF, inj, case_, on) as VF
import Data.Functor.Variant (VariantF)
import Data.Variant (Variant, default, expand, inj, match, onMatch, prj, case_, on)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

type Basic r = (number :: Int, text :: String | r)

describe :: Variant (Basic (flag :: Boolean)) -> String
describe = case_
  # on (Proxy @"number") (\n -> "number " <> show n)
  # on (Proxy @"text") (\s -> "text " <> s)
  # on (Proxy @"flag") (\b -> "flag " <> show b)

widen :: Variant (Basic ()) -> Variant (Basic (flag :: Boolean))
widen = expand

partial :: forall r. Variant (number :: Int | r) -> String
partial = default "other" # onMatch { number: \n -> "n=" <> show n }

data Add a = Add a a
derive instance Functor Add
data Lit a = Lit Int
derive instance Functor Lit

type ExprF = VariantF (add :: Add, lit :: Lit)

newtype Expr = Expr (ExprF Expr)

lit :: Int -> Expr
lit n = Expr (VF.inj (Proxy @"lit") (Lit n))

plus :: Expr -> Expr -> Expr
plus a b = Expr (VF.inj (Proxy @"add") (Add a b))

evaluate :: Expr -> Int
evaluate (Expr layer) = layer # (VF.case_
  # VF.on (Proxy @"lit") (\(Lit n) -> n)
  # VF.on (Proxy @"add") (\(Add a b) -> evaluate a + evaluate b))

main :: Effect Unit
main = do
  log (describe (inj (Proxy @"number") 3))
  log (describe (widen (inj (Proxy @"text") "hi")))
  log (describe (inj (Proxy @"flag") true))
  log (partial (inj (Proxy @"number") 5 :: Variant (Basic ())) <> " " <> partial (inj (Proxy @"text") "x" :: Variant (Basic ())))
  log (show (prj (Proxy @"text") (inj (Proxy @"text") "found" :: Variant (Basic ())) :: Maybe String))
  log (show (prj (Proxy @"number") (inj (Proxy @"text") "missing" :: Variant (Basic ())) :: Maybe Int))
  log (match { number: show, text: identity } (inj (Proxy @"number") 12 :: Variant (Basic ())))
  log (show (evaluate (plus (lit 1) (plus (lit 2) (lit 39)))))
  log (show (inj (Proxy @"number") 1 == (inj (Proxy @"number") 1 :: Variant (Basic ()))))
  log (show (inj (Proxy @"text") "shown" :: Variant (Basic ())))
