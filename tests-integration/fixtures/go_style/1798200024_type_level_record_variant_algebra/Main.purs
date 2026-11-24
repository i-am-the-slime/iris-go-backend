module TL.RecVariant where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, un)
import Data.Variant (Variant, inj, match, on, default, expand)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VF
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

newtype Expr = Expr (Variant (lit :: Int, add :: { left :: Expr, right :: Expr }, neg :: Expr, vars :: Array Expr))

derive instance Newtype Expr _
instance Show Expr where
  show (Expr v) = show v

instance Eq Expr where
  eq (Expr a) (Expr b) = a == b

lit :: Int -> Expr
lit = Expr <<< inj (Proxy @"lit")

add :: Expr -> Expr -> Expr
add left right = Expr (inj (Proxy @"add") { left, right })

neg :: Expr -> Expr
neg = Expr <<< inj (Proxy @"neg")

evaluate :: Expr -> Int
evaluate (Expr v) = v # match
  { lit: identity
  , add: \{ left, right } -> evaluate left + evaluate right
  , neg: \e -> negate (evaluate e)
  , vars: \es -> Array.foldl (\acc e -> acc + evaluate e) 0 es
  }

-- Extensible algebra via open rows
type LitF r = (lit :: Int | r)
type NegF r = (neg :: String | r)

renderLit :: forall r. (Variant r -> String) -> Variant (LitF r) -> String
renderLit fallback = fallback # on (Proxy @"lit") show

renderNeg :: forall r. (Variant r -> String) -> Variant (NegF r) -> String
renderNeg fallback = fallback # on (Proxy @"neg") ("-" <> _)

renderBoth :: Variant (LitF + NegF ()) -> String
renderBoth = renderLit (renderNeg (\_ -> "impossible"))

-- Fix point over VariantF
newtype Mu f = In (f (Mu f))

data ConstF a b = ConstF a
derive instance Functor (ConstF a)
data PairF a = PairF a a
derive instance Functor PairF

type ExprF = VariantF (const :: ConstF Int, pair :: PairF)

cata :: forall f a. Functor f => (f a -> a) -> Mu f -> a
cata alg (In layer) = alg (map (cata alg) layer)

sumAlg :: ExprF Int -> Int
sumAlg = VF.match { const: \(ConstF n) -> n, pair: \(PairF a b) -> a + b }

constE :: Int -> Mu ExprF
constE n = In (VF.inj (Proxy @"const") (ConstF n))

pairE :: Mu ExprF -> Mu ExprF -> Mu ExprF
pairE a b = In (VF.inj (Proxy @"pair") (PairF a b))

main :: Effect Unit
main = do
  let expr = add (lit 1) (neg (add (lit 2) (lit 3)))
  log (show (evaluate expr))
  log (show expr)
  log (show (expr == expr))
  log (show (expr == lit 1))
  log (show (evaluate (Expr (inj (Proxy @"vars") [ lit 1, lit 2, neg (lit 10) ]))))
  log (renderBoth (inj (Proxy @"lit") 5))
  log (renderBoth (inj (Proxy @"neg") "x"))
  log (show (cata sumAlg (pairE (constE 1) (pairE (constE 2) (constE 39)))))
