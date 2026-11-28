module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (findMap)
import Data.Maybe (Maybe(..), maybe)
import Effect (Effect)
import Effect.Console (log)

type Transform = forall b. Maybe (Parser b -> Parser b)

newtype Parser a = P { parse :: String -> Array a, transform :: Transform }

mkParser :: forall a. (String -> Array a) -> Parser a
mkParser parse = P { parse, transform: Nothing }

parse :: forall a. Parser a -> String -> Array a
parse (P parser) = parser.parse

applyTransform :: forall a. Transform -> Parser a -> Parser a
applyTransform transform parser =
  maybe parser (\apply -> P ((unwrap (apply parser)) { transform = transform })) transform
  where
  unwrap (P inner) = inner

applyFirst :: forall a. (forall b. Array (Maybe (Parser b -> Parser b))) -> Parser a -> Parser a
applyFirst transforms = applyTransform (findMap identity transforms)

both :: forall a. Parser a -> Parser a -> Parser a
both (P { parse: first, transform: (t :: Transform) }) (P { parse: second, transform: (t' :: Transform) }) =
  applyFirst [ t, t' ] (mkParser \input -> first input <> second input)

withTransform :: forall a. (forall b. Parser b -> Parser b) -> Parser a -> Parser a
withTransform transform = applyTransform (Just transform)

reversing :: forall b. Parser b -> Parser b
reversing (P parser) = P (parser { parse = Array.reverse <<< parser.parse })

main :: Effect Unit
main = do
  let digits = mkParser \input -> [ input <> "1", input <> "2" ]
  log (show (parse (both digits (withTransform reversing digits)) "x"))
  log (show (parse (both (withTransform reversing (mkParser \_ -> [ 1, 2 ])) (mkParser \_ -> [ 3 ])) ""))
