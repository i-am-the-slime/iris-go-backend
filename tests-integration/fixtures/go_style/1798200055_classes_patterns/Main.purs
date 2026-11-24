module T.Pat where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

classify :: Int /\ String /\ Maybe Number /\ Array Char -> String
classify = case _ of
  0 /\ _ /\ _ /\ _ -> "zero"
  n /\ "special" /\ _ /\ _ | n < 0 -> "negative special"
  _ /\ name /\ Just 1.5 /\ [ 'a', second ] -> name <> " 1.5 " <> show second
  n /\ name /\ Just x /\ chars
    | x > 10.0, Array.length chars > 1 -> name <> " big " <> show n
    | Just first <- Array.head chars -> name <> " first=" <> show first
  _ /\ _ /\ Nothing /\ [] -> "nothing-empty"
  whole@(_ /\ _ /\ _ /\ _) -> "other " <> show whole

describeUser :: { name :: String, age :: Int, roles :: Array String } -> String
describeUser user@{ name, roles: [ onlyRole ] } = name <> " only " <> onlyRole <> " " <> show user.age
describeUser { name, age } | age >= 65 = name <> " senior"
describeUser { roles } = "roles " <> show (Array.length roles)

lookupBoth :: Map.Map String Int -> String -> String -> Either String Int
lookupBoth table a b = ado
  x <- note ("missing " <> a) (Map.lookup a table)
  y <- note ("missing " <> b) (Map.lookup b table)
  in x + y
  where
  note message = case _ of
    Nothing -> Left message
    Just v -> Right v

main :: Effect Unit
main = do
  let inputs =
        [ 0 /\ "a" /\ Nothing /\ []
        , (-1) /\ "special" /\ Nothing /\ []
        , 5 /\ "x" /\ Just 1.5 /\ [ 'a', 'b' ]
        , 5 /\ "y" /\ Just 11.0 /\ [ 'a', 'b' ]
        , 5 /\ "z" /\ Just 2.0 /\ [ 'q' ]
        , 5 /\ "w" /\ Nothing /\ []
        , 5 /\ "v" /\ Just 2.0 /\ []
        ]
  inputs <#> classify # Array.intercalate "\n" # log
  [ { name: "A", age: 30, roles: [ "admin" ] }, { name: "B", age: 70, roles: [] }, { name: "C", age: 20, roles: [ "x", "y" ] } ] <#> describeUser # show # log
  let table = Map.fromFoldable [ "a" /\ 1, "b" /\ 2 ]
  log (show (lookupBoth table "a" "b") <> show (lookupBoth table "a" "c") <> show (lookupBoth table "d" "c"))
  let { name, nested: { deep } } = { name: "n", nested: { deep: [ 1, 2 ] } }
  let first /\ second = 1 /\ "two"
  log (name <> show deep <> show first <> second)
  [ "yes", "no", "maybe" ] <#> (case _ of
      "yes" -> true
      "no" -> false
      _ -> false) # show # log
  [ 'a', 'Z', '1' ] <#> (case _ of
      c | c >= 'a' && c <= 'z' -> "lower"
        | c >= 'A' && c <= 'Z' -> "upper"
        | otherwise -> "other") # show # log
