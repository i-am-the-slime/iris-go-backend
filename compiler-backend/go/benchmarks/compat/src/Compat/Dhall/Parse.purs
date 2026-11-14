module Compat.Dhall.Parse where

import Prelude

import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Newtype (wrap)
import Data.Traversable (traverse)
import Dhall.Core (normalize)
import Dhall.Core.AST (Expr)
import Dhall.Map (InsOrdStrMap)
import Dhall.Parser as Parser
import Dhall.Printer (printAST)
import Dhall.TypeCheck as TypeCheck
import Data.Void (Void, absurd)
import Effect (Effect)
import Effect.Console (log)
import Validation.These as Validation

main :: Effect Unit
main = for_ sources \source -> do
  log ("-- " <> source)
  case Parser.parse source >>= traverse (const Nothing) of
    Nothing -> log "parse error"
    Just (expression :: Expr InsOrdStrMap Void) -> case Validation.hush' (TypeCheck.typeOf expression) of
      Nothing -> log "type error"
      Just type_ -> do
        log ("type:       " <> print (normalize type_))
        log ("normalised: " <> print (normalize expression))
  where
  sources =
    [ "let double = \\(n : Natural) -> n * 2 in double 21"
    , "{ name = \"dhall\", version = 3 }.version"
    , "Natural/fold 5 Natural (\\(x : Natural) -> x + 3) 0"
    , "merge { Left = \\(n : Natural) -> n + 1, Right = \\(b : Bool) -> 0 } (< Left : Natural | Right : Bool >.Left 7)"
    , "List/length Natural ([1, 2] # [3])"
    , "let Person = { name : Text, age : Natural } let people : List Person = [ { name = \"ann\", age = 30 }, { name = \"bob\", age = 41 } ] in List/fold Person people Natural (\\(p : Person) -> \\(total : Natural) -> p.age + total) 0"
    , "\\(a : Type) -> \\(x : a) -> x"
    , "1 + True"
    , "{ unclosed = "
    ]

print :: Expr InsOrdStrMap Void -> String
print = printAST { ascii: true, line: Nothing, printImport: absurd, tabs: { width: wrap 2, soft: false, align: false } }
