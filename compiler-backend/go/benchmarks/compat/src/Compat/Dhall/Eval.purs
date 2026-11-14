module Compat.Dhall.Eval where

import Prelude

import Data.Foldable (foldl, for_)
import Data.Maybe (Maybe(..))

import Data.Newtype (wrap)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Void (Void, absurd)
import Dhall.Core (normalize)
import Dhall.Core.AST (Expr, Var(..))
import Dhall.Core.AST as AST
import Dhall.Lib.Numbers (naturalFromInt)
import Dhall.Map (InsOrdStrMap)
import Dhall.Map as Dhall.Map
import Dhall.Printer (printAST)
import Dhall.TypeCheck as TypeCheck
import Effect (Effect)
import Effect.Console (log)
import Validation.These as Validation

type Dhall = Expr InsOrdStrMap Void

main :: Effect Unit
main = for_ examples \(name /\ expression) -> do
  log ("-- " <> name)
  log ("source:     " <> print expression)
  case Validation.hush' (TypeCheck.typeOf expression) of
    Nothing -> log "type error"
    Just type_ -> do
      log ("type:       " <> print (normalize type_))
      log ("normalised: " <> print (normalize expression))
  where
  examples =
    [ "let" /\ AST.mkLet "double" Nothing (AST.mkLam "n" AST.mkNatural (AST.mkNaturalTimes (variable "n") (natural 2))) (AST.mkApp (variable "double") (natural 21))
    , "record field" /\ AST.mkField package "version"
    , "record" /\ package
    , "Natural/fold" /\ apply AST.mkNaturalFold [ natural 5, AST.mkNatural, AST.mkLam "x" AST.mkNatural (AST.mkNaturalPlus (variable "x") (natural 3)), natural 0 ]
    , "union merge" /\ AST.mkMerge handlers (AST.mkApp (AST.mkField either "Left") (natural 7)) Nothing
    , "list length" /\ apply AST.mkListLength [ AST.mkNatural, AST.mkListAppend (naturals [ 1, 2 ]) (naturals [ 3 ]) ]
    , "list fold" /\ apply AST.mkListFold [ AST.mkNatural, naturals [ 1, 2, 3, 4 ], AST.mkNatural, AST.mkLam "x" AST.mkNatural (AST.mkLam "acc" AST.mkNatural (AST.mkNaturalPlus (variable "x") (variable "acc"))), natural 0 ]
    , "text" /\ AST.mkTextAppend (AST.mkTextLit' "Dhall ") (AST.mkTextLit' "in Go")
    , "polymorphic identity" /\ AST.mkApp (AST.mkApp identityFunction AST.mkBool) (AST.mkBoolLit true)
    , "combine" /\ AST.mkCombine package (record [ "stable" /\ AST.mkBoolLit false ])
    , "ill-typed" /\ AST.mkNaturalPlus (natural 1) (AST.mkBoolLit true)
    ]

  package = record [ "name" /\ AST.mkTextLit' "dhall", "version" /\ natural 3 ]
  either = AST.mkUnion (Dhall.Map.fromFoldable [ "Left" /\ Just AST.mkNatural, "Right" /\ Just AST.mkBool ])
  handlers = record
    [ "Left" /\ AST.mkLam "n" AST.mkNatural (AST.mkNaturalPlus (variable "n") (natural 1))
    , "Right" /\ AST.mkLam "b" AST.mkBool (natural 0)
    ]
  identityFunction = AST.mkLam "a" (AST.mkConst AST.Type) (AST.mkLam "x" (variable "a") (variable "x"))

print :: Dhall -> String
print = printAST { ascii: true, line: Nothing, printImport: absurd, tabs: { width: wrap 2, soft: false, align: false } }

variable :: String -> Dhall
variable name = AST.mkVar (V name 0)

natural :: Int -> Dhall
natural = AST.mkNaturalLit <<< naturalFromInt

naturals :: Array Int -> Dhall
naturals = AST.mkListLit Nothing <<< map natural

record :: Array (String /\ Dhall) -> Dhall
record = AST.mkRecordLit <<< Dhall.Map.fromFoldable

apply :: Dhall -> Array Dhall -> Dhall
apply = foldl AST.mkApp
