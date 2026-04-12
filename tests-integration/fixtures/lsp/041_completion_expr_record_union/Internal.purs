module Yoga.React.DOM.Internal where

import Prim.Row (class Union)
import Prim.RowList (class RowToList, RowList)
import Type.RowList (class ListToRow)
import Type.RowList as RL
import Prim.Boolean (True, False)
import Prim.Symbol as Symbol
import Type.Equality (class TypeEquals)
import Unsafe.Coerce (unsafeCoerce)

data JSX

instance Semigroup JSX where
  append _ _ = unsafeCoerce unit

instance Monoid JSX where
  mempty = unsafeCoerce unit

class IsJSX :: Type -> Constraint
class IsJSX a

instance IsJSX JSX
instance IsJSX String
instance (TypeEquals a JSX) => IsJSX (Array a)

type FFIComponent props =
  forall givenProps nonDataProps kids
   . IsJSX kids
  => CoerceReactProps { | givenProps } { | nonDataProps } { | props }
  => { | givenProps }
  -> kids
  -> JSX

type FFIComponent_ props =
  forall givenProps nonDataProps
   . CoerceReactProps { | givenProps } { | nonDataProps } { | props }
  => { | givenProps }
  -> JSX

class CoerceReactProps :: forall k. Type -> k -> Type -> Constraint
class CoerceReactProps props nonDataProps targetProps | props -> nonDataProps

instance
  ( WithoutDataProps { | props } { | nonDataProps }
  , Union nonDataProps missing targetProps
  ) =>
  CoerceReactProps { | props } { | nonDataProps } { | targetProps }

class WithoutDataPropsRL (from :: RowList Type) (to :: RowList Type) | from -> to

class
  MaybeWithoutDataPropRL (exclude :: Boolean) (propName :: Symbol) (propVal :: Type) (from :: RowList Type) (to :: RowList Type)
  | exclude propName propVal from -> to

instance WithoutDataPropsRL RL.Nil RL.Nil
instance
  ( DoesStartWith "data-" propName exclude
  , MaybeWithoutDataPropRL exclude propName propVal from to
  ) =>
  WithoutDataPropsRL (RL.Cons propName propVal from) to

instance (WithoutDataPropsRL from to) => MaybeWithoutDataPropRL False propName propVal from (RL.Cons propName propVal to)
instance (WithoutDataPropsRL from to) => MaybeWithoutDataPropRL True propName propVal from to

class WithoutDataProps props without where
  unsafeHideDataProps :: props -> without

instance
  ( RowToList r rl
  , ListToRow withoutRL without
  , WithoutDataPropsRL rl withoutRL
  ) =>
  WithoutDataProps (Record r) (Record without) where
  unsafeHideDataProps = unsafeCoerce

class DoesStartWith (prefix :: Symbol) (full :: Symbol) (match :: Boolean) | prefix full -> match

instance DoesStartWith "" full True
else instance DoesStartWith prefix "" False
else instance
  ( Symbol.Cons prefixH prefixT prefix
  , Symbol.Cons fullH fullT full
  , DoesStartWithChar prefixH prefixT fullH fullT match
  ) =>
  DoesStartWith prefix full match

class
  DoesStartWithChar (prefixH :: Symbol) (prefixT :: Symbol) (fullH :: Symbol) (fullT :: Symbol) (match :: Boolean)
  | prefixH prefixT fullH fullT -> match

instance DoesStartWith prefix full match => DoesStartWithChar c prefix c full match
else instance DoesStartWithChar prefixH prefixT fullH fullT False

foreign import data CSS :: Type
