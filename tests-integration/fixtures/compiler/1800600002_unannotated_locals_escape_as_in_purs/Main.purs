module Main where

data Unit = Unit

data Spec = Spec

data Index scope = Index Int

class Shout value where
  shout :: value -> value

foreign import mkEval :: forall value. Spec -> value -> value

foreign import consumeIdentity :: (forall value. value -> value) -> Unit

foreign import consumeUnit :: (forall value. value -> Unit) -> Unit

foreign import applyBoth :: (forall value. value -> Array value) -> Unit

consumeShout :: (forall value. Shout value => value -> value) -> Unit
consumeShout _ = Unit

toInt :: forall scope. Index scope -> Int
toInt (Index number) = number

acceptedPointFree :: Unit
acceptedPointFree = consumeIdentity eval
  where
  eval = mkEval Spec

acceptedAlias :: Unit
acceptedAlias = applyBoth wrap
  where
  wrap = singleton

  singleton :: forall value. value -> Array value
  singleton value = [ value ]

acceptedIgnoredArgument :: Unit
acceptedIgnoredArgument = consumeUnit ignore
  where
  ignore _ = Unit

acceptedLocalEvidence :: Unit
acceptedLocalEvidence = consumeShout loud
  where
  loud = shout

acceptedNestedUnderSignature :: Int -> Int
acceptedNestedUnderSignature number = fill (Index number)
  where
  fill :: forall scope. Index scope -> Int
  fill index = lowest index
    where
    lowest nested = toInt nested

acceptedSiblingAlias :: Int -> Int
acceptedSiblingAlias number = fill (Index number)
  where
  fill :: forall scope. Index scope -> Int
  fill index = lowest index

  lowest = toInt

rejectedWrap :: Unit
rejectedWrap = applyBoth wrap
  where
  wrap value = [ value ]

rejectedLambda :: Unit
rejectedLambda = consumeIdentity same
  where
  same = \value -> value

rejectedCase :: Unit
rejectedCase = consumeIdentity eval
  where
  eval = case Spec of
    Spec -> mkEval Spec

rejectedLet :: Unit
rejectedLet = do
  let same value = value
  consumeIdentity same

rejectedSiblingOfSignature :: Int -> Int
rejectedSiblingOfSignature number = fill (Index number)
  where
  fill :: forall scope. Index scope -> Int
  fill index = lowest index

  lowest index = toInt index
