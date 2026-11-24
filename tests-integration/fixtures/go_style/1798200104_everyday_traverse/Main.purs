module Fun.Traverse where

import Prelude

import Control.Apply (lift2)
import Data.Foldable (foldM)
import Data.Array (range)
import Data.Either (Either(..))
import Data.Foldable (foldMap, foldl, foldr, for_, traverse_, intercalate)
import Data.Int (fromString)
import Data.Maybe (Maybe(..))
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (un)
import Data.Traversable (for, sequence, traverse)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref

newtype Validated a = Validated (Either (Array String) a)

instance Functor Validated where
  map f (Validated result) = Validated (result <#> f)

instance Apply Validated where
  apply (Validated (Left errorsA)) (Validated (Left errorsB)) = Validated (Left (errorsA <> errorsB))
  apply (Validated (Left errors)) _ = Validated (Left errors)
  apply (Validated (Right f)) (Validated result) = Validated (result <#> f)

instance Applicative Validated where
  pure = Validated <<< Right

toEither :: forall a. Validated a -> Either (Array String) a
toEither (Validated result) = result

parseNumber :: String -> Either String Int
parseNumber text = case fromString text of
  Just n -> Right n
  Nothing -> Left ("bad: " <> text)

halve :: Int -> Maybe Int
halve n
  | n `mod` 2 == 0 = Just (n / 2)
  | otherwise = Nothing

quarter :: Int -> Maybe Int
quarter = halve >=> halve

quarterBack :: Int -> Maybe Int
quarterBack = halve <=< halve

quarterBind :: Int -> Maybe Int
quarterBind n = halve n >>= halve

quarterFlipped :: Int -> Maybe Int
quarterFlipped n = halve =<< halve n

quarterDo :: Int -> Maybe Int
quarterDo n = do
  half <- halve n
  halve half

eighthChain :: Int -> Maybe Int
eighthChain n = pure n >>= halve >>= halve >>= halve

validatePositive :: Int -> Either (Array String) Int
validatePositive n
  | n > 0 = Right n
  | otherwise = Left [ "not positive: " <> show n ]

validatePositiveV :: Int -> Validated Int
validatePositiveV n
  | n > 0 = pure n
  | otherwise = Validated (Left [ "not positive: " <> show n ])

readerCombined :: Int -> Int
readerCombined = (+) <$> (_ * 2) <*> (_ + 10)

readerLift :: Int -> Int
readerLift = lift2 (+) (_ * 2) (_ + 10)

readerDo :: Int -> Int
readerDo = do
  doubled <- (_ * 2)
  shifted <- (_ + 10)
  pure (doubled + shifted)

readerAdo :: Int -> Int
readerAdo = ado
  doubled <- (_ * 2)
  shifted <- (_ + 10)
  in doubled + shifted

main :: Effect Unit
main = do
  let texts = [ "1", "2", "3" ]
  let badTexts = [ "1", "x", "y" ]
  log $ show (traverse parseNumber texts)
  log $ show (traverse parseNumber badTexts)
  log $ show (for texts parseNumber)
  log $ show (sequence (texts <#> parseNumber))
  log $ show (sequence [ Just 1, Just 2 ])
  log $ show (sequence [ Just 1, Nothing ])
  log $ show (map quarter [ 8, 6, 12, 3 ])
  log $ show (map quarterBack [ 8, 6, 12, 3 ])
  log $ show (map quarterBind [ 8, 6, 12, 3 ])
  log $ show (map quarterFlipped [ 8, 6, 12, 3 ])
  log $ show (map quarterDo [ 8, 6, 12, 3 ])
  log $ show (map eighthChain [ 8, 16, 12 ])
  log $ show (foldMap show [ 1, 2, 3 ])
  log $ show (un Additive (foldMap Additive [ 1, 2, 3 ]))
  log $ show (foldl (\acc n -> acc <> show n) "" [ 1, 2, 3 ])
  log $ show (foldr (\n acc -> acc <> show n) "" [ 1, 2, 3 ])
  log $ show (foldl (-) 100 [ 1, 2, 3 ])
  log $ show (foldr (-) 100 [ 1, 2, 3 ])
  log $ show (foldM (\acc n -> if n > 0 then Just (acc + n) else Nothing) 0 [ 1, 2, 3 ])
  log $ show (foldM (\acc n -> if n > 0 then Just (acc + n) else Nothing) 0 [ 1, -2, 3 ])
  log $ show (intercalate ", " [ "a", "b", "c" ])
  log $ show (lift2 (+) (Just 1) (Just 2))
  log $ show ((+) <$> Just 1 <*> Just 2)
  log $ show
    ( ado
        a <- Just 1
        b <- Just 2
        in a * 10 + b
    )
  log $ show ((/\) <$> [ 1, 2 ] <*> [ "a", "b" ])
  log $ show (traverse validatePositive [ 1, -2, -3 ])
  log $ show (toEither (traverse validatePositiveV [ 1, -2, -3 ]))
  log $ show (toEither (traverse validatePositiveV [ 1, 2, 3 ]))
  log $ show
    ( toEither ado
        a <- validatePositiveV 0
        b <- validatePositiveV (-1)
        c <- validatePositiveV 5
        in a + b + c
    )
  log $ show (toEither (lift2 (+) (validatePositiveV 0) (validatePositiveV (-7))))
  log $ show (map readerCombined [ 1, 2 ])
  log $ show (map readerLift [ 1, 2 ])
  log $ show (map readerDo [ 1, 2 ])
  log $ show (map readerAdo [ 1, 2 ])
  log $ show (apply (+) (_ * 3) 4)
  total <- Ref.new 0
  for_ (range 1 10) \n -> Ref.modify_ (_ + n) total
  traverse_ (\n -> Ref.modify_ (_ * 2) total # when (n > 8)) (range 1 10)
  Ref.read total >>= show >>> log
  results <- for [ 1, 2, 3 ] \n -> do
    Ref.modify_ (_ + n) total
    Ref.read total
  log $ show results
  results2 <- traverse (\n -> Ref.modify (_ + n) total) [ 1, 2, 3 ]
  log $ show results2
  effects <- sequence [ pure 1, Ref.read total, pure 3 ]
  log $ show effects
  summed <- foldM (\acc n -> Ref.modify (_ + n) total <#> (_ + acc)) 0 [ 1, 2, 3 ]
  log $ show summed
