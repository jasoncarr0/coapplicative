{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveFunctor, DerivingStrategies, DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import GHC.Generics
import Control.Coapplicative
import Control.Coapplicative.Traced
import Data.List.NonEmpty
import Data.Functor.Sum
import Data.Functor.Identity
import Control.Comonad
import Control.Comonad.Traced hiding (Sum)
import Data.Bifunctor
import Data.Bits (Xor(..))

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

data Ex a
  = A (Sum Identity Identity a)
  | B a
  | C (NonEmpty a)
  | D (Int, String, a)
  deriving stock (Generic, Generic1, Functor, Show)
  deriving (Splittable, Coapplicative) via (Generically1 Ex)

testCompiles :: IO ()
testCompiles = print (split (B x))
 where
  x :: Either Int Bool
  x = Left 4

someInt :: Gen Int
someInt = Gen.int $ Range.constant 0 10

someInt2 :: Gen Int
someInt2 = Gen.int $ Range.constant 11 20

someInt3 :: Gen Int
someInt3 = Gen.int $ Range.constant 21 30

prop_nonEmptyDupSplit :: Property
prop_nonEmptyDupSplit = property $ do
  xs <- forAll $ Gen.nonEmpty (Range.linear 1 20) $ Gen.either someInt someInt
  bimap duplicate duplicate (split xs) === split (fmap split (duplicate xs))

prop_tracedXorDupSplit :: Property
prop_tracedXorDupSplit = property $ do
  i <- forAll $ Gen.either someInt someInt
  j <- forAll $ Gen.either someInt2 someInt2
  let toFn (i, j) b =
        case b of
          Xor False -> i
          Xor True -> j
      toFn' = traced . toFn
      fromFn (TracedT (Identity f)) = (f $ Xor False, f $ Xor True)
      fromFn' = fromFn . fmap fromFn
      fromFns = bimap fromFn' fromFn'

      f :: Traced (Xor Bool) (Either Int Int)
      f = toFn' (i, j)
  annotate $ show $ fromFn' $ duplicate f
  fromFns (bimap duplicate duplicate (split f)) ===
    fromFns (split (fmap split (duplicate f)))

{-
data Z3 = Z0 | Z1 | Z2
instance Semigroup Z3 where
  Z0 <> x = x
  x <> Z0 = x
  Z1 <> Z1 = Z2
  Z1 <> Z2 = Z0
  Z2 <> Z1 = Z0
  Z2 <> Z2 = Z1

instance Monoid Z3 where
  mempty = Z0

instance FinCyclic Z3 where
  generator = Z1

prop_tracedDupSplit :: Property
prop_tracedDupSplit = property $ do
  i <- forAll $ Gen.either someInt someInt
  j <- forAll $ Gen.either someInt2 someInt2
  k <- forAll $ Gen.either someInt3 someInt3

  let toFn (i, j, k) z3 =
        case z3 of
          Z0 -> i
          Z1 -> j
          Z2 -> k
      toFn' = traced . toFn
      fromFn :: Traced Z3 a -> (a, a, a)
      fromFn (TracedT (Identity f)) = (f Z0, f Z1, f Z2)
      fromFn' :: Traced Z3 (Traced Z3 a) -> ((a, a, a), (a, a, a), (a, a, a))
      fromFn' = fromFn . fmap fromFn
      fromFns :: Either (Traced Z3 (Traced Z3 a)) (Traced Z3 (Traced Z3 a)) ->
                 Either ((a, a, a), (a, a, a), (a, a, a))
                        ((a, a, a), (a, a, a), (a, a, a))
      fromFns = bimap fromFn' fromFn'

      f :: Traced Z3 (Either Int Int)
      f = toFn' (i, j, k)
  annotate $ show $ fromFn' $ duplicate f
  fromFns (bimap duplicate duplicate (split f)) ===
    fromFns (split (fmap split (duplicate f)))
    -}

testProps :: IO Bool
testProps =
  checkParallel $ Group "Properties" [
      ("nonempty_dup_split", prop_nonEmptyDupSplit),
      ("traced_xor_dup_split", prop_tracedXorDupSplit)
    ]

main :: IO ()
main = do
  testCompiles
  _ <- testProps
  pure ()
