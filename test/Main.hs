{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveFunctor, DerivingStrategies, DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Main (main) where

import GHC.Generics
import Control.Coapplicative
import Control.Coapplicative.Traced
import Data.List.NonEmpty
import Data.Functor.Classes (Eq1(..), Show1(..))
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
instance Eq1 Ex where
  liftEq e x y =
    case (x, y) of
      (A fx, A fy) -> liftEq e fx fy
      (B x, B y) -> e x y
      (C xs, C ys) -> liftEq e xs ys
      (D (i1, s1, x), D (i2, s2, y)) ->
        i1 == i2 && s1 == s2 && e x y
      _ -> False
instance Eq a => Eq (Ex a) where
  (==) = liftEq (==)
instance Show1 Ex where
  liftShowsPrec showA shows i ex _ = "TODO Show1 Ex"

testCompiles :: IO ()
testCompiles = do
  print (split (B x))
 where
  x :: Either Int Bool
  x = Left 4

someInt :: Gen Int
someInt = Gen.int $ Range.constant 0 9

someInt2 :: Gen Int
someInt2 = Gen.int $ Range.constant 10 19

someInt3 :: Gen Int
someInt3 = Gen.int $ Range.constant 20 29

genEx :: Gen a -> Gen (Ex a)
genEx ga =
  -- doesn't matter
  let genString = Gen.string (Range.constant 0 5) Gen.binit in
  Gen.choice [
    A <$> (Gen.choice [pure (InL . Identity), pure (InR . Identity)] <*> ga),
    B <$> ga,
    C <$> Gen.nonEmpty (Range.constant 0 20) ga,
    D <$> ((,,) <$> someInt <*> genString <*> ga)
  ]
  

prop_nonEmptyDupSplit :: Property
prop_nonEmptyDupSplit = property $ do
  xs <- forAll $ Gen.nonEmpty (Range.linear 1 20) $ Gen.either someInt someInt
  bimap duplicate duplicate (split xs) === split (fmap split (duplicate xs))


-- TODO use a newtype instead so we can verify all properties easily;
-- mechanized though so lower priority
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

-- Use only when we find something that isn't a comonad :)
pred_validSplit :: (Splittable f, Eq1 f, Show1 f) => (forall a. Gen a -> Gen (f a)) -> Property
pred_validSplit gen = property $ do
  xs <- forAll $ gen (Gen.either someInt someInt2)
  let left :: a -> Either a Bool
      left = Left
      right :: a -> Either Bool a
      right = Right
  split (left <$> xs) === Left xs
  split (right <$> xs) === Right xs
  f <- (*) <$> forAll someInt
  g <- (+) <$> forAll someInt

  bimap (fmap f) (fmap g) (split xs) === split (bimap f g <$> xs)

pred_validComonadCoapplicative :: (Coapplicative w, Comonad w, Eq1 w, Show1 w)
                               => (forall a. Gen a -> Gen (w a)) -> Property
pred_validComonadCoapplicative gen = property $ do
  xs <- forAll $ gen (Gen.either someInt someInt2)
  -- copy-paste to not regen
  let left :: a -> Either a Bool
      left = Left
      right :: a -> Either Bool a
      right = Right
  split (left <$> xs) === Left xs
  split (right <$> xs) === Right xs
  f <- (*) <$> forAll someInt
  g <- (+) <$> forAll someInt

  -- nonempty laws are trivial
  bimap extract extract (split xs) === extract xs
  bimap duplicate duplicate (split xs) === split (fmap split (duplicate xs))

  copure xs === extract xs
  bimap copure id (split xs) === costrength xs
  (costrength . fmap costrength) (duplicate xs) ===
    bimap id duplicate (costrength xs)


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
  let genNE = Gen.nonEmpty (Range.linear 1 20) in
  checkParallel $ Group "Properties" [
      ("traced_xor_dup_split", prop_tracedXorDupSplit),
      ("nonempty_valid", pred_validComonadCoapplicative genNE),
      ("generics_split", pred_validSplit genEx)
    ]

main :: IO ()
main = do
  let _ = testCompiles
  _ <- testProps
  pure ()
