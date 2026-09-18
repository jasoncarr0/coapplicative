{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveFunctor, DerivingStrategies, DerivingVia #-}

module Main (main) where

import GHC.Generics
import Control.CoApplicative
import Data.List.NonEmpty
import Data.Functor.Sum
import Data.Functor.Identity

data Test a
  = A (Sum Identity Identity a)
  | B a
  | C (NonEmpty a)
  | D (Int, String, a)
  deriving stock (Generic, Generic1, Functor, Show)
  deriving CoApplicative via (Generically1 Test)

testCompiles :: IO ()
testCompiles = print (split (B x))
 where
  x :: Either Int Bool
  x = Left 4

main :: IO ()
main = do
  testCompiles
