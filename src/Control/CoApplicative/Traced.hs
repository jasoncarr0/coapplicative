{-# LANGUAGE FlexibleInstances #-}

-- | This module includes the FinCyclic typeclass,
-- which is used for the CoApplciative instance of Traced
-- (although that instance is in the main module Control.CoApplicative)
module Control.CoApplicative.Traced (FinCyclic(..)) where

import Data.Bits (Xor(..))

-- | A cyclic group.
-- Every element must be equal to some power of `generator`
-- and append must be cancellable
--
-- The choice of generator is unique only up to monoidal isomorphism.
class Monoid m => FinCyclic m where
  generator :: m

instance FinCyclic () where
  generator = ()

instance FinCyclic (Xor Bool) where
  generator = Xor True
