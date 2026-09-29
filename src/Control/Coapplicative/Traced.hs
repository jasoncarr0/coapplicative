{-# LANGUAGE FlexibleInstances #-}

-- | This module includes the TinyCyclic typeclass,
-- which is used for the CoApplciative instance of Traced
-- (although that instance is in the main module Control.CoApplicative)
module Control.CoApplicative.Traced (TinyGroup(..)) where

import Data.Bits (Xor(..))

-- | Traced has only a single non-trivial way to make a Coapplicative
-- instance which agrees with Comonad's duplicate
--
-- Specifically, the Monoid must be either trivial or equivalent to Z2
-- That is to say, it must be a group and every element must be equal
-- to the generator or equal to mempty
--
-- This typeclass is provided so that it is possible to supply other
-- instances which are not law-abiding
class Monoid m => TinyGroup m where
  generator :: m

instance TinyGroup () where
  generator = ()

instance TinyGroup (Xor Bool) where
  generator = Xor True
