{-# LANGUAGE DeriveFunctor, Rank2Types #-}

module Control.CoApplicative.Connector (Connector(..), pureConnector) where

import Data.Void

import Control.CoApplicative

-- | A type which is a CoApplicative but cannot be made into a Comonad
-- (nor Applicative, Monad, etc)
newtype Connector a = Connector { runConnector :: (forall b. Eq b => ((a -> b) -> b)) }
  deriving (Functor)

-- | Project a pure value into a Connector
-- We could implement Pointed but don't
pureConnector :: a -> Connector a
pureConnector a = Connector ($ a)




instance CoApplicative Connector where
  nonempty c = runConnector c id
  split c =
    if runConnector c isLeft
      then Left leftOnly
      else Right rightOnly
    where
      isLeft (Left _) = True
      isLeft (Right _) = False
      -- Unreachable due to parametricity
      inconsistent = error "Inconsistent Connector value"
      leftOnly = Connector (\f -> runConnector c (either f inconsistent))
      rightOnly = Connector (\f -> runConnector c (either inconsistent f))
