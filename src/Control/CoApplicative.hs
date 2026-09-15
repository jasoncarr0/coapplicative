{-# LANGUAGE DeriveFunctor #-}

module Control.CoApplicative (CoApplicative(..), CoAppComonad(..)) where

import Data.Void
import Data.Functor.Identity (Identity(..))
import Control.Comonad
import Control.Comonad.Trans.Env
import Data.List.NonEmpty
import Data.Maybe (mapMaybe)
import Data.Functor.Sum

leftToMaybe :: Either a b -> Maybe a
leftToMaybe (Left x) = Just x
leftToMaybe (Right _) = Nothing
rightToMaybe :: Either a b -> Maybe b
rightToMaybe (Left _) = Nothing
rightToMaybe (Right x) = Just x

-- | An opmonoidal functor over the cocartesian structure
-- of Either and Void.
--
-- Laws include associativity, and compatibility with fmap
-- (which implies identity laws)
--
-- either id split . split = either split id . split . fmap reassoc
-- where reassoc is the unique total function of type (Either a (Either b c)) -> Either (Either a b) c
-- split . fmap (either f g) = either (fmap f) (fmap g) . split
-- split . fmap Left = Left
-- split . fmap Right = Right
--
-- Every Comonad is a CoApplicative, but not always in a compatible way
-- with the Comonad structure.
-- In particular, dup must distribute with split
--
-- Some Comonads have multiple compatible structures, such as `Traced` over a cyclic group:
-- choose the Left/Right according to the head, replacing any incompatible elements by scanning
-- for the next appropriate element via adding a generator.
-- ℤ3 and up have multiple generators.
-- Although this example is not identical, these possibilities are isomorphic

class Functor f => CoApplicative f where
  nonempty :: f Void -> Void
  split :: f (Either a b) -> Either (f a) (f b)

  -- | Filter Maybe through the data-structure along Just,
  -- discarding the context of Nothing values
  --
  -- The default implementation biases towards the Left
  splitMaybe :: f (Maybe a) -> Maybe (f a)
  splitMaybe = leftToMaybe . split . fmap maybeToLeft
    where
      maybeToLeft (Just x) = Left x
      maybeToLeft Nothing = Right ()

  -- | Zip a list through the data-structure,
  -- discarding the context of nil values
  splitList :: f [a] -> [f a]
  splitList = roll . maybe Nothing (Just . dorec) . splitMaybe . fmap unroll
    where
      dorec was = (fmap fst was, splitList $ fmap snd was)

      unroll :: [b] -> Maybe (b, [b])
      unroll [] = Nothing
      unroll (x : xs) = Just (x, xs)
      roll :: Maybe (b, [b]) -> [b]
      roll Nothing = []
      roll (Just (x, xs)) = x : xs

instance CoApplicative Identity where
  nonempty (Identity v) = v
  split (Identity (Left x)) = Left (Identity x)
-- This is compatible
  split (Identity (Right y)) = Right (Identity y)

-- | Default CoApplicative for NonEmpty filters
-- to those elements which match the head element.
-- Compatible with the Comonad instance,
--   so nom-empty has "good" pattern matching, in which matching
--   on a value produces a new value with a consistent view of the context
--   
instance CoApplicative NonEmpty where
  nonempty (v :| _) = v
  split (Left x :| rest) = Left (x :| mapMaybe leftToMaybe rest)
  split (Right x :| rest) = Right (x :| mapMaybe rightToMaybe rest)

instance (CoApplicative f, CoApplicative g) => CoApplicative (Sum f g) where
  nonempty (InL fv) = nonempty fv
  nonempty (InR gv) = nonempty gv
  split (InL fe) = either (Left . InL) (Right . InL) (split fe)
  split (InR ge) = either (Left . InR) (Right . InR) (split ge)
  splitMaybe (InL fm) = InL <$> (splitMaybe fm)
  splitMaybe (InR gm) = InR <$> (splitMaybe gm)
  splitList (InL fxs) = InL <$> (splitList fxs)
  splitList (InR gxs) = InR <$> (splitList gxs)

instance CoApplicative ((,) a) where
  nonempty (_, v) = v
  split (a, Left x) = Left (a, x)
  split (a, Right y) = Right (a, y)

instance CoApplicative ((,,) a b) where
  nonempty (_, _, v) = v
  split (a, b, Left x) = Left (a, b, x)
  split (a, b, Right y) = Right (a, b, y)

instance CoApplicative ((,,,) a b c) where
  nonempty (_, _, _, v) = v
  split (a, b, c, Left x) = Left (a, b, c, x)
  split (a, b, c, Right y) = Right (a, b, c, y)

instance CoApplicative ((,,,,) a b c d) where
  nonempty (_, _, _, _, v) = v
  split (a, b, c, d, Left x) = Left (a, b, c, d, x)
  split (a, b, c, d, Right y) = Right (a, b, c, d, y)

instance CoApplicative ((,,,,,) a b c d e) where
  nonempty (_, _, _, _, _, v) = v
  split (a, b, c, d, e, Left x) = Left (a, b, c, d, e, x)
  split (a, b, c, d, e, Right y) = Right (a, b, c, d, e, y)

instance CoApplicative ((,,,,,,) a b c d e f) where
  nonempty (_, _, _, _, _, _, v) = v
  split (a, b, c, d, e, f, Left x) = Left (a, b, c, d, e, f, x)
  split (a, b, c, d, e, f, Right y) = Right (a, b, c, d, e, f, y)

instance CoApplicative w => CoApplicative (EnvT e w) where
  nonempty (EnvT _ wv) = nonempty wv
  split (EnvT e we) = either (Left . EnvT e) (Right . EnvT e) (split we)
  splitMaybe (EnvT e wm) = EnvT e <$> splitMaybe wm
  splitList (EnvT e wxs) = EnvT e <$> splitList wxs

newtype CoAppComonad w a = CoAppComonad (w a) deriving Functor

-- | There is a derivable instance for Comonads,
-- but this will not be compatible with context shifts for most
-- Comonads (primarily only the products)
instance Comonad w => CoApplicative (CoAppComonad w) where
  nonempty (CoAppComonad wv) = extract wv
  split (CoAppComonad wab) =
    case extract wab of
      Left x -> Left (CoAppComonad $ fmap (either id (const x)) wab)
      Right y -> Right (CoAppComonad $ fmap (either (const y) id) wab)
