{-# LANGUAGE DeriveFunctor, TypeOperators, FlexibleContexts, UndecidableInstances #-}

-- | Provides CoApplicative typeclass and instances.
module Control.CoApplicative (CoApplicative(..), CoAppComonad(..)) where

import Control.CoApplicative.Traced(FinCyclic(..))
import Control.Comonad
import Control.Comonad.Trans.Env
import Control.Comonad.Trans.Traced
import Data.Void
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty
import Data.Maybe (mapMaybe)
import Data.Functor.Sum
import Data.Coerce
import GHC.Generics

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
  -- discarding the context of nil values.
  -- I.e. each position in the resulting
  -- list will "collect" the corresponding f a
  splitList :: f [a] -> [f a]
  splitList = roll . maybe Nothing (Just . dorec) . splitMaybe . fmap unroll
    {- TODO: make this fuse? At least on its output -}
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

-- | Filters out elements which do not match the head.
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

-- | In order to have a consistent view of the context, we must be able
-- to replace non-matching parts of the context in a consistent way.
--
-- A finite cyclic group allows us to choose a new index for any non-matching
-- location in a way that always agrees and agrees with Monoidal shifts
--
-- The FinCyclic class is presented in Control.CoApplicative.Traced but this
-- instance is here to avoid an orphan instance.
instance (CoApplicative w, FinCyclic m) => CoApplicative (TracedT m w) where
  nonempty = nonempty . fmap (\t -> t mempty) . runTracedT
  split = either (Left . TracedT) (Right . TracedT) . split . fmap splitCyclic . runTracedT
    where
      splitCyclic :: FinCyclic m => (m -> Either a b) -> Either (m -> a) (m -> b)
      splitCyclic t =
        case t mempty of
          Left _ -> Left findLefts
          Right _ -> Right findRights
        where
          -- These terminate because generator will eventually
          -- cover the entire group, and by the calling condition
          -- we know that at least one element will eventually
          -- be found on the correct side of the Either
          findLefts i =
            case t i of
              Left x -> x
              Right _ -> findLefts (i <> generator)
          findRights i =
            case t i of
              Left _ -> findRights (i <> generator)
              Right x -> x

instance CoApplicative f => CoApplicative (M1 i c f) where
  nonempty (M1 fv) = nonempty fv
  split (M1 fab) = either (Left . M1) (Right . M1) (split fab)
  splitMaybe (M1 fa) = M1 <$> splitMaybe fa
  splitList (M1 fxs) = M1 <$> splitList fxs

-- identical to Sum
instance (CoApplicative f, CoApplicative g) => CoApplicative (f :+: g) where
  nonempty (L1 fv) = nonempty fv
  nonempty (R1 gv) = nonempty gv
  split (L1 fe) = either (Left . L1) (Right . L1) (split fe)
  split (R1 ge) = either (Left . R1) (Right . R1) (split ge)
  splitMaybe (L1 fm) = L1 <$> (splitMaybe fm)
  splitMaybe (R1 gm) = R1 <$> (splitMaybe gm)
  splitList (L1 fxs) = L1 <$> (splitList fxs)
  splitList (R1 gxs) = R1 <$> (splitList gxs)

instance (CoApplicative f, CoApplicative g) => CoApplicative (f :.: g) where
  nonempty (Comp1 fgv) = nonempty (nonempty <$> fgv)
  split (Comp1 fgab) =
    either (Left . Comp1) (Right . Comp1) $
    split (fmap split fgab)
  splitMaybe (Comp1 fga) = fmap Comp1 $ splitMaybe $ fmap splitMaybe fga
  splitList (Comp1 fgxs) = fmap Comp1 $ splitList $ fmap splitList fgxs

instance CoApplicative Par1 where
  nonempty (Par1 v) = v
  split (Par1 (Left a)) = Left (Par1 a)
  split (Par1 (Right a)) = Right (Par1 a)
  splitMaybe (Par1 m) = Par1 <$> m
  splitList (Par1 xs) = Par1 <$> xs

instance CoApplicative f => CoApplicative (Rec1 f) where
  nonempty (Rec1 fv) = nonempty fv
  split (Rec1 fab) = either (Left . Rec1) (Right . Rec1) (split fab)
  splitMaybe (Rec1 fa) = coerce $ splitMaybe fa
  splitList (Rec1 fxs) = coerce $ splitList fxs

instance (Generic1 f, CoApplicative (Rep1 f)) => CoApplicative (Generically1 f) where
  nonempty (Generically1 fa) = nonempty (from1 fa)
  split (Generically1 fab) =
    either (Left . Generically1 . to1) (Right . Generically1 . to1)
    (split (from1 fab))
  splitMaybe (Generically1 fa) = fmap Generically1 $ fmap to1 $ splitMaybe $ from1 fa
  splitList (Generically1 fxs) = fmap Generically1 $ fmap to1 $ splitList $ from1 fxs

-- | There is a derivable instance for any Comonad,
-- but this will not be compatible with context shifts for most instances.
-- 
-- In the context of pattern-matching, this means that reaching the same branch
-- two different ways may result in conflicting views of the surrounding context.
-- (only the context which lands on the same side of the branch is consistent)
newtype CoAppComonad w a = CoAppComonad { runCoAppComonad :: w a } deriving (Functor)

instance Comonad w => CoApplicative (CoAppComonad w) where
  nonempty (CoAppComonad wv) = extract wv
  split (CoAppComonad wab) =
    case extract wab of
      Left x -> Left (CoAppComonad $ fmap (either id (const x)) wab)
      Right y -> Right (CoAppComonad $ fmap (either (const y) id) wab)

instance Comonad w => Comonad (CoAppComonad w) where
  extract = extract . runCoAppComonad
  {- coerce gets blocked by unknown roles sadly -}
  duplicate (CoAppComonad wa) = CoAppComonad (fmap CoAppComonad (duplicate wa))


