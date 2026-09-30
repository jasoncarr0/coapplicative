{-# LANGUAGE DeriveFunctor, TypeOperators, FlexibleContexts, UndecidableInstances #-}

-- | Provides Coapplicative typeclass and instances.
module Control.Coapplicative (Splittable(..), Coapplicative(..), CoappComonad(..)) where

import Control.Coapplicative.Traced
import Control.Comonad
import Control.Comonad.Env
import Control.Comonad.Traced hiding (Sum)
import Data.Void
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty
import Data.Maybe (mapMaybe)
import Data.Bifunctor
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
-- `reassoc . either id split . split = either split id . split . fmap reassoc`
-- where reassoc is the unique total function of type `(Either a (Either b c)) -> Either (Either a b) c`
-- `split . fmap (either f g) = either (fmap f) (fmap g) . split`
-- `split . fmap Left = Left`
-- `split . fmap Right = Right`
--
-- Every Comonad is Splittable, but not often in a
-- way that is compatible with the Comonad structure.
-- In particular, dup must distribute with split:
--
-- `duplicate . split = fmap split . split . duplicate`
class Functor f => Splittable f where
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


-- | A CoApplicative has both a cocartesian costrength and is splittable.
-- This is dual to the situation with Applicative, but all functors in
-- Haskell are implicitly strong with respect to product.
--
-- Every Comonad can be made into a Coapplicative, but not always
-- in a way that is compatible with the structure of duplicate.
--
-- Hence the situation with Applicative and Monad almost dualizes but
-- does not, because not all functors are costrong with respect to
-- sums.
--
-- `copure` is derivable from the other operations in a dual way to
-- Applicative's `pure`. Optimized functions may be provided but
-- must agree.
class Splittable f => Coapplicative f where
  costrength :: f (Either a b) -> Either a (f b)
  costrength = bimap copure id . split
  copure :: f a -> a
  copure = either id (absurd . nonempty) . costrength . fmap Left

instance Splittable Identity where
  nonempty (Identity v) = v
  split (Identity (Left x)) = Left (Identity x)
-- This is compatible
  split (Identity (Right y)) = Right (Identity y)
instance Coapplicative Identity where
  costrength (Identity (Left x)) = Left x
  costrength (Identity (Right y)) = Right (Identity y)
  copure = runIdentity

-- | Filters out elements which do not match the head.
instance Splittable NonEmpty where
  nonempty (v :| _) = v
  split (Left x :| rest) = Left (x :| mapMaybe leftToMaybe rest)
  split (Right x :| rest) = Right (x :| mapMaybe rightToMaybe rest)
instance Coapplicative NonEmpty where
  costrength (Left x :| _) = Left x
  costrength (Right y :| rest) = Right (y :| mapMaybe rightToMaybe rest)
  copure = extract

instance (Splittable f, Splittable g) => Splittable (Sum f g) where
  nonempty (InL fv) = nonempty fv
  nonempty (InR gv) = nonempty gv
  split (InL fe) = bimap InL InL (split fe)
  split (InR ge) = bimap InR InR (split ge)
  splitMaybe (InL fm) = InL <$> (splitMaybe fm)
  splitMaybe (InR gm) = InR <$> (splitMaybe gm)
  splitList (InL fxs) = InL <$> (splitList fxs)
  splitList (InR gxs) = InR <$> (splitList gxs)
instance (Coapplicative f, Coapplicative g) => Coapplicative (Sum f g) where
  costrength (InL fe) = bimap id InL $ costrength fe
  costrength (InR ge) = bimap id InR $ costrength ge
  copure (InL fx) = copure fx
  copure (InR gx) = copure gx

instance Splittable ((,) a) where
  nonempty (_, v) = v
  split (a, Left x) = Left (a, x)
  split (a, Right y) = Right (a, y)
instance Coapplicative ((,) a) where
  costrength (_, Left x) = Left x
  costrength (a, Right y) = Right (a, y)
  copure (_, x) = x

instance Splittable ((,,) a b) where
  nonempty (_, _, v) = v
  split (a, b, Left x) = Left (a, b, x)
  split (a, b, Right y) = Right (a, b, y)
instance Coapplicative ((,,) a b) where
  costrength (_, _, Left x) = Left x
  costrength (a, b, Right y) = Right (a, b, y)
  copure (_, _, x) = x

instance Splittable ((,,,) a b c) where
  nonempty (_, _, _, v) = v
  split (a, b, c, Left x) = Left (a, b, c, x)
  split (a, b, c, Right y) = Right (a, b, c, y)
instance Coapplicative ((,,,) a b c) where
  costrength (_, _, _, Left x) = Left x
  costrength (a, b, c, Right y) = Right (a, b, c, y)
  copure (_, _, _, x) = x

instance Splittable ((,,,,) a b c d) where
  nonempty (_, _, _, _, v) = v
  split (a, b, c, d, Left x) = Left (a, b, c, d, x)
  split (a, b, c, d, Right y) = Right (a, b, c, d, y)
instance Coapplicative ((,,,,) a b c d) where
  costrength (_, _, _, _, Left x) = Left x
  costrength (a, b, c, d, Right y) = Right (a, b, c, d, y)
  copure (_, _, _, _, x) = x

instance Splittable ((,,,,,) a b c d e) where
  nonempty (_, _, _, _, _, v) = v
  split (a, b, c, d, e, Left x) = Left (a, b, c, d, e, x)
  split (a, b, c, d, e, Right y) = Right (a, b, c, d, e, y)
instance Coapplicative ((,,,,,) a b c d e) where
  costrength (_, _, _, _, _, Left x) = Left x
  costrength (a, b, c, d, e, Right y) = Right (a, b, c, d, e, y)
  copure (_, _, _, _, _, x) = x

instance Splittable ((,,,,,,) a b c d e f) where
  nonempty (_, _, _, _, _, _, v) = v
  split (a, b, c, d, e, f, Left x) = Left (a, b, c, d, e, f, x)
  split (a, b, c, d, e, f, Right y) = Right (a, b, c, d, e, f, y)
instance Coapplicative ((,,,,,,) a b c d e f) where
  costrength (_, _, _, _, _, _, Left x) = Left x
  costrength (a, b, c, d, e, f, Right y) = Right (a, b, c, d, e, f, y)
  copure (_, _, _, _, _, _, x) = x

instance Splittable w => Splittable (EnvT e w) where
  nonempty (EnvT _ wv) = nonempty wv
  split (EnvT e we) = bimap (EnvT e) (EnvT e) (split we)
  splitMaybe (EnvT e wm) = EnvT e <$> splitMaybe wm
  splitList (EnvT e wxs) = EnvT e <$> splitList wxs
instance Coapplicative w => Coapplicative (EnvT e w) where
  costrength (EnvT e wx) = bimap id (EnvT e) $ costrength wx
  copure (EnvT _ wx) = copure wx

-- | In order to have a consistent view of the context, we must be able
-- to replace non-matching parts of the context in a consistent way.
--
-- Largely no Monoid can satisfy this, but this instance is provided because
-- it exists, and because it is a non-trivial law-abiding instance
-- which is not filtering a zipper.
--
-- Creating non-law-abiding TinyGroup instances will allow for this instance
-- to be used in a way which is not quite compatible with the Comonad instance.
instance (Splittable w, TinyGroup m) => Splittable (TracedT m w) where
  nonempty = nonempty . fmap (\t -> t mempty) . runTracedT
  split = coerce . split . fmap splitCyclic . runTracedT
    where
      -- This is somehwa
      splitCyclic :: TinyGroup m => (m -> Either a b) -> Either (m -> a) (m -> b)
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
instance (Coapplicative w, TinyGroup m) => Coapplicative (TracedT m w) where
  copure (TracedT wa) = copure (($ mempty) <$> wa)

instance Splittable f => Splittable (M1 i c f) where
  nonempty (M1 fv) = nonempty fv
  split (M1 fab) = coerce (split fab)
  splitMaybe (M1 fa) = M1 <$> splitMaybe fa
  splitList (M1 fxs) = M1 <$> splitList fxs
instance Coapplicative f => Coapplicative (M1 i c f) where
  copure (M1 fa) = copure fa

-- identical to Sum
instance (Splittable f, Splittable g) => Splittable (f :+: g) where
  nonempty (L1 fv) = nonempty fv
  nonempty (R1 gv) = nonempty gv
  split (L1 fe) = bimap L1 L1 (split fe)
  split (R1 ge) = bimap R1 R1 (split ge)
  splitMaybe (L1 fm) = L1 <$> (splitMaybe fm)
  splitMaybe (R1 gm) = R1 <$> (splitMaybe gm)
  splitList (L1 fxs) = L1 <$> (splitList fxs)
  splitList (R1 gxs) = R1 <$> (splitList gxs)
instance (Coapplicative f, Coapplicative g) => Coapplicative (f :+: g) where
  copure (L1 fa) = copure fa
  copure (R1 ga) = copure ga
  costrength (L1 fa) = bimap id L1 $ costrength fa
  costrength (R1 ga) = bimap id R1 $ costrength ga

instance (Splittable f, Splittable g) => Splittable (f :.: g) where
  nonempty (Comp1 fgv) = nonempty (nonempty <$> fgv)
  split (Comp1 fgab) =
    coerce $
    split (fmap split fgab)
  splitMaybe (Comp1 fga) = fmap Comp1 $ splitMaybe $ fmap splitMaybe fga
  splitList (Comp1 fgxs) = fmap Comp1 $ splitList $ fmap splitList fgxs
instance (Coapplicative f, Coapplicative g) => Coapplicative (f :.: g) where
  copure (Comp1 fgx) = copure $ copure <$> fgx
  costrength (Comp1 fgx) =
    coerce $ costrength $ fmap costrength fgx

instance Splittable Par1 where
  nonempty (Par1 v) = v
  split (Par1 (Left a)) = Left (Par1 a)
  split (Par1 (Right a)) = Right (Par1 a)
  splitMaybe (Par1 m) = Par1 <$> m
  splitList (Par1 xs) = Par1 <$> xs
instance Coapplicative Par1 where
  copure (Par1 x) = x

instance Splittable f => Splittable (Rec1 f) where
  nonempty (Rec1 fv) = nonempty fv
  split (Rec1 fab) = coerce (split fab)
  splitMaybe (Rec1 fa) = coerce $ splitMaybe fa
  splitList (Rec1 fxs) = coerce $ splitList fxs
instance Coapplicative f => Coapplicative (Rec1 f) where
  copure (Rec1 fx) = copure fx
  costrength (Rec1 fx) = coerce $ costrength fx

instance (Generic1 f, Splittable (Rep1 f)) => Splittable (Generically1 f) where
  nonempty (Generically1 fa) = nonempty (from1 fa)
  split (Generically1 fab) =
    bimap (Generically1 . to1) (Generically1 . to1)
    (split (from1 fab))
  splitMaybe (Generically1 fa) = fmap Generically1 $ fmap to1 $ splitMaybe $ from1 fa
  splitList (Generically1 fxs) = fmap Generically1 $ fmap to1 $ splitList $ from1 fxs
instance (Generic1 f, Coapplicative (Rep1 f)) => Coapplicative (Generically1 f) where
  copure (Generically1 fx) = copure (from1 fx)
  costrength (Generically1 fx) = bimap id (Generically1 . to1) $ costrength $ from1 fx

-- | There is a derivable instance for any Comonad,
-- but this will not be compatible with context shifts for most instances.
-- 
-- In the context of pattern-matching, this means that reaching the same branch
-- two different ways may result in conflicting views of the surrounding context.
-- (only the context which lands on the same side of the branch is consistent)
newtype CoappComonad w a = CoappComonad { runCoappComonad :: w a } deriving (Functor)

instance Comonad w => Splittable (CoappComonad w) where
  nonempty (CoappComonad wv) = extract wv
  split (CoappComonad wab) =
    case extract wab of
      Left x -> Left (CoappComonad $ fmap (either id (const x)) wab)
      Right y -> Right (CoappComonad $ fmap (either (const y) id) wab)
instance Comonad w => Coapplicative (CoappComonad w) where
  copure (CoappComonad wx) = extract wx
  costrength (CoappComonad wab) =
    case extract wab of
      Left x -> Left x
      Right y -> Right (CoappComonad $ fmap (either (const y) id) wab)

instance Comonad w => Comonad (CoappComonad w) where
  extract = extract . runCoappComonad
  {- coerce gets blocked by unknown roles sadly -}
  duplicate (CoappComonad wa) = CoappComonad (fmap CoappComonad (duplicate wa))


