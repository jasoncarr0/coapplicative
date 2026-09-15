module Control.CoApplicative.Traced (FinCyclic(..)) where

import Control.CoApplicative
import Control.Comonad.Trans.Traced
import Data.Bits (Xor)

-- | A cyclic group.
-- Every element must be equal to some power of `generator`
-- and append must be cancellable
--
-- The choice of generator is unique only up to monoidal isomorphism
class Monoid m => FinCyclic m where
  generator :: m

instance FinCyclic () where
  generator = ()

instance FinCyclic (Xor Bool) where
  generator = Xor True

instance FinCyclic a => FinCyclic (Solo a) where
  generator = Solo generator

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

instance (CoApplicative w, FinCyclic m) => CoApplicative (TracedT m w) where
  nonempty = nonempty . fmap (\t -> t mempty) . runTracedT
  split = either (Left . TracedT) (Right . TracedT) . split . fmap splitCyclic . runTracedT
