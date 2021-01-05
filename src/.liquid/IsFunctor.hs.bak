module IsFunctor where

import           Liquid.ProofCombinators
import           Relation
import           Function


{-@
data IsFunctor f = IsFunctor
  { vmap :: forall a b . (a -> b) -> (f a -> f b)
  , vmap_vid :: forall a . x:f a -> {vmap vid x = vid x}
  }
@-}
data IsFunctor f = IsFunctor
  { vmap :: forall a b . (a -> b) -> (f a -> f b)
  , vmap_vid :: forall a . f a -> Proof
  }
