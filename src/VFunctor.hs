module VFunctor where

import Function
import Liquid.ProofCombinators
import Relation

-- Data Class. A functor is a TODO
{-@
data VFunctor f = VFunctor
  { vmap :: forall a b . (a -> b) -> (f a -> f b)
  , vmap_vid :: forall a . x:f a -> {vmap vid x = vid x}
  }
@-}
data VFunctor f = VFunctor
  { vmap :: forall a b. (a -> b) -> (f a -> f b),
    vmap_vid :: forall a. f a -> Proof
  }
