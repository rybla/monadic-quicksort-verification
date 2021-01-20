module VFunctor where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation

-- Data Class. A functor is a TODO
{-@
data VFunctor f = VFunctor
  { vmapF :: forall a b . (a -> b) -> (f a -> f b)
  , vmapF_vid :: forall a . x:f a -> {vmapF vid x = vid x}
  }
@-}
data VFunctor f = VFunctor
  { vmapF :: forall a b. (a -> b) -> (f a -> f b),
    vmapF_vid :: forall a. f a -> Proof
  }
