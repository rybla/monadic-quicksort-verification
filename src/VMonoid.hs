module VMonoid where

import Function
import Liquid.ProofCombinators
import VSemigroup

-- Data Class. A monoid is TODO.
{-@
data VMonoid a = VMonoid
  { iSemigroup :: VSemigroup a
  , epsilon :: a
  , op_identity :: x:a -> {IsIdentity (op iSemigroup) epsilon x}
  }
@-}
data VMonoid a = VMonoid
  { iSemigroup :: VSemigroup a,
    epsilon :: a,
    op_identity :: a -> Proof
  }
