module IsMonoid where

import           Liquid.ProofCombinators
import           Function
import           IsSemigroup


{-@
data IsMonoid a = IsMonoid
  { isSemigroup :: IsSemigroup a
  , epsilon :: a
  , op_identity :: x:a -> {IsIdentity (op isSemigroup) epsilon x}
  }
@-}
data IsMonoid a = IsMonoid
  { isSemigroup :: IsSemigroup a
  , epsilon :: a
  , op_identity :: a -> Proof
  }
