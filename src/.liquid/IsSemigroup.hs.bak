module IsSemigroup where

import           Liquid.ProofCombinators
import           Function


{-@
data IsSemigroup a = IsSemigroup
  { op :: Op2 a
  , op_associative :: x:a -> y:a -> z:a -> {IsAssociative op x y z}
  }
@-}
data IsSemigroup a = IsSemigroup
  { op :: Op2 a
  , op_associative :: a -> a -> a -> Proof
  }
