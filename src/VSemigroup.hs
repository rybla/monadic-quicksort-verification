module VSemigroup where

import Function
import Liquid.ProofCombinators

-- Data Class. A semigroup is a TODO.
{-@
data VSemigroup a = VSemigroup
  { op :: Op2 a
  , op_associative :: x:a -> y:a -> z:a -> {IsAssociative op x y z}
  }
@-}
data VSemigroup a = VSemigroup
  { op :: Op2 a,
    op_associative :: a -> a -> a -> Proof
  }
