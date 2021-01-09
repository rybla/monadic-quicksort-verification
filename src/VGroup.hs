module VGroup where

import Function
import Liquid.ProofCombinators
import Relation
import VSemigroup

-- Data Class. A group is a semigroup with an invertible operator and an
-- identity element epsilon.
{-@
data Group a = Group
  { iSemigroup :: VSemigroup a
  , epsilon :: a
  , invert  :: Op1 a
  , op_identity   :: x:a -> {IsIdentity (op iSemigroup) epsilon x}
  , op_invertible :: x:a -> {IsInvertible (op iSemigroup) invert x}
  }
@-}
data Group a = Group
  { iSemigroup :: VSemigroup a,
    epsilon :: a,
    invert :: Op1 a,
    op_identity :: Property a,
    op_invertible :: Property a
  }
