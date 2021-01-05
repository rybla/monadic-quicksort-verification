module IsEq where

import           Liquid.ProofCombinators
import           Function
import           Relation


{-@
data IsEq a = IsEq
  { eq :: RelationD a
  , eq_reflexive  :: x:a ->               {IsReflexive  eq x}
  , eq_symmetric  :: x:a -> y:a ->        {IsSymmetric  eq x y}
  , eq_transitive :: x:a -> y:a -> z:a -> {IsTransitive eq x y z}
  }
@-}
data IsEq a = IsEq
  { eq :: RelationD a
  , eq_reflexive  :: a ->           Proof
  , eq_symmetric  :: a -> a ->      Proof
  , eq_transitive :: a -> a -> a -> Proof
  }
