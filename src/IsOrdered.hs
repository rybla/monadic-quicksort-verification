module IsOrdered where

import           Liquid.ProofCombinators
import           Function
import           Relation


{-@
data IsOrdered a = IsOrdered
  { leq :: RelationD a
  , leq_transitive :: x:a -> y:a -> z:a -> {IsTransitive leq x y z}
  }
@-}
data IsOrdered a = IsOrdered
  { leq  :: RelationD a
  , leq_transitive :: a -> a -> a -> Proof
  }
