module VPartitioned where

import           Liquid.ProofCombinators
import           Function
import           Relation


-- NOTE. I should be parametrizing all my classes over `VPartitioned` rather
-- than LH's built-in equality, however this would be very annoying given the
-- limited infixed-notation support. And I also this it might not be compatible
-- with LH's SMT-solver strategies perhaps? Not sure about that...


-- Data Class. A partitioned set is a set that is partitioned into equivalence classes
-- (via the `eq` relation) which are preserved under bijections.
{-@
data VPartitioned a = VPartitioned
  { eq :: RelationD a
  , eq_reflexive  :: x:a ->               {IsReflexive  eq x}
  , eq_symmetric  :: x:a -> y:a ->        {IsSymmetric  eq x y}
  , eq_transitive :: x:a -> y:a -> z:a -> {IsTransitive eq x y z}
  }
@-}
data VPartitioned a = VPartitioned
  { eq :: RelationD a
  , eq_reflexive  :: a ->           Proof
  , eq_symmetric  :: a -> a ->      Proof
  , eq_transitive :: a -> a -> a -> Proof
  }
