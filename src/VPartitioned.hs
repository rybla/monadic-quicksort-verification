module VPartitioned where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation

-- NOTE. I should be parametrizing all my classes over `VPartitioned` rather
-- than LH's built-in vequality, however this would be very annoying given the
-- limited infixed-notation support. And I also this it might not be compatible
-- with LH's SMT-solver strategies perhaps? Not sure about that...

-- Data Class. A partitioned set is a set that is partitioned into vequivalence classes
-- (via the `eq` relation) which are preserved under bijections.
{-@
data VPartitioned a = VPartitioned
  { veq :: RelationD a
  , veq_reflexive  :: x:a ->               {IsReflexive  veq x}
  , veq_symmetric  :: x:a -> y:a ->        {IsSymmetric  veq x y}
  , veq_transitive :: x:a -> y:a -> z:a -> {IsTransitive veq x y z}
  }
@-}
data VPartitioned a = VPartitioned
  { veq :: RelationD a,
    veq_reflexive :: a -> Proof,
    veq_symmetric :: a -> a -> Proof,
    veq_transitive :: a -> a -> a -> Proof
  }
