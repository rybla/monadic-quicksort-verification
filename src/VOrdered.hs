module VOrdered where

import           Liquid.ProofCombinators
import           Function
import           Relation


-- Data Class. A (totally) ordered set is TODO.
{-@
data VOrdered a = VOrdered
  { leq :: RelationD a
  , leq_reflexive     :: x:a -> {IsReflexive leq x}
  , leq_antisymmetric :: x:a -> y:a -> {IsAntisymmetric leq x y}
  , leq_transitive    :: x:a -> y:a -> z:a -> {IsTransitive leq x y z}
  , leq_connex :: x:a -> y:a -> {IsConnex leq x y} }
@-}
data VOrdered a = VOrdered
  { leq :: RelationD a
  , leq_reflexive     :: Property a
  , leq_antisymmetric :: Property2 a
  , leq_transitive    :: Property3 a
  , leq_connex :: Property2 a
  }
