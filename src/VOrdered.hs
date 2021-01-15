module VOrdered where

import Function
import Liquid.ProofCombinators
import Relation

-- Data Class. A (totally) ordered set is TODO.
{-@
data VOrdered a = VOrdered
  { vleq :: RelationD a
  , vleq_reflexive     :: x:a -> {IsReflexive vleq x}
  , vleq_antisymmetric :: x:a -> y:a -> {IsAntisymmetric vleq x y}
  , vleq_transitive    :: x:a -> y:a -> z:a -> {IsTransitive vleq x y z}
  , vleq_connex :: x:a -> y:a -> {IsConnex vleq x y} }
@-}
data VOrdered a = VOrdered
  { vleq :: RelationD a,
    vleq_reflexive :: Property a,
    vleq_antisymmetric :: Property2 a,
    vleq_transitive :: Property3 a,
    vleq_connex :: Property2 a
  }
