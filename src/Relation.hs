module Relation where

import           Liquid.ProofCombinators


-- `Relation<n>` is an N-ary relation.
-- `Relation<n>D` is a homogenous N-ary relation.

{-@ type Predicate a = a -> Bool @-}
type Predicate a = a -> Bool

{-@ type Relation a b = a -> b -> Bool @-}
type Relation a b = a -> b -> Bool

{-@ type RelationD a = Relation a a @-}
type RelationD a = Relation a a

{-@ type Relation3 a b c = a -> b -> c -> Bool @-}
type Relation3 a b c = a -> b -> c -> Bool

{-@ type Relation3D a = Relation3 a a a @-}
type Relation3D a = Relation3 a a a


-- Predicates.
-- NOTE. Predicate parameters must be capitalized.

{-@ predicate IsReflexive  R X     = R X X @-}
{-@ predicate IsSymmetric  R X Y   = R X Y => R Y X @-}
{-@ predicate IsTransitive R X Y Z = R X Y => R Y Z => R X Y @-}

{-@ predicate PreservesMeasure   M F X   = M X   =  M (F X) @-}
{-@ predicate PreservesPredicate P F X   = P X   => P (F X) @-}
{-@ predicate PreservesRelation  R F X Y = R X Y => R (F X) (F Y) @-}
