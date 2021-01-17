module Relation where

import Language.Haskell.Liquid.ProofCombinators

-- Types. Forms of generic relations.
-- - `Relation<n>` is an `n`-ary relation.
-- - `Relation<n>D` is a homogenous `n`-ary relation.

type Predicate a = a -> Bool

type Relation a b = a -> b -> Bool

type RelationD a = Relation a a

type Relation3 a b c = a -> b -> c -> Bool

type Relation3D a = Relation3 a a a

-- Types. Forms of generic homogeneous properties.
-- - `Property<n>` is a homogeneous `n`-ary property.
-- - `Property<n>D` is a homogeneous `n`-ary property.

type Property a = a -> Proof

type Property2 a = a -> a -> Proof

type Property3 a = a -> a -> a -> Proof

-- Predicates.
-- NOTE. Predicate parameters must be capitalized.

-- Predicates. Forms of (homogenous) relations.
{-@ predicate IsReflexive     R X     = R X X @-}
{-@ predicate IsSymmetric     R X Y   = R X Y => R Y X @-}
{-@ predicate IsTransitive    R X Y Z = R X Y => R Y Z => R X Y @-}
{-@ predicate IsConnex        R X Y   = R X Y || R Y X @-}
{-@ predicate IsAntisymmetric R X Y   = R X Y => R Y X => X = Y @-}

-- Predicates. Forms of property-preserving relations.
{-@ predicate PreservesMeasure   M F X   = M (F X)       =  M X @-}
{-@ predicate PreservesPredicate P F X   = P (F X)       => P X @-}
{-@ predicate PreservesRelation  R F X Y = R (F X) (F Y) => R X Y @-}
