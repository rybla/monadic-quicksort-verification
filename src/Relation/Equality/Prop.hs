{-# LANGUAGE IncoherentInstances #-}

module Relation.Equality.Prop where

import Function
import Language.Haskell.Liquid.ProofCombinators

{-
# Propositional Equality
-}

{-
## Definition
-}

{-@
measure eqprop :: a -> a -> Bool
@-}

data EqualityProp a = EqualityProp

{-@
type EqualProp a X Y = {w:EqualityProp a | eqprop X Y}
@-}

{-
### Axioms
-}

{-@ assume
fromSMT :: x:a -> y:a -> {_:Proof | x = y} -> EqualProp a {x} {y}
@-}
fromSMT :: a -> a -> Proof -> EqualityProp a
fromSMT x y pf = EqualityProp

{-@ assume
extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqualProp b {f x} {g x}) -> EqualProp (a -> b) {f} {g}
@-}
extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
extensionality f g pf = EqualityProp

{-@ assume
substitutability :: f:(a -> b) -> x:a -> y:a -> EqualProp a {x} {y} -> EqualProp b {f x} {f y}
@-}
substitutability :: (a -> b) -> a -> a -> EqualityProp a -> EqualityProp b
substitutability f x y pf = EqualityProp

{-
### Witnesses
-}

{-@ assume
toWitness :: x:a -> y:a -> {_:t | eqprop x y} -> EqualProp a {x} {y}
@-}
toWitness :: a -> a -> t -> EqualityProp a
toWitness x y pf = EqualityProp

{-@
fromWitness :: x:a -> y:a -> EqualProp a {x} {y} -> {_:Proof | eqprop x y}
@-}
fromWitness :: a -> a -> EqualityProp a -> Proof
fromWitness x y pf = trivial

{-
## Properties
-}

{-
### Equality

Combines together the equality properties:
- reflexivity
- symmetry
- transitivity
- substitutability
-}

{-@
class (Reflexivity a, Symmetry a, Transitivity a) => Equality a where
  __Equality :: {v:Maybe a | v = Nothing}
@-}
class (Reflexivity a, Symmetry a, Transitivity a) => Equality a where
  __Equality :: Maybe a

{-
### SMT Equality
-}

{-@
class EqSMT a where
  eqSMT :: x:a -> y:a -> {b:Bool | ((x = y) => b) && (b => (x = y))}
@-}
class EqSMT a where
  eqSMT :: a -> a -> Bool

{-
### Concreteness
-}

{-@
class Concreteness a where
  concreteness :: x:a -> y:a -> EqualProp a {x} {y} -> {_:Proof | x = y}
@-}
class Concreteness a where
  concreteness :: a -> a -> EqualityProp a -> Proof

instance EqSMT a => Concreteness a where
  concreteness x y pf = concreteness_EqSMT x y pf

{-@ assume
concreteness_EqSMT :: EqSMT a => x:a -> y:a -> EqualProp a {x} {y} -> {_:Proof | x = y}
@-}
concreteness_EqSMT :: EqSMT a => a -> a -> EqualityProp a -> Proof
concreteness_EqSMT _ _ _ = ()

{-
### Retractability
-}

{-@
class Retractability a b where
  retractability :: f:(a -> b) -> g:(a -> b) -> EqualProp (a -> b) {f} {g} -> (x:a -> EqualProp b {f x} {g x})
@-}
class Retractability a b where
  retractability :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> (a -> EqualityProp b)

instance Retractability a b where
  retractability f g ep_f_g x =
    substitutability (given x) f g ep_f_g
      ? (given x f) -- instantiate `f x`
      ? (given x g) -- instantiate `g x`

{-
### Reflexivity
-}

{-@
class Reflexivity a where
  reflexivity :: x:a -> EqualProp a {x} {x}
@-}
class Reflexivity a where
  reflexivity :: a -> EqualityProp a

instance Concreteness a => Reflexivity a where
  reflexivity x = fromSMT x x trivial

instance Reflexivity b => Reflexivity (a -> b) where
  reflexivity f =
    let ep_fx_fx x = reflexivity (f x)
     in extensionality f f ep_fx_fx

{-
### Symmetry
-}

{-@
class Symmetry a where
  symmetry :: x:a -> y:a -> EqualProp a {x} {y} -> EqualProp a {y} {x}
@-}
class Symmetry a where
  symmetry :: a -> a -> EqualityProp a -> EqualityProp a

instance Concreteness a => Symmetry a where
  symmetry x y ep_x_y =
    let e_x_y = concreteness x y ep_x_y
        e_y_x = e_x_y -- by SMT
     in fromSMT y x e_y_x

instance (Symmetry b, Retractability a b) => Symmetry (a -> b) where
  symmetry f g ep_f_g =
    let ep_fx_gx = retractability f g ep_f_g
        ep_gx_fx x = symmetry (f x) (g x) (ep_fx_gx x)
     in extensionality g f ep_gx_fx

{-
### Transitivity
-}

{-@
class Transitivity a where
  transitivity :: x:a -> y:a -> z:a -> EqualProp a {x} {y} -> EqualProp a {y} {z} -> EqualProp a {x} {z}
@-}
class Transitivity a where
  transitivity :: a -> a -> a -> EqualityProp a -> EqualityProp a -> EqualityProp a

instance Concreteness a => Transitivity a where
  transitivity x y z ep_x_y ep_y_z =
    let e_x_y = concreteness x y ep_x_y
        e_y_z = concreteness y z ep_y_z
        e_x_z = e_x_y &&& e_y_z -- by SMT
     in fromSMT x z e_x_z

instance (Transitivity b, Retractability a b) => Transitivity (a -> b) where
  transitivity f g h ep_f_g ep_g_h =
    let es_fx_gx = retractability f g ep_f_g
        es_gx_hx = retractability g h ep_g_h
        es_fx_hx x = transitivity (f x) (g x) (h x) (es_fx_gx x) (es_gx_hx x)
     in extensionality f h es_fx_hx

{-
## Lemmas
-}

{-@
alphaEquivalency :: Equality b => f:(a -> b) -> EqualProp (a -> b) {f} {(\x:a -> f x)}
@-}
alphaEquivalency :: Equality b => (a -> b) -> EqualityProp (a -> b)
alphaEquivalency f =
  extensionality f (\x -> f x) $ \x ->
    -- TODO: why does this not go through?
    -- reflexivity (f x) ? f x ? (\x -> f x) x
    undefined

{-@
betaEquivalencyTrivial :: Equality b => x:a -> y:b -> EqualProp b {y} {apply (\_:a -> y) x}
@-}
betaEquivalencyTrivial :: Equality b => a -> b -> EqualityProp b
betaEquivalencyTrivial = undefined
