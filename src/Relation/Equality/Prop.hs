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
measure eqprop :: a -> a -> EqualityProp a -> Bool
@-}

{-@
type EqualProp a X Y = {w:EqualityProp a | eqprop X Y w}
@-}

{-@
data EqualityProp :: * -> * where
    FromSMT :: x:a -> y:a -> {_:() | x = y} -> EqualProp a {x} {y}
  | Extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqualProp b {f x} {g x}) -> EqualProp (a -> b) {f} {g}
  | Substitutability :: x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
data EqualityProp :: * -> * where
  FromSMT :: a -> a -> Proof -> EqualityProp a
  Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
  Substitutability :: a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

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
class (Reflexivity a, Symmetry a, Transitivity a, Substitutability a) => Equality a where
  __Equality :: {v:Maybe a | v = Nothing}
@-}
class (Reflexivity a, Symmetry a, Transitivity a, Substitutability a) => Equality a where
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
  retractability f g eqProp_f_g x =
    Substitutability f g (given x) eqProp_f_g
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
  reflexivity x = FromSMT x x trivial

instance Reflexivity b => Reflexivity (a -> b) where
  reflexivity f =
    let eqProp_fx_fx x = reflexivity (f x)
     in Extensionality f f eqProp_fx_fx

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
  symmetry x y eqProp_x_y =
    let eq_x_y = concreteness x y eqProp_x_y
        eq_y_x = eq_x_y -- by SMT
     in FromSMT y x eq_y_x

instance (Symmetry b, Retractability a b) => Symmetry (a -> b) where
  symmetry f g eqProp_f_g =
    let eqProp_fx_gx = retractability f g eqProp_f_g
        eqProp_gx_fx x = symmetry (f x) (g x) (eqProp_fx_gx x)
     in Extensionality g f eqProp_gx_fx

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
  transitivity x y z eqProp_x_y eqProp_y_z =
    let eq_x_y = concreteness x y eqProp_x_y
        eq_y_z = concreteness y z eqProp_y_z
        eq_x_z = eq_x_y &&& eq_y_z -- by SMT
     in FromSMT x z eq_x_z

instance (Transitivity b, Retractability a b) => Transitivity (a -> b) where
  transitivity f g h eqProp_f_g eqProp_g_h =
    let eSMT_fx_gx = retractability f g eqProp_f_g
        eSMT_gx_hx = retractability g h eqProp_g_h
        eSMT_fx_hx x = transitivity (f x) (g x) (h x) (eSMT_fx_gx x) (eSMT_gx_hx x)
     in Extensionality f h eSMT_fx_hx

{-
### Substitutability
-}

{-@
class Substitutability a where
  substitutability :: forall b. x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
class Substitutability a where
  substitutability :: forall b. a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

instance Substitutability a where
  substitutability x y c eqProp_x_y = Substitutability x y c eqProp_x_y
