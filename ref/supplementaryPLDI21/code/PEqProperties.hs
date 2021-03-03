{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt"     @-}

module PEqProperties where

import Language.Haskell.Liquid.ProofCombinators
import PropositionalEquality
import Prelude hiding (flip)

infixl 3 =~=

(=~=) :: a -> a -> a
_ =~= y = y

{-@ class Reflexivity a where
      refl :: x:a -> EqRT a {x} {x}
@-}

class Reflexivity a where
  refl :: a -> EqT a

instance AEq a => Reflexivity a where
  refl a = EqSMT a a (reflP a)

instance Reflexivity b => Reflexivity (a -> b) where
  refl f = EqFun f f (\a -> refl (f a))

{-@ class Symmetry a where
      sym :: x:a -> y:a -> EqRT a {x} {y} -> EqRT a {y} {x}
@-}

class Symmetry a where
  sym :: a -> a -> EqT a -> EqT a

instance SMTEq a => Symmetry a where
  sym l r pf = eqSMT r l (toSMT l r (pf `const` reflP r))

instance (Symmetry b) => Symmetry (a -> b) where
  sym l r pf =
    EqFun r l $ \a ->
      sym
        (l a)
        (r a)
        (EqCtx l r pf (dollar a) ? (dollar a l) ? (dollar a r))

{-@ class Transitivity a where
      trans :: x:a -> y:a -> z:a -> EqRT a {x} {y} -> EqRT a {y} {z} -> EqRT a {x} {z}
@-}

class Transitivity a where
  trans :: a -> a -> a -> EqT a -> EqT a -> EqT a

instance SMTEq a => Transitivity a where
  trans x y z pfXY pfYZ = eqSMT x z $ toSMT x y pfXY ? toSMT y z (pfYZ `const` reflP y)

instance Transitivity b => Transitivity (a -> b) where
  trans x y z pfXY pfYZ =
    EqFun
      x
      z
      ( \a ->
          trans
            (x a)
            (y a)
            (z a)
            (EqCtx x y pfXY (dollar a) ? dollar a x ? dollar a y)
            (EqCtx y z pfYZ (dollar a) ? dollar a y ? dollar a z)
      )

{-@ class Congruence a b where
      cong :: x:a -> y:a -> EqRT a {x} {y} -> ctx:(a -> b) -> EqRT b {ctx x} {ctx y}
@-}

class Congruence a b where
  cong :: a -> a -> EqT a -> (a -> b) -> EqT b

instance (SMTEq a, AEq b) => Congruence a b where
  cong x y pf ctx = eqSMT (ctx x) (ctx y) (toSMT x y (pf `const` reflP (ctx x)))

instance (Congruence a c) => Congruence a (b -> c) where
  cong x y pf ctx =
    EqFun (ctx x) (ctx y) (\b -> cong x y pf (flip ctx b) ? flip ctx b x ? flip ctx b y)

-------------------------------------------------------------------------------

-- | Completeness WRT SMT -----------------------------------------------------

-------------------------------------------------------------------------------

class AEq a => SMTEq a where
  toSMT :: a -> a -> EqT a -> ()

{-@ class AEq a => SMTEq a where
       toSMT :: x:a -> y:a -> EqRT a {x} {y} -> { x = y} @-}

instance AEq a => SMTEq a where
  toSMT x y _ = aEqToSMT x y

{-@ assume aEqToSMT :: AEq a => x:a -> y:a -> {x = y} @-}
aEqToSMT :: AEq a => a -> a -> ()
aEqToSMT _ _ = ()

-------------------------------------------------------------------------------

-- | Helpers ------------------------------------------------------------------

-------------------------------------------------------------------------------

{-@ reflect flip @-}
flip :: (a -> b -> c) -> (b -> a -> c)
flip f a b = f b a

{-@ reflect dollar @-}
dollar :: a -> (a -> b) -> b
dollar x f = f x
