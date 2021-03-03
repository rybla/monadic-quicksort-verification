module Equality where

import Language.Haskell.Liquid.ProofCombinators

-- Measure. Uninterpretted propositional equality.
{-@ measure peq :: a -> a -> Bool @-}

-- Type. Type-indexed propositional equality.
{-@ type PEq a x y = {VV:PBEq a | peq x y} @-}

-- Data. Axiom system for propositional equality.
{-@
data PBEq :: * -> * where
    BEq :: forall a. x:a -> y:a -> {pf:Proof | x = y} -> PEq a x y
  | XEq :: forall a b. f:(a -> b) -> g:(a -> b) -> (x:a -> PEq b (f x) (g x)) -> PEq (a -> b) f g
  | CEq :: x:a -> y:a -> ctx:(a -> b) -> PEq a x y -> PEq b (ctx x) (ctx y)
@-}
data PBEq :: * -> * where
  BEq :: forall a. a -> a -> Proof -> PBEq a
  XEq :: forall a b. (a -> b) -> (a -> b) -> (a -> PBEq b) -> PBEq (a -> b)
  CEq :: forall a b. a -> a -> (a -> b) -> PBEq a -> PBEq b

infixl 3 ==*

{-@
assume (==*) :: forall a. x:a -> {y:a | peq x y} -> {z:a | peq z y && peq z x}
@-}
(==*) :: a -> a -> a
_ ==* x = x
{-# INLINE (==*) #-}

{-@ reflect isBEq @-}
isBEq :: PBEq a -> Bool
isBEq (BEq _ _ _) = True
isBEq _ = False

-- Axiom. Extract native functional equality from `BEq`-constructed
-- propositional equality.
{-@
assume fromPBEq :: forall a. x:a -> y:a -> {pf:PBEq a | peq x y && isBEq pf} -> {x = y}
@-}
fromPBEq :: forall a. a -> a -> PBEq a -> Proof
fromPBEq _ _ (BEq _ _ _) = trivial
fromPBEq _ _ (XEq _ _ _) = trivial -- impossible
fromPBEq _ _ (CEq _ _ _ _) = trivial -- impossible

-- Axiom. Extract native (pointwise) function equality from propositional (PBEq)
-- function equality.
{-@
assume fromPBEq_f :: forall a b. f:(a -> b) -> g:(a -> b) -> {_:PBEq (a -> b) | peq f g} -> x:a -> {f x = g x}
@-}
fromPBEq_f :: forall a b. (a -> b) -> (a -> b) -> PBEq (a -> b) -> a -> Proof
fromPBEq_f _ _ _ _ = trivial

-- Function. Apply a function to its argument.
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

--------------------------------------------------------------------------------
-- η-equivalence
--------------------------------------------------------------------------------

-- Theorem. Pointwise η-equivalence:
--
--  f = λx(f x)
--
-- Proven by extracting from propositional equality via `toEq`.
{-@
assume eta_equivalence ::
  forall a b. f:(a -> b) -> x:a ->
  {f x = apply (\x:a -> f x) x}
@-}
eta_equivalence :: forall a b. (a -> b) -> a -> Proof
eta_equivalence f = fromPBEq_f f (\x -> f x) (eta_equivalence_PBEq f)

-- Lemma. Propositional η-equivalence.
{-@
assume eta_equivalence_PBEq ::
  forall a b. f:(a -> b) ->
  {_:PBEq (a -> b) | peq f (\x:a -> f x)}
@-}
eta_equivalence_PBEq :: forall a b. (a -> b) -> PBEq (a -> b)
eta_equivalence_PBEq f = XEq f (\x -> f x) (eta_equivalence_PBEq_pointwise f)

-- Lemma. Propositional pointwise η-equivalence.
{-@
eta_equivalence_PBEq_pointwise ::
  forall a b. f:(a -> b) -> y:a ->
  {peq (f y) (apply (\x:a -> f x) y)}
@-}
eta_equivalence_PBEq_pointwise :: forall a b. (a -> b) -> a -> PBEq b
eta_equivalence_PBEq_pointwise f y =
  BEq
    (f y)
    ((\x -> f x) y)
    (eta_equivalence_pointwise f y)

-- Lemma. Pointwise η-equivalence.
{-@
eta_equivalence_pointwise ::
  forall a b. f:(a -> b) -> y:a ->
  {f y = apply (\x:a -> f x) y}
@-}
eta_equivalence_pointwise :: forall a b. (a -> b) -> a -> Proof
eta_equivalence_pointwise f y =
  f y
    ==! (\x -> f x) y
    ==! apply (\x -> f x) y
    *** QED

--------------------------------------------------------------------------------
-- α-equivalence
--------------------------------------------------------------------------------

-- -- Theorem. α-equivalence.
-- --
-- --  λx(fx) = λy(fy)
-- --
-- -- Proven by extracting from propositional equality via `toEq`.
-- {-@
-- alpha_equivalence ::
--   forall a b. f:(a -> b) ->
--   {(\x:a -> f x) = (\y:a -> f y)}
-- @-}
-- alpha_equivalence :: forall a b. (a -> b) -> Proof
-- alpha_equivalence f = toEq (\x -> f x) (\y -> f y) (alpha_equivalence_PBEq f)

-- Lemma. Propositional α-equivalence.
{-@
assume alpha_equivalence_PBEq ::
  forall a b. f:(a -> b) ->
  {h:PBEq (a -> b) | peq (\x:a -> f x) (\y:a -> f y)}
@-}
alpha_equivalence_PBEq :: forall a b. (a -> b) -> PBEq (a -> b)
alpha_equivalence_PBEq f =
  XEq
    (\x -> f x)
    (\y -> f y)
    (\x -> BEq ((\x -> f x) x) ((\y -> f y) x) trivial)
