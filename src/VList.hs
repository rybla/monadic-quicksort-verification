module VList where

import Language.Haskell.Liquid.ProofCombinators
import Relation
import VNat
import VSemigroup

-- Data. A list is a sequence of elements, constructed as either the empty list
-- or a head element appended to another list.
-- data VList a = VNil | VCons a (VList a)
data VList a = VNil | VCons {vhead :: a, vtail :: VList a}

-- -- Measure. `VList a` length.
-- {-@
-- measure mlength :: forall a . VList a -> VNat
-- mlength VNil = Zero
-- mlength (VCons _ xs) = Suc (mlength xs)
-- @-}

-- Measure. Length of `VList a`.
{-@ measure vlength  @-}
vlength :: forall a. VList a -> VNat
vlength VNil = Zero
vlength (VCons _ xs) = Suc (vlength xs)

-- VConstructor. Singleton `VList a`.
{-@ reflect vsingleton @-}
vsingleton :: forall a. a -> VList a
vsingleton x = VCons x VNil

-- Function. Append two `VList a`s.
{-@ reflect vappend @-}
vappend :: forall a. VList a -> VList a -> VList a
vappend VNil ys = ys
vappend (VCons x xs) ys = VCons x (vappend xs ys)

-- Lemma. `vappend` is associative.
{-@
assume vappend_associative :: forall a . xs:VList a -> ys:VList a -> zs:VList a ->
  {IsAssociative vappend xs ys zs}
@-}
vappend_associative ::
  forall a. VList a -> VList a -> VList a -> Proof
vappend_associative _ _ _ = ()

-- Instance. `VList a` forms a semigroup with operator `vappend`.
{-@
iSemigroup_vappend :: forall a . VSemigroup (VList a)
@-}
iSemigroup_vappend :: forall a. VSemigroup (VList a)
iSemigroup_vappend =
  VSemigroup {op = vappend, op_associative = vappend_associative}

-- TODO: prove
-- Lemma. `vappend` has identity `VNil`.
{-@
assume vappend_identity :: forall a . xs:VList a ->
  {IsIdentity vappend VNil xs}
@-}
vappend_identity :: forall a. VList a -> Proof
vappend_identity _ = ()

-- NOTE: doesn't infer that `op iSemigroup_vappend = vappend`
-- -- Instance .`VList a` forms a monoid with operator `vappend` and identity `VNil`.
-- {-@
-- isMonoid_vappend :: forall a . VMonoid (VList a)
-- @-}
-- isMonoid_vappend :: forall a . VMonoid (VList a)
-- isMonoid_vappend = VMonoid { iSemigroup        = iSemigroup_vappend
--                             , epsilon     = VNil
--                             , op_identity = vappend_identity
--                             }

-- Lemma. The length of an appended list is the sum of the lengths of the
-- component lists.
{-@
vappend_sums_vlength :: forall a . xs:VList a -> ys:VList a ->
  {vlength (vappend xs ys) = vadd (vlength xs) (vlength ys)}
@-}
vappend_sums_vlength :: forall a. VList a -> VList a -> Proof
vappend_sums_vlength VNil ys =
  vlength (vappend VNil ys)
    === vlength ys
    === (vadd Zero (vlength ys) ? vadd_identity (vlength ys))
    === vadd (vlength VNil) (vlength ys)
    *** QED
vappend_sums_vlength (VCons x xs) ys =
  vlength (vappend (VCons x xs) ys)
    === vlength (VCons x (vappend xs ys))
    === Suc (vlength (vappend xs ys))
    === (Suc (vadd (vlength xs) (vlength ys)) ? vappend_sums_vlength xs ys)
    === vadd (Suc (vlength xs)) (vlength ys)
    === vadd (vlength (VCons x xs)) (vlength ys)
    *** QED

-- Function. Test if all elements of `VList a` satisfy a predicate.
{-@ reflect vall @-}
vall :: forall a. Predicate a -> VList a -> Bool
vall _ VNil = True
vall p (VCons x xs) = p x && vall p xs

-- Function. Reversed `VList a`.
{-@ reflect vreverse @-}
vreverse :: forall a. VList a -> VList a
vreverse VNil = VNil
vreverse (VCons x xs) = vappend (vreverse xs) (VCons x VNil)

-- Lemma. `vreverse` preserves `VList a` length.
{-@
vreverse_preserves_vlength :: forall a . xs:VList a ->
  {PreservesMeasure vlength vreverse xs}
@-}
vreverse_preserves_vlength :: forall a. VList a -> Proof
vreverse_preserves_vlength VNil =
  vlength (vreverse VNil)
    === vlength VNil
    *** QED
vreverse_preserves_vlength (VCons x xs) =
  vlength (vreverse (VCons x xs))
    === vlength (vappend (vreverse xs) (VCons x VNil))
    === ( vadd (vlength (vreverse xs)) (vlength (VCons x VNil))
            ? vappend_sums_vlength (vreverse xs) (VCons x VNil)
        )
    === vadd (vlength (vreverse xs)) (vlength (VCons x VNil))
    === ( vadd (vlength xs) (vlength (VCons x VNil))
            ? vreverse_preserves_vlength xs
        )
    === vadd (vlength xs) (Suc Zero)
    === (Suc (vadd (vlength xs) Zero) ? vadd_Suc_right (vlength xs) Zero)
    === (Suc (vlength xs) ? vadd_identity (vlength xs))
    === vlength (VCons x xs)
    *** QED
