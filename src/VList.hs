module VList where

import           Liquid.ProofCombinators
import           Function
import           Relation
import           VSemigroup
import           VMonoid
import           VMonad
import           VMonadPlus
import           VNat


-- Data. A list is a sequence of elements, constructed as either the empty list
-- or a head element appended to another list.
{-@
data VList a = Nil | Cons {hd::a, tl::VList a}
@-}
data VList a = Nil | Cons a (VList a)


-- -- Measure. `VList a` length.
-- {-@
-- measure mlength :: forall a . VList a -> VNat
-- mlength Nil = Zero
-- mlength (Cons _ xs) = Suc (mlength xs)
-- @-}


-- Measure. Length of `VList a`.
{-@ measure vlength  @-}
vlength :: forall a . VList a -> VNat
vlength Nil         = Zero
vlength (Cons x xs) = Suc (vlength xs)


-- Constructor. Singleton `VList a`.
{-@ reflect vsingleton @-}
vsingleton :: forall a . a -> VList a
vsingleton x = Cons x Nil


-- Function. Append two `VList a`s.
{-@ reflect vappend @-}
vappend :: forall a . VList a -> VList a -> VList a
vappend Nil         ys = ys
vappend (Cons x xs) ys = Cons x (vappend xs ys)


-- Lemma. `vappend` is associative.
{-@
assume vappend_associative :: forall a . xs:VList a -> ys:VList a -> zs:VList a ->
  {IsAssociative vappend xs ys zs}
@-}
vappend_associative
  :: forall a . VList a -> VList a -> VList a -> Proof
vappend_associative xs ys zs = ()


-- Instance. `VList a` forms a semigroup with operator `vappend`.
{-@
iSemigroup_vappend :: forall a . VSemigroup (VList a)
@-}
iSemigroup_vappend :: forall a . VSemigroup (VList a)
iSemigroup_vappend =
  VSemigroup { op = vappend, op_associative = vappend_associative }


-- Lemma. `vappend` has identity `Nil`.
{-@
assume vappend_identity :: forall a . xs:VList a ->
  {IsIdentity vappend Nil xs}
@-}
vappend_identity :: forall a . VList a -> Proof
vappend_identity xs = ()


-- NOTE: doesn't infer that `op iSemigroup_vappend = vappend`
-- -- Instance .`VList a` forms a monoid with operator `vappend` and identity `Nil`.
-- {-@
-- isMonoid_vappend :: forall a . VMonoid (VList a)
-- @-}
-- isMonoid_vappend :: forall a . VMonoid (VList a)
-- isMonoid_vappend = VMonoid { iSemigroup        = iSemigroup_vappend
--                             , epsilon     = Nil
--                             , op_identity = vappend_identity
--                             }


-- Lemma. The length of an appended list is the sum of the lengths of the
-- component lists.
{-@
vappend_sums_vlength :: forall a . xs:VList a -> ys:VList a ->
  {vlength (vappend xs ys) = vadd (vlength xs) (vlength ys)}
@-}
vappend_sums_vlength :: forall a . VList a -> VList a -> Proof
vappend_sums_vlength Nil ys =
  vlength (vappend Nil ys)
    ==. vlength ys
    ==. vadd Zero (vlength ys)
    ?   vadd_identity (vlength ys)
    ==. vadd (vlength Nil) (vlength ys)
    *** QED
vappend_sums_vlength (Cons x xs) ys =
  vlength (vappend (Cons x xs) ys)
    ==. vlength (Cons x (vappend xs ys))
    ==. Suc (vlength (vappend xs ys))
    ==. Suc (vadd (vlength xs) (vlength ys))
    ?   vappend_sums_vlength xs ys
    ==. vadd (Suc (vlength xs))    (vlength ys)
    ==. vadd (vlength (Cons x xs)) (vlength ys)
    *** QED


-- Function. Test if all elements of `VList a` satisfy a predicate.
{-@ reflect vall @-}
vall :: forall a . Predicate a -> VList a -> Bool
vall p Nil         = True
vall p (Cons x xs) = p x && vall p xs


-- Function. Reversed `VList a`.
{-@ reflect vreverse @-}
vreverse :: forall a . VList a -> VList a
vreverse Nil         = Nil
vreverse (Cons x xs) = vappend (vreverse xs) (Cons x Nil)


-- Lemma. `vreverse` preserves `VList a` length.
{-@
vreverse_preserves_vlength :: forall a . xs:VList a ->
  {PreservesMeasure vlength vreverse xs}
@-}
vreverse_preserves_vlength :: forall a . VList a -> Proof
vreverse_preserves_vlength Nil = ()
vreverse_preserves_vlength (Cons x xs) =
  vlength (vreverse (Cons x xs))
    ==. vlength (vappend (vreverse xs) (Cons x Nil))
    ==. vadd (vlength (vreverse xs)) (vlength (Cons x Nil))
    ?   vappend_sums_vlength (vreverse xs) (Cons x Nil)
    ==. vadd (vlength (vreverse xs)) (vlength (Cons x Nil))
    ==. vadd (vlength xs)            (vlength (Cons x Nil))
    ?   vreverse_preserves_vlength xs
    ==. vadd (vlength xs) (Suc Zero)
    ==. Suc (vadd (vlength xs) Zero)
    ?   vadd_m_Sn (vlength xs) Zero
    ==. Suc (vlength xs)
    ?   vadd_identity (vlength xs)
    ==. vlength (Cons x xs)
    *** QED
