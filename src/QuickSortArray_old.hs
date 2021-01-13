module QuickSortArray where

import Function
import Liquid.ProofCombinators
import QuickSortList
import Relation
import SlowSortList
import VList
import VMonad
import VMonadArray
import VMonadPlus
import VOrdered

--------------------------------------------------------------------------------
-- Quick Sort
--------------------------------------------------------------------------------

-- TODO

--------------------------------------------------------------------------------
-- Partitioning
--------------------------------------------------------------------------------

-- Type. General constraints for nondeterministically sorting arrays.
{-@
type Constraints m a = (VMonadArray m a, VMonadPlus m, VOrdered a)
@-}
type Constraints m a = (VMonadArray m a, VMonadPlus m, VOrdered a)

-- Type.
{-@
type PartitiontrArray m a =
  Constraints m a ->
  a ->
  Index ->
  VTuple2D (VList a) ->
  VList a ->
  m (VNat, VNat)
@-}
type PartitiontrArray m a =
  Constraints m a ->
  a ->
  Index ->
  VTuple2D (VList a) ->
  VList a ->
  m (VNat, VNat)

-- Type.
{-@
type PartitiontrArray_Specification m a =
  Constraints m a ->
  a ->
  VTuple2D (VList a) ->
  VList a ->
  m (VTuple2D (VList a))

@-}
type PartitiontrArray_Specification m a =
  Constraints m a ->
  a ->
  VTuple2D (VList a) ->
  VList a ->
  m (VTuple2D (VList a))

-- -- Function. Partition list (not tail-recursive).
-- {-@ reflect partl @-}
-- partl ::
--   forall a.
--   VOrdered a ->
--   a ->
--   VTuple3D (VList a) ->
--   VTuple2D (VList a)
-- partl iOrdered p (ys, zs, xs) = let (us, vs) = partition_ p xs in (vappend ys us, vappend zs vs)
--   where
--     partition_ = partition iOrdered

-- Function. Tail-recursive partition list.
{-@ reflect partl @-}
partl ::
  forall a.
  VOrdered a ->
  a ->
  VTuple3D (VList a) ->
  VTuple2D (VList a)
partl iOrdered p (ys, zs) Nil = (ys, zs)
partl iOrdered p (ys, zs) (Cons x xs) =
  if leq_ x p
    then partl_ p (vappend ys (vsingleton x), zs) xs
    else partl_ p (ys, vappend zs (vsingleton x)) xs
  where
    partl_ = partl iOrdered
    leq_ = leq iOrdered

-- Function.
{-@ reflect ipartl @-}
ipartl :: forall m a. PartitiontrArray m a
ipartl (iMonadArray, iMonadPlus, iOrdered) p i (ys, zs) xs = undefined

-- Function. First writes `ys ++ zs ++ xs` to the array, then applies `ipartl` using the respective lengths.
-- I.e. vwriteList i (ys ++ zs ++ xs) >> ipartl p i (vlength ys, vlength zs, vlength xs)
{-@ reflect ipartlInContext @-}
ipartlInContext :: forall m a. PartitiontrArray m a
ipartlInContext (iMonadArray, iMonadPlus, iOrdered) p i (ys, zs) xs =
  vseq_
    (vwriteList_ i (vappend ys (vappend zs xs)))
    (ipartl_ p i (vlength ys, vlength zs) (vlength xs))
  where
    vseq_ = vseq iMonad_
    vwriteList_ = vwriteList iMonadArray
    ipartl_ = ipartl (iMonadArray, iMonadPlus, iOrdered)

{-@ reflect ipartlInContext_specification_make @-}
ipartlInContext_specification_make ::
  forall m a.
  PartitiontrArray_Specification m a ->
  PartitiontrArray m a
ipartlInContext_specification_make paritiontrArrayInContext_specification (iMonadArray, iMonadPlus, iOrdered) p i (ys, zs) xs =
  vbind_
    (paritiontrArrayInContext_specification_ p (ys, zs) xs)
    (vwriteListsToLengths2_ i)
  where
    vbind_ = vbind iMonad_
    paritiontrArrayInContext_specification_ = paritiontrArrayInContext_specification (iMonadArray, iMonadPlus, iOrdered)
    vwriteListsToLengths2_ = vwriteListsToLengths2 iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Predicate. That the final `ipartl` (in context) is refined by candidate `F` (in context). I.e.
--   `vwriteList i (ys ++ zs ++ xs) >> ipartl p i (vlength ys, vlength zs) (vlength xs)`
--     plus-monadically refines
--   `ipartl_specification p i (ys, zs) xs >>= vwriteListsToLengths2 i`
{-@
predicate IsPartitiontrArrayGeneralization F IMONADARRAY IMONADPLUS IORDERED P I XS YS ZS =
  RefinesPlusMonadic
    (ipartlInContext (IMONADARRAY, IMONADPLUS, IORDERED) P I (YS, ZS) XS)
    (ipartlInContext_specification_make F (IMONADARRAY, IMONADPLUS, IORDERED) P I (YS, ZS) XS)
@-}

-- Function. Functional specification of `ipartl`.
{-@ reflect ipartl_specification1 @-}
ipartl_specification1 :: forall m a. PartitiontrArray_Specification m a
ipartl_specification1 iMonadArray iOrdered p (ys, zs) xs =
  vlift_apply_second_ permute (partl_ p (ys, zs) xs)
  where
    vlift_apply_second_ = VMonadArray.iMonad iMonadArray
    partl_ = partl iOrdered

-- Lemma.
{-@
assume isPartitiontrArray_specification1 ::
  forall m a.
  Constraints m a ->
  p:a ->
  i:Index ->
  xs:(VList a) ->
  ys:(VList a) ->
  zs:(VList a) ->
  {IsPartitiontrArrayGeneralization ipartl_specification1 iMonadArray iMonadPlus iOrdered p xs ys zs}
@-}
isPartitiontrArray_specification1 ::
  forall m a.
  Constraints m a ->
  a ->
  Index ->
  VList a ->
  VList a ->
  VList a ->
  Proof
isPartitiontrArray_specification1 (iMonadArray, iMonadPlus, iOrdered) p i xs ys zs = ()

-- Function.
{-@ reflect ipartl_helper @-}
ipartl_helper ::
  forall m a.
  Constraints m a ->
  a ->
  VTuple2D (VList a) ->
  VList a ->
  m (VTuple2D (VList a))
ipartl_helper (iMonadArray, iMonadPlus, iOrdered) p (ys, zs) Nil = vlift_ (ys, zs)
  where
    vlift_ = vlift iMonad_
    iMonad_ = VMonadPlus.iMonad iMonadPlus
ipartl_helper (iMonadArray, iMonadPlus, iOrdered) p (ys, zs) (Cons xs) =
  if leq_ x p
    then vbind_ (permute_ zs) (\zs' -> ipartl_helper_ p (vappend ys (vsingleton x), zs') xs)
    else vbind_ (permute_ (vappend zs (vsingleton xs))) (\zs' -> ipartl_helper_ p (ys, zs') xs)
  where
    vbind_ = vbind iMonad_
    permute_ = permute iMonadPlus
    ipartl_helper_ = ipartl_helper (iMonadArray, iMonadPlus, iOrdered)
    leq_ = leq iOrdered
    iMonad_ = VMonadPlus.iMonad iMonadPlus

{-@ reflect ipartl_specification2 @-}
ipartl_specification2 :: forall m a. PartitiontrArray_Specification m a
ipartl_specification2 p i (ys, zs) xs = ipartl_helper_ p (ys, zs) xs
  where
    ipartl_helper_ = ipartl_helper (iMonadArray, iMonadPlus, iOrdered)

-- Lemma.
{-@
assume isPartitiontrArray_specification2 ::
  forall m a.
  Constraints m a ->
  p:a ->
  i:Index ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {IsPartitiontrArrayGeneralization ipartl_specification2 iMonadArray iMonadPlus iOrdered p i xs ys zs}
@-}
isPartitiontrArray_specification2 ::
  forall m a.
  Constraints m a ->
  a ->
  Index ->
  VList a ->
  VList a ->
  VList a ->
  Proof
isPartitiontrArray_specification2 (iMonadArray, iMonadPlus, iOrdered) p i xs ys zs = ()

-- Function. Slightly clarified version of `ipartl_helper`.
{-@ reflect ipartl_helper' @-}
ipartl_helper' ::
  forall m a.
  Constraints m a ->
  a ->
  VTuple3D (VList a) ->
  m (VTuple2D (VList a))
ipartl_helper' (iMonadArray, iMonadPlus, iOrdered) p (ys, zs, Nil) = vlift_ (ys, zs)
ipartl_helper' (iMonadArray, iMonadPlus, iOrdered) p (ys, zs, Cons x xs) =
  vbind_ (dispatch x p (ys, zs, xs)) (ipartl_helper'_ p)
  where
    dispatch x p (ys, zs, xs) =
      if leq_ x p
        then vbind_ (permute_ zs) (\zs' -> vlift_ (vappend ys (vsingleton x), zs', xs))
        else vbind_ (permute (vappend zs (vsingleton x))) (\zs' -> vlift_ (ys, zs', xs))
    vbind_ = vbind iMonad_
    vlift_ = vlift iMonad_
    ipartl_helper'_ = ipartl_helper' (iMonadArray, iMonadPlus, iOrdered)
    leq_ = leq iOrdered
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- -- Lemma.
-- {-@
-- ipartl_helper2

-- @-}