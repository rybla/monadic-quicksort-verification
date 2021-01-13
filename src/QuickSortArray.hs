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
type VMonadPlusOrdered m a = (VMonadPlus m, VOrdered a)
@-}
type VMonadPlusOrdered m a = (VMonadPlus m, VOrdered a)

{-@
type VMonadArrayPlusOrdered m a = (VMonadArray m a, VMonadPlus m, VOrdered a)
@-}
type VMonadArrayPlusOrdered m a = (VMonadArray m a, VMonadPlus m, VOrdered a)

-- Type.
{-@
type PartitiontrArray m a =
  (VMonadArray m a, VMonadPlus m, VOrdered a) ->
  a ->
  Index ->
  VTuple2D (VList a) ->
  VList a ->
  m (VNat, VNat)
@-}
type PartitiontrArray m a =
  (VMonadArray m a, VMonadPlus m, VOrdered a) ->
  a ->
  Index ->
  VTuple2D (VList a) ->
  VList a ->
  m (VNat, VNat)

-- Type.
{-@
type PartitiontrArray_Specification m a =
  (VMonadArray m a, VMonadPlus m, VOrdered a) ->
  a ->
  VTuple2D (VList a) ->
  VList a ->
  m (VTuple2D (VList a))

@-}
type PartitiontrArray_Specification m a =
  (VMonadArray m a, VMonadPlus m, VOrdered a) ->
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
partl iOrdered p (ys, zs, Nil) = (ys, zs)
partl iOrdered p (ys, zs, Cons x xs) =
  if leq_ x p
    then partl_ p (vappend ys (vsingleton x), zs) xs
    else partl_ p (ys, vappend zs (vsingleton x)) xs
  where
    partl_ = partl iOrdered
    leq_ = leq iOrdered

-- Function.
{-@ reflect ipartl @-}
ipartl :: forall m a. (VMonadArray m a, VMonadPlus m, VOrdered a) -> a -> Index -> VTuple3D VNat -> m (VTuple2D VNat)
ipartl (iMonadArray, iMonadPlus, iOrdered) p i (ys_l, zs_l, xs_l) = undefined

-- Function. Write components to array, then `ipartl` with respective lengths.
{-@ reflect ipartl' @-}
ipartl' :: forall m a. (VMonadArray m a, VMonadPlus m, VOrdered a) -> a -> Index -> VTuple3D (VList a) -> m (VTuple2D VNat)
ipartl' (iMonadArray, iMonadPlus, iOrdered) p i (ys, zs, xs) =
  vseq_
    (vwriteList_ i (vappend ys (vappend zs xs)))
    (ipartl_ p i (vlength ys, vlength zs, vlength xs))
  where
    vseq_ = vseq iMonad_
    vwriteList_ = vwriteList iMonadArray
    ipartl_ = ipartl (iMonadArray, iMonadPlus, iOrdered)
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Specification. `ipartl'` specification #1 (page 10).
{-@ reflect ipartl'_specification1 @-}
ipartl'_specification1 :: forall m a. (VMonadArray m a, VMonadPlus m, VOrdered a) -> a -> Index -> VTuple3D (VList a) -> m (VTuple2D VNat)
ipartl'_specification1 (iMonadArray, iMonadPlus, iOrdered) p i (ys, zs, xs) =
  vbind_
    (vlift_apply_second_ permute_ (partl_ p (ys, zs, xs)))
    (vwriteListsToLengths2_ i)
  where
    vbind_ = vbind iMonad_
    vlift_apply_second_ = vlift_apply_second_ iMonad_
    permute_ = permute iMonadPlus
    partl_ = partl (iMonadArray, iMonadPlus, iOrdered)
    vwriteListsToLengths2_ = vwriteListsToLengths2 iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Lemma. `ipartl` specification #1 is correct.
{-@
assume ipartl'_specification1_correct ::
  forall m a.
  iMonadArrayPlusOrdered:(VMonadArray m a, VMonadPlus m, VOrdered a) ->
  p:a ->
  i:Index ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {RefinesPlusMonadic (snd2D iMonadArrayPlusOrdered)
    (ipartl' iMonadArrayPlusOrdered p i (ys, zs, xs))
    (ipartl'_specification1 iMonadArrayPlusOrdered p i (ys, zs, xs))}
@-}
ipartl'_specification1_correct :: forall m a. (VMonadArray m a, VMonadPlus m, VOrdered a) -> a -> Index -> VList a -> VList a -> VList a -> Proof
ipartl'_specification1_correct iMonadArrayPlusOrdered p i xs ys zs = ()

-- Function. Combining `vlift_apply_second` into `partl` (page 10, Derivation).
{-@ reflect partl' @-}
partl' :: forall m a. (VMonadPlus m, VOrdered a) -> a -> VTuple3D (VList a) -> m (VTuple2D (VList a))
partl' (iMonadPlus, iOrdered) p (ys, zs, Nil) = vlift_ (ys, zs)
  where
    vlift_ = vlift iMonad_
    iMonad_ = VMonadPlus.iMonad iMonadPlus
partl' (iMonadPlus, iOrdered) p (ys, zs, Cons x xs) =
  if leq_ x p
    then
      vbind_
        (permute_ zs)
        (\zs' -> partl'_ p (vappend ys (vsingleton x), zs', xs))
    else
      vbind_
        (permute (vappend zs (vsingleton x)))
        (\zs' -> partl'_ p (ys, zs', xs))
  where
    leq_ = leq iOrdered
    vbind_ = vbind iMonad_
    permute_ = permute iMonadPlus
    partl'_ = partl' (iMonadPlus, iOrdered)
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Specification. `ipartl'` specification #2 (page 10, display 10).
{-@ reflect ipartl'_specification2 @-}
ipartl'_specification2 :: forall m a. (VMonadArray m a, VMonadPlus m, VOrdered a) -> a -> Index -> VTuple3D (VList a) -> m (VTuple2D VNat)
ipartl'_specification2 (iMonadArray, iMonadPlus, iOrdered) p i (ys, zs, xs) =
  vbind_
    (partl'_ p (ys, zs, xs))
    (vwriteListsToLengths2_ i)
  where
    vbind_ = vbind iMonad_
    partl'_ = partl' (iMonadPlus, iOrdered)
    vwriteListsToLengths2_ = vwriteListsToLengths2 iMonadArray

-- Lemma.
{-@
ipartl'_specification2_correct ::
  forall m a.
  iMonadArrayPlusOrdered:(VMonadArray m a, VMonadPlus m, VOrdered a) ->
  p:a ->
  i:Index ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {RefinesPlusMonadic (snd2D iMonadArrayPlusOrdered)
    (ipartl' iMonadArrayPlusOrdered p i (ys, zs, xs))
    (ipartl'_specification2 iMonadArrayPlusOrdered p i (ys, zs, xs))}
@-}

-- Function. Combining `vlift_apply_second` into `partl` (derivation, page 10).
{-@ reflect partl'' @-}
partl'' :: forall m a. VMonadPlusOrdered m a -> a -> VTuple3D (VList a) -> m (VTuple2D (VList a))
partl'' (iMonadPlus, iOrdered) p (ys, zs, Nil) = vlift_ (ys, zs)
  where
    vlift_ = vlift iMonad_
    iMonad_ = VMonadPlus.iMonad iMonadPlus
partl'' (iMonadPlus, iOrdered) p (ys, zs, Cons x xs) = vbind_ (dispatch x p (ys, zs, xs)) (partl'_ p)
  where
    dispatch x p (ys, zs, xs) =
      if x leq_ p
        then
          vbind_
            (permute_ zs)
            (\zs' -> vlift_ (vappend ys (vsingleton x), zs', xs))
        else
          vbind_
            (permute_ (vappend zs (vsingleton x)))
            (\zs' -> vlift_ (ys, zs', xs))
    vlift_ = vlift iMonad_
    vbind_ = vbind iMonad_
    partl'_ = partl (iMonadPlus, iOrdered)
    permute_ = permute iOrdered
    iMonad_ = VMonadPlus.iMonad iMonadPlus

ipartl'' :: forall m a. VMonadArrayPlusOrdered m a -> a -> Index -> VTuple3D (VList a) -> VTuple2D VNat
ipartl'' (iMonadArray, iMonadPlus, iOrdered) p i (ys, zs, xs) =
  vseq_
    (vwriteList_ (vadd i (vadd ys_l (vadd zs_l vone))) xs)
    ( if x leq_ p
        then
          vseq_
            ( vbind_
                (permute_ zs)
                (\zs' -> vlift_ (vappend ys (vsingleton x), zs', xs))
            )
            (ipartl_ p i (vadd ys_l vone, vlength zs', xs_l))
        else
          vseq_
            ( vbind_
                (permute_ (vappend zs (vsingleton x)))
                (\zs' -> vlift_ (ys, zs', xs))
            )
            (ipartl_ p i (ys_l, vlength zs', xs_l))
    )
  where
    (ys_l, zs_l) = (vlength ys, vlength zs)
    vseq_ = vseq iMonad_
    vlift_ = vlift iMonad_
    vbind_ = vbind iMonad_
    leq_ = leq iOrdered
    permute_ = permute iMonadPlus
    ipartl_ = ipartl_ (iMonadArray, iMonadPlus, iOrdered)
    iMonad_ = VMonadPlus.iMonad iMonadPlus

ipartl''_specification :: forall m a. VMonadArrayPlusOrdered m a -> a -> Index -> (VList a, VList a, a, VList a) -> m (VTuple2D VNat)

partl''_specification (iMonadArray, iMonadPlus, iOrdered) p i (ys, zs, x, xs) =
  vbind_ (partl'_ p (ys, zs, Cons x xs)) (vwriteListsToLengths2_ i)
  where
    vbind_ = vbind iMonad_
    partl'_ = partl' (iMonadPlus, iOrdered)
    vwriteListsToLengths2_ = vwriteListsToLengths2 iMonadArray
    iMonad_ = iMonad VMonadPlus.iMonad iMonadPlus

-- Lemma. Refinement at top of page 11.
{-@
assume ipartl''_specification_correct ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  p:a ->
  i:Index ->
  x:a ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {RefinesPlusMonadic (snd2D iMonadArrayPlusOrdered)
    (ipartl'' iMonadArrayPlusOrdered p i (ys, zs, xs))
    (ipartl''_specification iMonadArrayPlusOrdered p i (ys, zs, x, xs))}
@-}
ipartl''_specification_correct :: forall m a. VMonadArrayPlusOrdered m a -> a -> Index -> a -> VList a -> VList a -> VList a -> Proof
ipartl''_specification_correct = ()