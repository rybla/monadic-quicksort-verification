module PartitionArray where

import Function
import Language.Haskell.Liquid.ProofCombinators
import QuickSortList
import Relation
import SlowSortList
import VList
import VMonad
import VMonadArray
import VMonadPlus
import VNat
import VOrdered
import VTuple
import VUnit

-- TODO: What's the theorem here? Is it just that this implementation finally
-- shows `ipartl_specification1_correct` sound?

-- Type. Constraints for nondeterministically sorting arrays.
type VMonadArrayPlusOrdered m a = (VMonadArray m a, VMonadPlus m, VOrdered a)

-- Function. Partition list `xs` onto two other lists `ys` and `zs` (not
-- tail-recursively) using `partition`.
{-@ reflect partl_ntr @-}
partl_ntr ::
  forall a.
  VOrdered a ->
  a ->
  VTuple3D (VList a) ->
  VTuple2D (VList a)
partl_ntr iOrdered p (ys, zs, xs) =
  let (us, vs) = partition_ p xs
   in (vappend ys us, vappend zs vs)
  where
    partition_ = partition iOrdered

-- Function. Partition list `xs` onto two other lists `ys` and `zs`
-- (tail-recursively).
{-@ reflect partl @-}
partl ::
  forall a.
  VOrdered a ->
  a ->
  VTuple3D (VList a) ->
  VTuple2D (VList a)
partl iOrdered p (ys, zs, Nil) = (ys, zs)
partl iOrdered p (ys, zs, Cons x xs) =
  if vleq_ x p
    then partl_ p (vappend ys (vsingleton x), zs, xs)
    else partl_ p (ys, vappend zs (vsingleton x), xs)
  where
    partl_ = partl iOrdered
    vleq_ = vleq iOrdered

-- Lemma.
-- TODO: prove
{-@
assume partl_correct ::
  forall a.
  iOrdered:VOrdered a ->
  p:a ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {partl iOrdered p (ys, zs, xs) =
   partl iOrdered p (ys, zs, xs)}
@-}
partl_correct ::
  forall a.
  VOrdered a ->
  a ->
  VList a ->
  VList a ->
  VList a ->
  Proof
partl_correct iOrdered p xs ys zs = ()

-- Lemma.
-- TODO: prove
{-@
assume partl_generalizes_partition ::
  forall a.
  iOrdered:VOrdered a ->
  p:a ->
  xs:VList a ->
  {partl iOrdered p (Nil, Nil, xs) = partition iOrdered p xs}
@-}
partl_generalizes_partition ::
  forall a.
  VOrdered a ->
  a ->
  VList a ->
  Proof
partl_generalizes_partition iOrdered p xs = ()

-- Function. Write components to array, then `ipartl` with respective lengths.
{-@ reflect ipartl' @-}
ipartl' ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VTuple3D (VList a) ->
  m (VTuple2D VNat)
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
{-@ reflect ipartl_specification1 @-}
ipartl_specification1 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VTuple3D (VList a) ->
  m (VTuple2D VNat)
ipartl_specification1 (iMonadArray, iMonadPlus, iOrdered) p i (ys, zs, xs) =
  vbind_
    (vlift_apply_second_ permute_ (partl_ p (ys, zs, xs)))
    (vwriteListsToLengths2_ i)
  where
    vbind_ = vbind iMonad_
    vlift_apply_second_ = vlift_apply_second iMonad_
    permute_ = permute iMonadPlus
    partl_ = partl iOrdered
    vwriteListsToLengths2_ = vwriteListsToLengths2 iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Lemma.
-- TODO: prove `ipartl` specification #1 is correct.
{-@
assume ipartl_specification1_correct ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  p:a ->
  i:Index ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {RefinesPlusMonadic (snd3 iMonadArrayPlusOrdered)
    (ipartl' iMonadArrayPlusOrdered p i (ys, zs, xs))
    (ipartl_specification1 iMonadArrayPlusOrdered p i (ys, zs, xs))}
@-}
ipartl_specification1_correct ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VList a ->
  VList a ->
  VList a ->
  Proof
ipartl_specification1_correct iMonadArrayPlusOrdered p i xs ys zs = ()

-- TODO: how to handle this?
-- -- NOTE: This implementation is not actually used. The actually used
-- -- implementation is presented next.
-- -- Function. Combining `vlift_apply_second` into `partl`.
-- -- (viz page 10, Derivation)
-- partl' ::
--   forall m a.
--   (VMonadPlus m, VOrdered a) ->
--   a ->
--   VTuple3D (VList a) ->
--   m (VTuple2D (VList a))
-- partl' (iMonadPlus, iOrdered) p (ys, zs, Nil) = vlift_ (ys, zs)
--   where
--     vlift_ = vlift iMonad_
--     iMonad_ = VMonadPlus.iMonad iMonadPlus
-- partl' (iMonadPlus, iOrdered) p (ys, zs, Cons x xs) =
--   if vleq_ x p
--     then
--       vbind_
--         (permute_ zs)
--         (\zs' -> partl'_ p (vappend ys (vsingleton x), zs', xs))
--     else
--       vbind_
--         (permute (vappend zs (vsingleton x)))
--         (\zs' -> partl'_ p (ys, zs', xs))
--   where
--     vleq_ = vleq iOrdered
--     vbind_ = vbind iMonad_
--     permute_ = permute iMonadPlus
--     partl'_ = partl' (iMonadPlus, iOrdered)
--     iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Function. Combining `vlift_apply_second` into `partl`. First version is
-- presented as above, but below version is the implementation used onward
-- (page 11, bottom).
{-@ reflect partl' @-}
partl' ::
  forall m a.
  VMonadPlusOrdered m a ->
  a ->
  VTuple3D (VList a) ->
  m (VTuple2D (VList a))
partl' (iMonadPlus, iOrdered) p (ys, zs, Nil) = vlift_ (ys, zs)
  where
    vlift_ = vlift iMonad_
    iMonad_ = VMonadPlus.iMonad iMonadPlus
partl' (iMonadPlus, iOrdered) p (ys, zs, Cons x xs) =
  vbind_
    (dispatch x p (ys, zs, xs))
    (partl'_ p)
  where
    dispatch x p (ys, zs, xs) =
      if vleq_ x p
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
    partl'_ = partl' (iMonadPlus, iOrdered)
    permute_ = permute iMonadPlus
    vleq_ = vleq iOrdered
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Specification. `ipartl'` specification #2.
-- (viz. page 10, display 10).
{-@ reflect ipartl_specification2 @-}
ipartl_specification2 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VTuple3D (VList a) ->
  m (VTuple2D VNat)
ipartl_specification2 (iMonadArray, iMonadPlus, iOrdered) p i (ys, zs, xs) =
  vbind_
    (partl'_ p (ys, zs, xs))
    (vwriteListsToLengths2_ i)
  where
    vbind_ = vbind iMonad_
    partl'_ = partl' (iMonadPlus, iOrdered)
    vwriteListsToLengths2_ = vwriteListsToLengths2 iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Lemma.
-- TODO: prove
-- (viz. page 10, display 10).
{-@
assume ipartl_specification2_correct ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a->
  p:a ->
  i:Index ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {RefinesPlusMonadic (snd3 iMonadArrayPlusOrdered)
    (ipartl' iMonadArrayPlusOrdered p i (ys, zs, xs))
    (ipartl_specification2 iMonadArrayPlusOrdered p i (ys, zs, xs))}
@-}
ipartl_specification2_correct ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VList a ->
  VList a ->
  VList a ->
  Proof
ipartl_specification2_correct (iMonadArray, iMonadPlus, iOrdered) p i xs ys zs =
  ()

-- Specification. For the `then` branch in `ipartl_Cons_specification3`.
-- (viz. page 11, )
{-@ reflect ipartl_Cons_then_specification3 @-}
ipartl_Cons_then_specification3 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  (VList a, VList a, a, VList a) ->
  m (VTuple2D VNat)
ipartl_Cons_then_specification3
  (iMonadArray, iMonadPlus, iOrdered)
  p
  i
  (ys, zs, x, xs) =
    vbind_
      (permute_ zs)
      ( \zs' ->
          vseq_
            (vwriteList_ i (vappend ys (vappend (vsingleton x) zs')))
            (ipartl_ p i (Suc ys_l, vlength zs', xs_l))
      )
    where
      (xs_l, ys_l) = (vlength xs, vlength ys)
      vbind_ = vbind iMonad_
      vseq_ = vseq iMonad_
      vwriteList_ = vwriteList iMonadArray
      permute_ = permute iMonadPlus
      ipartl_ = ipartl (iMonadArray, iMonadPlus, iOrdered)
      iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Specification. For the `else` branch in `ipartl_Cons_specification3`.
{-@ reflect ipartl_Cons_else_specification3 @-}
ipartl_Cons_else_specification3 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  (VList a, VList a, a, VList a) ->
  m (VTuple2D VNat)
ipartl_Cons_else_specification3
  (iMonadArray, iMonadPlus, iOrdered)
  p
  i
  (ys, zs, x, xs) =
    vbind_
      (permute_ (vappend zs (vsingleton x)))
      ( \zs' ->
          vseq_
            (vlift_ (ys, zs', xs))
            (ipartl_ p i (ys_l, vlength zs', xs_l))
      )
    where
      (xs_l, ys_l) = (vlength xs, vlength ys)
      vlift_ = vlift iMonad_
      vbind_ = vbind iMonad_
      vseq_ = vseq iMonad_
      permute_ = permute iMonadPlus
      ipartl_ = ipartl (iMonadArray, iMonadPlus, iOrdered)
      iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Specification. For `ipartl'` applied to a `xs = Cons ...`.
{-@ reflect ipartl_Cons_specification3 @-}
ipartl_Cons_specification3 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  (VList a, VList a, a, VList a) ->
  m (VTuple2D VNat)
ipartl_Cons_specification3
  (iMonadArray, iMonadPlus, iOrdered)
  p
  i
  (ys, zs, x, xs) =
    vseq_
      (vwriteList_ (vadd i (vadd ys_l (vadd zs_l vone))) xs)
      ( if vleq_ x p
          then ipartl_Cons_then_specification3_
          else ipartl_Cons_else_specification3_
      )
    where
      (xs_l, ys_l, zs_l) = (vlength xs, vlength ys, vlength zs)
      ipartl_Cons_then_specification3_ =
        ipartl_Cons_then_specification3
          (iMonadArray, iMonadPlus, iOrdered)
          p
          i
          (ys, zs, x, xs)
      ipartl_Cons_else_specification3_ =
        ipartl_Cons_else_specification3
          (iMonadArray, iMonadPlus, iOrdered)
          p
          i
          (ys, zs, x, xs)
      vseq_ = vseq iMonad_
      vwriteList_ = vwriteList iMonadArray
      vleq_ = vleq iOrdered
      iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Lemma.
-- TODO: prove
{-@
assume ipartl_Cons_specification3_correct ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  p:a ->
  i:Index ->
  x:a ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {RefinesPlusMonadic (snd3 iMonadArrayPlusOrdered)
    (ipartl_Cons_specification3 iMonadArrayPlusOrdered p i (ys, zs, x, xs))
    (ipartl_specification2 iMonadArrayPlusOrdered p i (ys, zs, Cons x xs))}
@-}
ipartl_Cons_specification3_correct ::
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  a ->
  VList a ->
  VList a ->
  VList a ->
  Proof
ipartl_Cons_specification3_correct iMonadArrayPlusOrdered p i x xs ys zs = ()

-- Specification. For the `then` branch in `iparlt'` applied to a
-- `xs = Cons ...`.
-- (viz. page 11, bottom refinement).
{-@ reflect ipartl_Cons_then_specification4 @-}
ipartl_Cons_then_specification4 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  (VList a, VList a, a, VList a) ->
  m (VTuple2D VNat)
ipartl_Cons_then_specification4
  (iMonadArray, iMonadPlus, iOrdered)
  p
  i
  (ys, zs, x, xs) =
    vseq_
      (vwriteList_ i (vappend ys (vappend zs (vsingleton x))))
      ( vseq_
          (vswap_ (vadd i ys_l) (vadd i (vadd ys_l zs_l)))
          (ipartl_ p i (Suc ys_l, zs_l, xs_l))
      )
    where
      (ys_l, zs_l, xs_l) = (vlength ys, vlength zs, vlength xs)
      vswap_ = vswap iMonadArray
      vseq_ = vseq iMonad_
      vwriteList_ = vwriteList iMonadArray
      ipartl_ = ipartl (iMonadArray, iMonadPlus, iOrdered)
      iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Lemma.
-- TODO: prove
-- Uses lemma from page 12, display 11.
-- (viz. page 11, bottom refinement).
{-@
assume ipartl_Cons_then_specification4_correct ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  p:a ->
  i:Index ->
  x:a ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {RefinesPlusMonadic (snd3 iMonadArrayPlusOrdered)
    (ipartl_Cons_then_specification4 iMonadArrayPlusOrdered p i (ys, zs, x, xs))
    (ipartl_Cons_then_specification3 iMonadArrayPlusOrdered p i (ys, zs, x, xs))}
@-}
ipartl_Cons_then_specification4_correct ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  a ->
  VList a ->
  VList a ->
  VList a ->
  Proof
ipartl_Cons_then_specification4_correct iMonadArrayPlusOrdered p i x xs ys zs =
  ()

-- Specification. For the `else` branch in `ipartl'` applied to a
-- `xs = Cons ...`. Note that `vlift vunit` refines `permute`.
-- (viz. page 11, middle refinement).
{-@ reflect ipartl_Cons_else_specification4 @-}
ipartl_Cons_else_specification4 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  (VList a, VList a, a, VList a) ->
  m (VTuple2D VNat)
ipartl_Cons_else_specification4
  (iMonadArray, iMonadPlus, iOrdered)
  p
  i
  (ys, zs, x, xs) =
    vseq_
      (vwriteList_ i (vappend ys (vappend zs (vsingleton x))))
      (ipartl_ p i (ys_l, Suc zs_l, xs_l))
    where
      (ys_l, zs_l, xs_l) = (vlength ys, vlength zs, vlength xs)
      vseq_ = vseq iMonad_
      ipartl_ = ipartl (iMonadArray, iMonadPlus, iOrdered)
      vwriteList_ = vwriteList iMonadArray
      iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Lemma.
-- TODO: prove
-- Uses lemma from page 12, display 11.
-- (viz. page 11, middle refinement).
{-@
assume ipartl_Cons_else_specification4_correct ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  p:a ->
  i:Index ->
  x:a ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {RefinesPlusMonadic (snd3 iMonadArrayPlusOrdered)
    (ipartl_Cons_else_specification4 iMonadArrayPlusOrdered p i (ys, zs, x, xs))
    (ipartl_Cons_else_specification3 iMonadArrayPlusOrdered p i (ys, zs, x, xs))
  }
@-}
ipartl_Cons_else_specification4_correct ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  a ->
  VList a ->
  VList a ->
  VList a ->
  Proof
ipartl_Cons_else_specification4_correct
  (iMonadArray, iMonadPlus, iOrdered)
  p
  i
  x
  xs
  ys
  zs =
    ()

{-@ reflect refinement11_greater @-}
refinement11_greater ::
  VMonadArrayPlusOrdered m a ->
  VNat ->
  a ->
  VList a ->
  m VUnit
refinement11_greater (iMonadArray, iMonadPlus, iOrdered) i x zs =
  vbind_
    (permute_ zs)
    (\zs' -> vwriteList_ i (vappend (vsingleton x) zs'))
  where
    vbind_ = vbind iMonad_
    permute_ = permute iMonadPlus
    vwriteList_ = vwriteList iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

{-@ reflect refinement11_lesser @-}
refinement11_lesser ::
  VMonadArrayPlusOrdered m a ->
  VNat ->
  a ->
  VList a ->
  m VUnit
refinement11_lesser (iMonadArray, iMonadPlus, iOrdered) i x zs =
  vseq_
    (vwriteList_ i (vappend zs (vsingleton x)))
    (vswap_ i (vadd i zs_l))
  where
    zs_l = vlength zs
    vseq_ = vseq iMonad_
    vwriteList_ = vwriteList iMonadArray
    vswap_ = vswap iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Lemma.
-- TODO: prove
{-@
assume refinement11 ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  i:VNat ->
  x:a ->
  zs:VList a ->
  {RefinesPlusMonadic (snd3 iMonadArrayPlusOrdered)
    (refinement11_lesser iMonadArrayPlusOrdered i x zs)
    (refinement11_greater iMonadArrayPlusOrdered i x zs)}
@-}
refinement11 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  VNat ->
  a ->
  VList a ->
  Proof
refinement11 (iMonadArray, iMonadPlus, iOrdered) i x zs = ()

-- Specification. For `ipartl'` applied to a `xs = Cons ...`.
-- (viz page 12, middle display)
{-@ reflect ipartl_Cons_specification4 @-}
ipartl_Cons_specification4 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  (VList a, VList a, a, VList a) ->
  m (VTuple2D VNat)
ipartl_Cons_specification4
  (iMonadArray, iMonadPlus, iOrdered)
  p
  i
  (ys, zs, x, xs) =
    vseq_
      (vwriteList_ (vadd i (vadd ys_l (Suc zs_l))) xs)
      ( if vleq_ x p
          then ipartl_Cons_then_specification4_
          else ipartl_Cons_else_specification4_
      )
    where
      (ys_l, zs_l, xs_l) = (vlength ys, vlength zs, vlength xs)
      vseq_ = vseq iMonad_
      vleq_ = vleq iOrdered
      vwriteList_ = vwriteList iMonadArray
      ipartl_Cons_then_specification4_ =
        ipartl_Cons_then_specification4
          (iMonadArray, iMonadPlus, iOrdered)
          p
          i
          (ys, zs, x, xs)
      ipartl_Cons_else_specification4_ =
        ipartl_Cons_else_specification4
          (iMonadArray, iMonadPlus, iOrdered)
          p
          i
          (ys, zs, x, xs)
      iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Specification. For `ipartl'` applied to a `xs = Cons ...`.
-- (viz. page 12, middle refinements, bottom).
{-@ reflect ipartl_Cons_specification5 @-}
ipartl_Cons_specification5 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  (VList a, VList a, a, VList a) ->
  m (VTuple2D VNat)
ipartl_Cons_specification5
  (iMonadArray, iMonadPlus, iOrdered)
  p
  i
  (ys, zs, x, xs) =
    vseq_
      (vwriteList_ i (vappend ys (vappend zs (Cons x xs))))
      ( vbind_
          (vread_ (vadd i (vadd ys_l zs_l)))
          ( \x' ->
              if vleq_ x' p
                then
                  vseq_
                    (vswap_ (vadd i ys_l) (vadd i (vadd ys_l zs_l)))
                    (ipartl_ p i (Suc ys_l, zs_l, xs_l))
                else (ipartl_ p i (ys_l, vadd zs_l vone, xs_l))
          )
      )
    where
      (ys_l, zs_l, xs_l) = (vlength ys, vlength zs, vlength xs)
      vseq_ = vseq iMonad_
      vbind_ = vbind iMonad_
      vleq_ = vleq iOrdered
      vread_ = vread iMonadArray
      vwriteList_ = vwriteList iMonadArray
      vswap_ = vswap iMonadArray
      ipartl_ = ipartl (iMonadArray, iMonadPlus, iOrdered)
      iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Lemma.
-- TODO: prove
-- NOTE: If I use a single `=` and indent the refinement type to look nice, I
-- get an error with that says `ipartl_Cons_specification5` is an undefined
-- symbol; I guess it thinks that I'm trying to do an assignment if I indent
-- after an `=`?
-- (viz. page 12, middle refinements).
{-@
assume ipartl_Cons_specification5_correct ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  p:a ->
  i:Index ->
  x:a ->
  xs:VList a ->
  ys:VList a ->
  zs:VList a ->
  {ipartl_Cons_specification5 iMonadArrayPlusOrdered p i (ys, zs, x, xs) ==
   ipartl_Cons_specification4 iMonadArrayPlusOrdered p i (ys, zs, x, xs)}
@-}
ipartl_Cons_specification5_correct ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  a ->
  VList a ->
  VList a ->
  VList a ->
  Proof
ipartl_Cons_specification5_correct iMonadArrayPlusOrdered p i x xs ys zs = ()

-- Function. Final deriviation of `ipartl`.
{-@ reflect ipartl @-}
ipartl ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VTuple3D VNat ->
  m (VTuple2D VNat)
ipartl (iMonadArray, iMonadPlus, iOrdered) p i (ys_l, zs_l, Zero) =
  vlift_ (ys_l, zs_l)
  where
    vlift_ = vlift iMonad_
    iMonad_ = VMonadPlus.iMonad iMonadPlus
ipartl (iMonadArray, iMonadPlus, iOrdered) p i (ys_l, zs_l, Suc xs_l) =
  vbind_
    (vread_ (vadd i (vadd ys_l zs_l)))
    ( \x ->
        if vleq_ x p
          then
            vseq_
              (vswap_ (vadd i ys_l) (vadd i (vadd ys_l zs_l)))
              (ipartl_ p i (Suc ys_l, zs_l, xs_l))
          else ipartl_ p i (ys_l, Suc zs_l, xs_l)
    )
  where
    vbind_ = vbind iMonad_
    vread_ = vread iMonadArray
    vleq_ = vleq iOrdered
    vseq_ = vseq iMonad_
    vswap_ = vswap iMonadArray
    ipartl_ = ipartl (iMonadArray, iMonadPlus, iOrdered)
    iMonad_ = VMonadPlus.iMonad iMonadPlus