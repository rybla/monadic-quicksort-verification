module QuickSortArray where

import Function
import Language.Haskell.Liquid.ProofCombinators
import PartitionArray
import QuickSortList
import Relation
import SlowSortList
import VList
import VMonad
import VMonadArray
import VMonadPlus
import VOrdered

-- Function. Write to array, then `iqsort`. This is an abbreviation for use in
-- specifications.
-- (viz. page 13, display 12)
iqsort' :: forall m a. VMonadArrayPlusOrdered m a -> a -> Index -> m VUnit
iqsort' (iMonadArray, iMonadPlus, iOrdered) p i =
  vseq_
    (vwriteList_ i xs)
    (iqsort_ i xs_l)
  where
    xs_l = vlength xs
    veq_ = veq iMonad_
    vwriteList_ = vwriteList iMonadArray
    iqsort_ = iqsort (iMonadArray, iMonadPlus, iOrdered)
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Specification.
iqsort_specification1 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VList a ->
  m VUnit
iqsort_specification1 (iMonadArray, iMonadPlus, iOrdered) p i xs =
  vbind_
    (slowsort_ xs)
    (vwriteList_ i)
  where
    vbind_ = vbind iMonad_
    slowsort_ = slowsort (iMonadPlus, iOrdered)
    vwriteList_ = vwriteList iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- TODO: prove
-- Lemma.
{-@
assume iqsort_specification1_correct ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  p:a ->
  i:Index ->
  xs:VList a ->
  {RefinesPlusMonadic (snd iMonadArrayPlusOrdered)
    (iqsort' iMonadArrayPlusOrdered p i xs)
    (iqsort_specification1 iMonadArrayPlusOrdered p i xs)}
@-}
iqsort_specification1_correct ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VList a ->
  Proof
iqsort_specification1_correct (iMonadArray, iMonadPlus, iOrdered) p i xs = ()

-- Specification. ...
{-@ reflect iqsort_specification2 @-}
iqsort_specification2 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VList a ->
  m VUnit
iqsort_specification2 iMonadArrayPlusOrdered p i xs =
  vbind_
    (partl'_ p (Nil, Nil, xs))
    ( \(ys, zs) ->
        ( vbind_
            (permute_ ys)
            ( \ys' ->
                vseq_
                  (vwriteList_ i (vappend ys' (vappend (vsingleton p) zs)))
                  ( vseq_
                      (iqsort_ i (vlength ys))
                      (iqsort_ (vadd i (Suc (vlength ys))) (vlength zs))
                  )
            )
        )
    )
  where
    partl'_ = partl' (iMonadPlus, iOrdered)
    vbind_ = vbind iMonad_
    slowsort_ = slowsort (iMonadPlus, iOrdered)
    vwriteList_ = vwriteList iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

{-@
iqsort_specification2_correct ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  p:a ->
  i:Index ->
  {iqsort_specification1 iMonadArrayPlusOrdered p i xs ==
   iqsort_specification2 iMonadArrayPlusOrdered p i xs}
@-}
iqsort_specification2_correct ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  m VUnit ->
  Proof
iqsort_specification2_correct iMonadArrayPlusOrdered p i = ()

{-@ reflect refinement13_greater @-}
refinement13_greater ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VList a ->
  m VUnit
refinement13_greater iMonadArrayPlusOrdered p i ys =
  vbind_
    (permute_ ys)
    ( \ys' ->
        (vwriteList_ i (vappend ys' (vsingleton p)))
    )
  where
    vbind_ = vbind iMonad_
    permute_ = permute iMonadPlus
    vwriteList_ = vwriteList iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

{-@ reflect refinement13_lesser @-}
refinement13_lesser ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VList a ->
  m VUnit
refinement13_lesser iMonadArrayPlusOrdered p i ys =
  vseq_
    (vwriteList_ i (vappend (vsingleton p) ys))
    (vswap_ i (vadd i ys_l))
  where
    ys_l = vlength ys
    vseq_ = vseq iMonad_
    vwriteList_ = vwriteList iMonadArray
    vswap_ = vswap iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Lemma.
-- (viz. page 13, display 13)
{-@
assume refinement13 ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadPlusOrdered m a ->
  p:a ->
  i:Index ->
  ys:VList a ->
  {RefinesPlusMonadic (snd3 iMonadArrayPlusOrdered)
    (refinement13_lesser p i ys)
    (refinement13_greater p i ys)}
@-}
refinement13 ::
  forall m a.
  VMonadPlusOrdered m a ->
  a ->
  Index ->
  VList a ->
  Proof
refinement13 (iMonadArray, iMonadPlus, iOrdered) p i ys = ()

{-@ reflect iqsort_specification3 @-}
iqsort_specification3 ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  VList a ->
  m VUnit
iqsort_specification3 (iMonadArray, iMonadPlus, iOrdered) p i xs =
  vseq_
    (vwriteList_ i (Cons p xs))
    ( vbind_
        (ipartl_ p (Suc i) (Zero, Zero, xs_l))
        ( \(ys_l, zs_l) ->
            vseq_
              (vswap_ i (vadd i ys_l))
              ( vseq_
                  (iqsort_ i ys_l)
                  (iqsort_ (vadd i (Suc ys_l)) zs_l)
              )
        )
    )
  where
    vseq_ = vseq iMonad_
    vwriteList_ = vwriteList iMonadArray
    vbind_ = vbind iMonad_
    vread_ = vread iMonadArray
    ipartl_ = ipartl (iMonadArray, iMonadPlus, iOrdered)
    iqsort_ = iqsort (iMonadArray, iMonadPlus, iOrdered)
    iMonad_ = VMonadPlus.iMonad iMonadPlus

{-@
assume iqsort_specification3_correct :: ...
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  p:a ->
  i:Index ->
  xs:VList a ->
  {RefinesPlusMonadic (snd3 iMonadArrayPlusOrdered)
    (iqsort_specification3 iMonadArrayPlusOrdered p i xs)
    (iqsort_specification2 iMonadArrayPlusOrdered p i xs)}
@-}
iqsort_specification3_correct ::
  forall m a.
  iMonadArrayPlusOrdered : VMonadArrayPlusOrdered m a ->
  p : a ->
  i : Index ->
  xs : VList a ->
  Proof
iqsort_specification3_correct iMonadArrayPlusOrdered p i xs = ()

-- Function. Quicksort (in place) array from position `i` to `i + n`.
iqsort :: forall m a. VMonadArrayPlusOrdered m a -> VNat -> m VUnit
iqsort (iMonadArray, iMonadPlus, iOrdered) p Zero = vlift_ vunit
  where
    vlift_ = vlift iMonad_
    iMonad_ = VMonadPlus.iMonad iMonadPlus
iqsort (iMonadArray, iMonadPlus, iOrdered) i (Suc n) =
  vbind_
    (vread_ i)
    ( \p ->
        ( vbind_
            (ipartl_ p (Suc i) (0, 0, n))
            ( \(ys_l, zs_l) ->
                ( vseq_
                    (vswap_ i (vadd i ys_l))
                    ( vseq_
                        (iqsort_ i ys_l)
                        (iqsort_ (vadd i (Suc ys_l)) zs_l)
                    )
                )
            )
        )
    )
  where
    vbind_ = vbind iMonad_
    vseq_ = vseq iMonad_
    vread_ = vread iMonadArray
    ipartl_ = ipartl (iMonadArray, iMonadPlus, iOrdered)
    iqsort_ = iqsort (iMonadArray, iMonadPlus, iOrdered)
    iMonad_ = VMonadPlus.iMonad iMonadPlus
