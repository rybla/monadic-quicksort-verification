module QuickSortArray where

import Function
import Liquid.ProofCombinators
import PartitionArray
import QuickSortList
import Relation
import SlowSortList
import VList
import VMonad
import VMonadArray
import VMonadPlus
import VOrdered

-- Function. Write to list then `iqsort`.
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
  m VUnit
iqsort_specification1 (iMonadArray, iMonadPlus, iOrdered) p i =
  vbind_
    (slowsort_ xs)
    (vwriteList_ i)
  where
    vbind_ = vbind iMonad_
    slowsort_ = slowsort (iMonadPlus, iOrdered)
    vwriteList_ = vwriteList iMonadArray
    iMonad_ = VMonadPlus.iMonad iMonadPlus

-- Lemma.
{-@
assume iqsort_specification1_correct ::
  forall m a.
  iMonadArrayPlusOrdered:VMonadArrayPlusOrdered m a ->
  p:a ->
  i:Index ->
  {RefinesPlusMonadic (snd iMonadArrayPlusOrdered)
    (iqsort' iMonadArrayPlusOrdered p i)
    (iqsort_specification1 iMonadArrayPlusOrdered p i)}
@-}
iqsort_specification1_correct ::
  forall m a.
  VMonadArrayPlusOrdered m a ->
  a ->
  Index ->
  Proof
iqsort_specification1_correct (iMonadArray, iMonadPlus, iOrdered) p i = ()

-- Function. Final `iqsort`
iqsort :: forall m a. VMonadArrayPlusOrdered m a -> a -> Index -> m VUnit
iqsort (iMonadArray, iMonadPlus, iOrdered) p Zero = vlift_ vunit
  where
    vlift_ = vlift iMonad_
    iMonad_ = VMonadPlus.iMonad iMonadPlus
iqsort (iMonadArray, iMonadPlus, iOrdered) p (Suc n) =
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
