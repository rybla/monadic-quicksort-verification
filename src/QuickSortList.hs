module QuickSortList where

import Function
import Language.Haskell.Liquid.Equational
import Relation
import SlowSortList
import VList
import VMonad
import VMonadPlus
import VOrdered
import VTuple
import Prelude hiding ((++), (<=), (>>), (>>=))

--------------------------------------------------------------------------------
-- Divide and Conquer
--------------------------------------------------------------------------------

{-@ reflect slowsort_VCons_expansion_aux1 @-}
slowsort_VCons_expansion_aux1 ::
  VMonadPlusOrdered m ->
  a ->
  VTuple2D (VList a) ->
  m (VList a)
slowsort_VCons_expansion_aux1 (iMonadPlus, iOrdered) p (ys, zs) =
  (guard_ (isSortedBetween_ p ys zs))
    >> ( (permute_ ys >>= guardBy_ isSorted_)
           >>= slowsort_VCons_expansion_aux2_ p zs
       )
  where
    (>>=) = vbind iMonad_
    (>>) = vseq iMonad_
    iMonad_ = iMonad iMonadPlus

    guard_ = guard iMonadPlus
    guardBy_ = guardBy iMonadPlus
    permute_ = permute iMonadPlus

    isSorted_ = isSorted iOrdered
    isSortedBetween_ = isSortedBetween iOrdered

    slowsort_VCons_expansion_aux2_ =
      slowsort_VCons_expansion_aux2
        (iMonadPlus, iOrdered)

{-@ reflect slowsort_VCons_expansion_aux2 @-}
slowsort_VCons_expansion_aux2 ::
  VMonadPlusOrdered m a ->
  a ->
  VList a ->
  VList a ->
  m (VList a)
slowsort_VCons_expansion_aux2 p zs ys' =
  (permute_ zs >>= guardBy_ isSorted_)
    >>= slowsort_VCons_expansion_aux3_ p ys'
  where
    (>>=) = vbind iMonad_
    iMonad_ = iMonad iMonadPlus

    guardBy_ = guardBy iMonadPlus
    permute_ = permute iMonadPlus

    isSorted_ = isSorted iOrdered

    slowsort_VCons_expansion_aux3_ =
      slowsort_VCons_expansion_aux3
        (iMonadPlus, iOrdered)

{-@ reflect slowsort_VCons_expansion_aux3 @-}
slowsort_VCons_expansion_aux3 ::
  VMonadPlusOrdered m a ->
  a ->
  VList a ->
  VList a ->
  m (VList a)
slowsort_VCons_expansion_aux3 (iMonadPlus, iOrdered) p ys' zs' =
  vlift_ (ys' ++ vsingleton p ++ zs')
  where
    vlift_ = vlift iMonad_
    iMonad_ = iMonad iMonadPlus

-- Function. Expanded form of `slowsort` on a `VCons`.
{-@ reflect slowsort_VCons_expansion @-}
slowsort_VCons_expansion ::
  forall m a.
  VMonadPlusOrdered m a ->
  a ->
  VList a ->
  m (VList a)
slowsort_VCons_expansion (iMonadPlus, iOrdered) p xs =
  split_ xs >>= slowsort_VCons_expansion_aux1_ p
  where
    (>>) = vseq iMonad_
    (>>=) = vbind iMonad_
    (>=>) = kleisli iMonad_
    vmapM2_ = vmapM2 iMonad_
    vlift_ = vlift iMonad_
    iMonad_ = iMonad iMonadPlus

    split_ = split iMonadPlus
    permute_ = permute iMonadPlus
    guard_ = guard iMonadPlus
    guardBy_ = guardBy iMonadPlus

    isSorted_ = isSorted iOrdered

    slowsort_ = slowsort (iMonadPlus, iOrdered)
    slowsort_VCons_expansion_ = slowsort_VCons_expansion (iMonadPlus, iOrdered)

-- Lemma.
-- TODO: prove
{-@
assume slowsort_VCons_expansion_correct ::
  forall m a.
  iMonadPlusOrdered:VMonadPlusOrdered m a ->
  p:a ->
  xs:VList a ->
  {slowsort iMonadPlusOrdered (VCons p xs) ==
   slowsort_VCons_expansion iMonadPlusOrdered p xs}
@-}
slowsort_VCons_expansion_correct ::
  forall m a.
  VMonadPlusOrdered m a ->
  a ->
  VList a ->
  Proof
-- TODO: proof in progress
slowsort_VCons_expansion_correct (iMonadPlus, iOrdered) p xs =
  slowsort_ (VCons p xs)
    -- by definition of `slowsort`
    ==. (permute_ >=> (guardBy_ isSorted_)) (VCons p xs)
    -- by definition of `kleisli`
    ==. raw_kleisli vbind_ permute_ (guardBy_ isSorted_) (VCons p xs)
    -- by definition of `raw_kleisli`
    ==. permute_ (VCons p xs) >>= guardBy_ isSorted_
    -- TODO
    ==. _
    *** QED
  where
    vseq_ = vseq iMonad_
    (>>) = vseq_
    vbind_ = vbind iMonad_
    (>>=) = vbind_
    vmapM2_ = vmapM2 iMonad_
    (>=>) = kleisli_
    kleisli_ = kleisli iMonad_
    vlift_ = vlift iMonad_
    iMonad_ = iMonad iMonadPlus

    split_ = split iMonadPlus
    permute_ = permute iMonadPlus
    guard_ = guard iMonadPlus
    guardBy_ = guardBy iMonadPlus

    vleq_ = vleq iOrdered
    isSorted_ = isSorted iOrdered

    slowsort_ = slowsort (iMonadPlus, iOrdered)
    slowsort_VCons_expansion_ = slowsort_VCons_expansion (iMonadPlus, iOrdered)

-- Function. Functional specification of `partition`.
{-@ reflect partition_specification @-}
partition_specification ::
  forall m a.
  VMonadPlusOrdered m a ->
  a ->
  VList a ->
  m (VList a, VList a)
partition_specification (iMonadPlus, iOrdered) x xs =
  vbind_
    (split_ xs)
    (guardBy_ (\(ys, zs) -> isSortedBetween_ x (ys, zs)))
  where
    vbind_ = vbind iMonad_
    iMonad_ = iMonad iMonadPlus
    isSortedBetween_ = isSortedBetween iOrdered
    split_ = split iMonadPlus
    guardBy_ = guardBy iMonadPlus

-- Function. TODO
{-@ reflect partition' @-}
partition' ::
  forall m a.
  VMonadPlusOrdered m a ->
  a ->
  VList a ->
  m (VTuple2D (VList a))
partition' (iMonadPlus, iOrdered) x xs = vlift_ (partition_ x xs)
  where
    vlift_ = vlift iMonad_
    partition_ = partition iOrdered
    iMonad_ = iMonad iMonadPlus

-- Lemma. `partition` refines `partition_step`
-- TODO: prove
-- {-@
-- assume partition_specification_correct :: forall m a. iMonadPlusOrdered:VMonadPlusOrdered m a -> x:a -> xs:VList a ->
--   {RefinesPlusMonadic (fst2 iMonadPlusOrdered) (partition' iMonadPlusOrdered x xs) (partition_specification iMonadPlusOrdered x xs)}
-- @-}
partition_specification_correct ::
  forall m a. VMonadPlusOrdered m a -> a -> VList a -> Proof
partition_specification_correct (iMonadPlus, iOrdered) x xs = ()

-- TODO: proof in progress
-- vaddMP iMonadPlus (partition' iMonadPlusOrdered x xs) (partition_specification iMonadPlusOrdered x xs)
--   ==. vaddMP
--     iMonadPlus
--     (vlift_ (partition_ x xs))
--     (vbind_ (split_ xs) (guardBy_ (isSortedBetween_ x)))
--   ==. partition_specification iMonadPlusOrdered x xs
--   *** QED

-- Function. Helper for "divide and conquer" property.
{-@ reflect quicksort_VCons_specification @-}
quicksort_VCons_specification ::
  forall m a.
  VMonadPlusOrdered m a ->
  a ->
  VList a ->
  m (VList a)
quicksort_VCons_specification (iMonadPlus, iOrdered) x xs =
  vbind_
    (vlift_ (partition_ x xs))
    ( \(ys, zs) ->
        vbind_
          (slowsort_ ys)
          ( \ys' ->
              vbind_
                (slowsort_ zs)
                (\zs' -> vlift_ (vappend ys' (vappend (vsingleton x) zs')))
          )
    )
  where
    slowsort_ = slowsort (iMonadPlus, iOrdered)
    partition_ = partition iOrdered
    vlift_ = vlift iMonad_
    vbind_ = vbind iMonad_
    iMonad_ = iMonad iMonadPlus

-- Lemma. The "divide and conquer" property refines `slowsort`. The proof makes
-- use of `slowsort_VCons_expansion_correct` and
-- `partition_specification_correct`.
-- TODO: prove
-- {-@
-- assume divide_and_conquer :: forall m a .
--   iMonadPlusOrdered:VMonadPlusOrdered m a -> x:a -> xs:VList a ->
--   {RefinesPlusMonadic (fst2 iMonadPlusOrdered) (quicksort_VCons_specification iMonadPlusOrdered x xs) (slowsort iMonadPlusOrdered (VCons x xs))}
-- @-}
divide_and_conquer ::
  forall m a. VMonadPlusOrdered m a -> a -> VList a -> Proof
divide_and_conquer (iMonadPlus, iOrdered) x xs = ()

-- Function. Partition a `VList` into a sublist of elements less than and a
-- sublist of elements greater than a given element.
{-@ reflect partition @-}
partition :: VOrdered a -> a -> VList a -> VTuple2D (VList a)
partition iOrdered x' VNil = (VNil, VNil)
partition iOrdered x' (VCons x xs) =
  let (ys, zs) = partition iOrdered x xs
   in if vleq_ x x' then (VCons x ys, zs) else (ys, VCons x zs)
  where
    vleq_ = vleq iOrdered

--------------------------------------------------------------------------------
-- Quick Sort
--------------------------------------------------------------------------------

{-@ lazy quicksort @-}
{-@ reflect quicksort @-}
quicksort :: forall a. VOrdered a -> VList a -> VList a
quicksort iOrdered VNil = VNil
quicksort iOrdered (VCons x xs) =
  let (ys, zs) = partition_ x xs
   in vappend (quicksort_ ys) (vappend (vsingleton x) (quicksort_ ys))
  where
    partition_ = partition iOrdered
    quicksort_ = quicksort iOrdered