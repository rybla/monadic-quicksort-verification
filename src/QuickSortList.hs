module QuickSortList where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation
import SlowSortList
import VList
import VMonad
import VMonadPlus
import VOrdered
import VTuple

--------------------------------------------------------------------------------
-- Divide and Conquer
--------------------------------------------------------------------------------

-- Function. Expanded form of `slowsort` on a `Cons`.
{-@ reflect slowsort_Cons_expansion @-}
slowsort_Cons_expansion ::
  forall m a.
  VMonadPlusOrdered m a ->
  a ->
  VList a ->
  m (VList a)
slowsort_Cons_expansion (iMonadPlus, iOrdered) p xs =
  vbind_
    (split_ xs)
    ( \(ys, zs) ->
        vseq_
          (guard_ (vall (\x -> vleq_ x p) ys && vall (vleq_ p) zs))
          ( vbind_
              (vbind_ (permute_ ys) (guardBy_ isSorted_))
              ( \ys' ->
                  vbind_
                    (vbind_ (permute_ zs) (guardBy_ isSorted_))
                    ( \zs' ->
                        vlift_ (vappend ys' (vappend (vsingleton p) zs'))
                    )
              )
          )
    )
  where
    vbind_ = vbind iMonad_
    vlift_ = vlift iMonad_
    split_ = split iMonadPlus
    vseq_ = vseq iMonad_
    vleq_ = vleq iOrdered
    permute_ = permute iMonadPlus
    guardBy_ = guardBy iMonadPlus
    guard_ = guard iMonadPlus
    isSorted_ = isSorted iOrdered
    iMonad_ = iMonad iMonadPlus

-- Lemma.
-- TODO: prove
{-@
assume slowsort_Cons_expansion_correct ::
  forall m a.
  iMonadPlusOrdered:VMonadPlusOrdered m a ->
  p:a ->
  xs:VList a ->
  {slowsort iMonadPlusOrdered (Cons p xs) ==
   slowsort_Cons_expansion iMonadPlusOrdered p xs}
@-}
slowsort_Cons_expansion_correct ::
  forall m a.
  VMonadPlusOrdered m a ->
  a ->
  VList a ->
  Proof
slowsort_Cons_expansion_correct (iMonadPlus, iOrdered) p xs = ()

-- TODO: proof in progress
-- slowsort_ (Cons p xs)
--   -- by definition of `slowsort`
--   === kleisli_ permute_ (guardBy_ isSorted_) (Cons p xs)
--   -- by definition of `kleisli`
--   === vbind_ (permute_ (Cons p xs)) (guardBy_ isSorted_)
--   -- by definition of `permute` on a `Cons`
--   === vbind_
--     ( vbind_
--         (split_ xs)
--         ( \(ys, zs) ->
--             vliftF2_
--               ( \ys' zs' ->
--                   vappend
--                     ys'
--                     (vappend (vsingleton p) zs')
--               )
--               (permute_ ys)
--               (permute_ zs)
--         )
--     )
--     (guardBy_ isSorted_)
--   -- by definition of `vliftF2`
--   === vbind_
--     ( vbind_
--         (split_ xs)
--         ( \(ys, zs) ->
--             vbind_
--               (permute_ ys)
--               ( \ys' ->
--                   vbind_
--                     (permute zs)
--                     ( \zs' ->
--                         vlift_ (vappend ys' (vappend (vsingleton p) zs'))
--                     )
--               )
--         )
--     )
--     (guardBy_ isSorted_)
--   -- by monad laws (bring outer `vbind` inside)
--   -- TODO: prove lemma in `VMonad`, I think it would be `vbind_associative` or something
--   === vbind_
--     (split_ xs)
--     ( \(ys, zs) ->
--         vbind_
--           (permute_ ys)
--           ( \ys' ->
--               vbind_
--                 (permute_ zs)
--                 ( \zs' ->
--                     vseq_
--                       (guard_ (isSortedBetween x ys' zs'))
--                       (vlift_ (vappend ys' (vappend (vsingleton p) zs')))
--                 )
--           )
--     )
--   -- by `isSortedBetween_expansion_correct`
--   === vbind_
--     (split_ xs)
--     ( \(ys, zs) ->
--         vbind_
--           (permute_ ys)
--           ( \ys' ->
--               vbind_
--                 (permute_ zs)
--                 ( \zs' ->
--                     vseq_
--                       (guard_ (isSortedBetween_expansion x ys' zs'))
--                       (vlift_ (vappend ys' (vappend (vsingleton p) zs')))
--                 )
--           )
--     )
--   -- by `guard_and_vseq`
--   === vbind_
--     (split_ xs)
--     ( \(ys, zs) ->
--         vseq_
--           (guard_ (vall (\x -> vleq_ x p) ys && vall (vleq_ p) zs))
--           ( vbind_
--               (vbind_ (permute_ ys) (guardBy_ isSorted_))
--               ( \ys' ->
--                   vbind_
--                     (vbind_ (permute_ zs) (guardBy_ isSorted_))
--                     ( \zs' ->
--                         vlift_ (vappend ys' (vappend (vsingleton p) zs'))
--                     )
--               )
--           )
--     )
--   -- by definition of `slowsort_Cons_expansion`
--   === slowsort_Cons_expansion_ p xs
--   *** QED
-- where
--   slowsort_ = slowsort (iMonadPlus, iOrdered)
--   slowsort_Cons_expansion_ = slowsort_Cons_expansion (iMonadPlus, iOrdered)

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
    (guardBy_ (isSortedBetween_ x))
  where
    vbind_ = vbind iMonad_
    iMonad_ = iMonad iMonadPlus
    isSortedBetween_ = isSortedBetween iOrdered
    split_ = split iMonadPlus
    guardBy_ = guardBy iMonadPlus

-- -- Predicate. Refinement specification of `partition`.
-- {-@
-- predicate IsPartition F X XS =
--   RefinesPlusMonadic iMonadPlus (vlift (iMonad iMonadPlus) (f iOrdered x xs)) (partition_specification iOrdered iMonadPlus x xs)
-- @-}

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
{-@
assume partition_specification_correct :: forall m a. iMonadPlusOrdered:VMonadPlusOrdered m a -> x:a -> xs:VList a ->
  {RefinesPlusMonadic (fst iMonadPlusOrdered) (partition' iMonadPlusOrdered x xs) (partition_specification iMonadPlusOrdered x xs)}
@-}
partition_specification_correct ::
  forall m a. VMonadPlusOrdered m a -> a -> VList a -> Proof
partition_specification_correct (iMonadPlus, iOrdered) x xs = ()

-- TODO: proof in progress
-- vmpadd iMonadPlus (partition' iMonadPlusOrdered x xs) (partition_specification iMonadPlusOrdered x xs)
--   === vmpadd
--     iMonadPlus
--     (vlift_ (partition_ x xs))
--     (vbind_ (split_ xs) (guardBy_ (isSortedBetween_ x)))
--   === partition_specification iMonadPlusOrdered x xs
--   *** QED

-- Function. Helper for "divide and conquer" property.
{-@ reflect quicksort_Cons_specification @-}
quicksort_Cons_specification ::
  forall m a.
  VMonadPlusOrdered m a ->
  a ->
  VList a ->
  m (VList a)
quicksort_Cons_specification (iMonadPlus, iOrdered) x xs =
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
-- use of `slowsort_Cons_expansion_correct` and
-- `partition_specification_correct`.
-- TODO: prove
{-@
assume divide_and_conquer :: forall m a .
  iMonadPlusOrdered:VMonadPlusOrdered m a -> x:a -> xs:VList a ->
  {RefinesPlusMonadic (fst iMonadPlusOrdered) (quicksort_Cons_specification iMonadPlusOrdered x xs) (slowsort iMonadPlusOrdered (Cons x xs))}
@-}
divide_and_conquer ::
  forall m a. VMonadPlusOrdered m a -> a -> VList a -> Proof
divide_and_conquer (iMonadPlus, iOrdered) x xs = ()

-- Function. Partition a `VList` into a sublist of elements less than and a
-- sublist of elements greater than a given element.
{-@ reflect partition @-}
partition :: VOrdered a -> a -> VList a -> VTuple2D (VList a)
partition iOrdered x' Nil = (Nil, Nil)
partition iOrdered x' (Cons x xs) =
  let (ys, zs) = partition iOrdered x xs
   in if vleq_ x x' then (Cons x ys, zs) else (ys, Cons x zs)
  where
    vleq_ = vleq iOrdered

--------------------------------------------------------------------------------
-- Quick Sort
--------------------------------------------------------------------------------

quicksort :: forall a. VOrdered a -> VList a -> VList a
quicksort iOrdered Nil = Nil
quicksort iOrdered (Cons x xs) =
  let (ys, zs) = partition_ x xs
   in vappend (quicksort_ ys) (vappend (vsingleton x) (quicksort_ ys))
  where
    partition_ = partition iOrdered
    quicksort_ = quicksort iOrdered