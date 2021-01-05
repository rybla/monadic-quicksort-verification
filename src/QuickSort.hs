module QuickSort where

import           Liquid.ProofCombinators
import           Function
import           Relation
import           VMonad
import           VMonadPlus
import           VOrdered
import           VList

import           SlowSort


--------------------------------------------------------------------------------
-- Quick Sort
--------------------------------------------------------------------------------


quicksort :: forall a . VOrdered a -> VList a -> VList a
quicksort iOrdered Nil = Nil
quicksort iOrdered (Cons x xs) =
  let (ys, zs) = partition_ x xs
  in  vappend (quicksort_ ys) (vappend (vsingleton x) (quicksort_ ys))
 where
  partition_ = partition iOrdered
  quicksort_ = quicksort iOrdered


--------------------------------------------------------------------------------
-- Partitioning
--------------------------------------------------------------------------------


-- Function. Functional specification of `partition`.
{-@ reflect partition_specification @-}
partition_specification
  :: forall m a
   . VMonadPlus m
  -> VOrdered a
  -> a
  -> VList a
  -> m (VList a, VList a)
partition_specification iMonadPlus iOrdered x xs = vbind_
  (split_ xs)
  (mguardBy_ (isSortedBetween_ x))
 where
  vbind_           = vbind iMonad_
  iMonad_          = iMonad iMonadPlus
  isSortedBetween_ = isSortedBetween iOrdered
  split_           = split iMonadPlus
  mguardBy_        = mguardBy iMonadPlus


-- Predicate. Refinement specification of `partition`.
{-@ predicate IsPartition F X XS = MRefines iMonadPlus (vlift (iMonad iMonadPlus) (f iOrdered x xs)) (partition_specification iOrdered iMonadPlus x xs) @-}


-- Function. Partition a `VList` into a sublist of elements less than and a
-- sublist of elements greater than a given element.
{-@ reflect partition @-}
partition :: VOrdered a -> a -> VList a -> (VList a, VList a)
partition iOrdered x' Nil = (Nil, Nil)
partition iOrdered x' (Cons x xs) =
  let (ys, zs) = partition iOrdered x xs
  in  if leq_ x x' then (Cons x ys, zs) else (ys, Cons x zs)
  where leq_ = leq iOrdered


-- Lemma. `partition` refines `partition_step`
-- TODO. prove
{-@
assume partition_correct :: forall m a . iMonadPlus:VMonadPlus m -> iOrdered:VOrdered a -> x:a -> xs:VList a ->
  {MRefines iMonadPlus (vlift (iMonad iMonadPlus) (partition iOrdered x xs)) (partition_specification iMonadPlus iOrdered x xs)}
@-}
partition_correct
  :: forall m a . VMonadPlus m -> VOrdered a -> a -> VList a -> Proof
partition_correct iMonadPlus iOrdered x xs = ()


-- Lemma. "Divide and conquer" property
{-@ reflect slowsort_step @-}
slowsort_step
  :: forall m a
   . VMonadPlus m
  -> VOrdered a
  -> a
  -> VList a
  -> m (VList a)
slowsort_step iMonadPlus iOrdered x xs = vbind_
  (vlift_ (partition_ x xs))
  (\(ys, zs) -> vbind_
    (slowsort_ ys)
    (\ys' -> vbind_
      (slowsort_ zs)
      (\zs' -> vlift_ (vappend ys' (vappend (vsingleton x) zs')))
    )
  )
 where
  slowsort_  = slowsort iMonadPlus iOrdered
  partition_ = partition iOrdered
  vlift_     = vlift iMonad_
  vbind_     = vbind iMonad_
  iMonad_    = iMonad iMonadPlus


-- Lemma. The "divide and conquer" property: `slowsort_step` refines `slowsort`.
-- TODO. prove
{-@
assume divide_and_conquer :: forall m a . iMonadPlus:VMonadPlus m -> iOrdered:VOrdered a -> x:a -> xs:VList a ->
  {MRefines iMonadPlus (slowsort_step iMonadPlus iOrdered x xs) (slowsort iMonadPlus iOrdered (Cons x xs))}
@-}
divide_and_conquer
  :: forall m a . VMonadPlus m -> VOrdered a -> a -> VList a -> Proof
divide_and_conquer iMonadPlus iOrdered x xs = ()
