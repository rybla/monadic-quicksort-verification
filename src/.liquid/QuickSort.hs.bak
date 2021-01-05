module QuickSort where

import           Liquid.ProofCombinators
import           Function
import           Relation
import           IsMonad
import           IsMonadPlus
import           IsOrdered
import           VList

import           SlowSort


--------------------------------------------------------------------------------
-- Quick Sort
--------------------------------------------------------------------------------


quicksort :: forall a . IsOrdered a -> VList a -> VList a
quicksort iOrd Nil = Nil
quicksort iOrd (Cons x xs) =
  let (ys, zs) = partition_ x xs
  in  vappend (quicksort_ ys) (vappend (vsingleton x) (quicksort_ ys))
 where
  partition_ = partition iOrd
  quicksort_ = quicksort iOrd


--------------------------------------------------------------------------------
-- Partitioning
--------------------------------------------------------------------------------


-- Function. Functional specification of `partition`.
{-@ reflect partition_specification @-}
partition_specification
  :: forall m a
   . IsMonadPlus m
  -> IsOrdered a
  -> a
  -> VList a
  -> m (VList a, VList a)
partition_specification isMonadPlus iOrd x xs = vbind_
  (split_ xs)
  (mguardBy_ (isSortedBetween_ x))
 where
  vbind_            = vbind isMonad_
  isMonad_            = isMonad isMonadPlus
  isSortedBetween_ = isSortedBetween iOrd
  split_           = split isMonadPlus
  mguardBy_        = mguardBy isMonadPlus


-- Predicate. Refinement specification of `partition`.
{-@ predicate IsPartition F X XS = MRefines isMonadPlus (vlift (isMonad isMonadPlus) (f iOrd x xs)) (partition_specification iOrd isMonadPlus x xs) @-}


-- Function. Partition a `VList` into a sublist of elements less than and a
-- sublist of elements greater than a given element.
{-@ reflect partition @-}
partition :: IsOrdered a -> a -> VList a -> (VList a, VList a)
partition iOrd x' Nil = (Nil, Nil)
partition iOrd x' (Cons x xs) =
  let (ys, zs) = partition iOrd x xs
  in  if leq_ x x' then (Cons x ys, zs) else (ys, Cons x zs)
  where leq_ = leq iOrd


-- Lemma. `partition` refines `partition_step`
-- TODO: prove
{-@
assume partition_correct :: forall m a . isMonadPlus:IsMonadPlus m -> iOrd:IsOrdered a -> x:a -> xs:VList a ->
  {MRefines isMonadPlus (vlift (isMonad isMonadPlus) (partition iOrd x xs)) (partition_specification isMonadPlus iOrd x xs)}
@-}
partition_correct
  :: forall m a
   . IsMonadPlus m
  -> IsOrdered a
  -> a
  -> VList a
  -> Proof
partition_correct isMonadPlus iOrd x xs = ()


-- Lemma. "Divide and conquer" property
{-@ reflect slowsort_step @-}
slowsort_step
  :: forall m a
   . IsMonadPlus m
  -> IsOrdered a
  -> a
  -> VList a
  -> m (VList a)
slowsort_step isMonadPlus iOrd x xs = vbind_
  (vlift_ (partition_ x xs))
  (\(ys, zs) -> vbind_
    (slowsort_ ys)
    (\ys' -> vbind_
      (slowsort_ zs)
      (\zs' -> vlift_ (vappend ys' (vappend (vsingleton x) zs')))
    )
  )
 where
  slowsort_  = slowsort isMonadPlus iOrd
  partition_ = partition iOrd
  vlift_      = vlift isMonad_
  vbind_      = vbind isMonad_
  isMonad_      = isMonad isMonadPlus


-- Lemma. The "divide and conquer" property: `slowsort_step` refines `slowsort`.
{-@
assume divide_and_conquer :: forall m a . isMonadPlus:IsMonadPlus m -> iOrd:IsOrdered a -> x:a -> xs:VList a ->
  {MRefines isMonadPlus (slowsort_step isMonadPlus iOrd x xs) (slowsort isMonadPlus iOrd (Cons x xs))}
@-}
divide_and_conquer
  :: forall m a
   . IsMonadPlus m
  -> IsOrdered a
  -> a
  -> VList a
  -> Proof
divide_and_conquer isMonadPlus iOrd x xs = ()
