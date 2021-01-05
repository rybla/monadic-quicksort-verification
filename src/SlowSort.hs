module SlowSort where

import           Liquid.ProofCombinators
import           Function
import           Relation
import           IsMonad
import           IsMonadPlus
import           IsOrdered
import           VList


--------------------------------------------------------------------------------
-- Slow Sort
--------------------------------------------------------------------------------


{-@ lazy slowsort @-} -- TODO: prove termination
{-@ reflect slowsort @-}
slowsort
  :: forall m a
   . IsMonadPlus m
  -> IsOrdered a
  -> VList a
  -> m (VList a)
slowsort isMonadPlus iOrd = kleisli_ permute_ (mguardBy_ isSorted_)
 where
  isSorted_ = isSorted iOrd
  permute_  = permute isMonadPlus
  mguardBy_ = mguardBy isMonadPlus
  kleisli_  = kleisli isMonad_
  isMonad_     = isMonad isMonadPlus


{-@ lazy permute @-} -- TODO: prove termination
{-@ reflect permute @-}
permute :: forall m a . IsMonadPlus m -> VList a -> m (VList a)
permute isMonadPlus Nil = vlift_ Nil
 where
  vlift_ = vlift isMonad_
  isMonad_ = isMonad isMonadPlus
permute isMonadPlus (Cons x xs) = vbind_
  (split_ xs)
  (\(ys, zs) -> vliftF2_ (\ys zs -> vappend ys (vappend xs zs))
                        (permute_ ys)
                        (permute_ zs)
  )
 where
  vbind_    = vbind isMonad_
  split_   = split isMonadPlus
  vliftF2_  = vliftF2 isMonad_
  permute_ = permute isMonadPlus
  isMonad_    = isMonad isMonadPlus


{-@ lazy isSorted @-} -- TODO: prove termination
{-@ reflect isSorted @-}
isSorted :: forall a . IsOrdered a -> Predicate (VList a)
isSorted iOrd Nil         = True
isSorted iOrd (Cons x xs) = vall (leq_ x) xs && isSorted_ xs
 where
  leq_      = leq iOrd
  isSorted_ = isSorted iOrd


{-@ reflect isSortedBetween @-}
isSortedBetween
  :: forall a . IsOrdered a -> a -> (VList a, VList a) -> Bool
isSortedBetween iOrd x (ys, zs) =
  vall (\y -> leq_ y x) ys && vall (\z -> leq_ x z) zs
  where leq_ = leq iOrd


{-@ lazy split @-} -- TODO: prove termination
{-@ reflect split @-}
split :: forall m a . IsMonadPlus m -> VList a -> m (VList a, VList a)
split isMonadPlus Nil = vlift_ (Nil, Nil)
 where
  vlift_ = vlift isMonad_
  isMonad_ = isMonad isMonadPlus
split isMonadPlus (Cons x xs) = vbind_
  (split_ xs)
  (\(ys, zs) -> vmadd_ (vlift_ (Cons x ys, zs)) (vlift_ (ys, Cons x zs)))
 where
  split_ = split isMonadPlus
  vmadd_  = vmadd isMonadPlus
  vlift_  = vlift isMonad_
  vbind_  = vbind isMonad_
  isMonad_  = isMonad isMonadPlus
