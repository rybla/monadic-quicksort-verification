module SlowSortList where

import           Liquid.ProofCombinators
import           Function
import           Relation
import           VMonad
import           VMonadPlus
import           VOrdered
import           VList


--------------------------------------------------------------------------------
-- Slow Sort
--------------------------------------------------------------------------------


{-@ lazy slowsort @-} -- TODO: prove termination
{-@ reflect slowsort @-}
slowsort
  :: forall m a . VMonadPlus m -> VOrdered a -> VList a -> m (VList a)
slowsort iMonadPlus iOrdered = kleisli_ permute_
                                        (mguardBy_ isSorted_)
 where
  isSorted_ = isSorted iOrdered
  permute_  = permute iMonadPlus
  mguardBy_ = mguardBy iMonadPlus
  kleisli_  = kleisli iMonad_
  iMonad_   = iMonad iMonadPlus


{-@ lazy permute @-} -- TODO: prove termination
{-@ reflect permute @-}
permute :: forall m a . VMonadPlus m -> VList a -> m (VList a)
permute iMonadPlus Nil = vlift_ Nil
 where
  vlift_  = vlift iMonad_
  iMonad_ = iMonad iMonadPlus
permute iMonadPlus (Cons x xs) = vbind_
  (split_ xs)
  (\(ys, zs) -> vliftF2_ (\ys zs -> vappend ys (vappend xs zs))
                         (permute_ ys)
                         (permute_ zs)
  )
 where
  vbind_   = vbind iMonad_
  split_   = split iMonadPlus
  vliftF2_ = vliftF2 iMonad_
  permute_ = permute iMonadPlus
  iMonad_  = iMonad iMonadPlus


{-@ lazy isSorted @-} -- TODO: prove termination
{-@ reflect isSorted @-}
isSorted :: forall a . VOrdered a -> Predicate (VList a)
isSorted iOrdered Nil         = True
isSorted iOrdered (Cons x xs) = vall (leq_ x) xs && isSorted_ xs
 where
  leq_      = leq iOrdered
  isSorted_ = isSorted iOrdered


{-@ reflect isSortedBetween @-}
isSortedBetween
  :: forall a . VOrdered a -> a -> (VList a, VList a) -> Bool
isSortedBetween iOrdered x (ys, zs) =
  vall (\y -> leq_ y x) ys && vall (\z -> leq_ x z) zs
  where leq_ = leq iOrdered


{-@ lazy split @-} -- TODO: prove termination
{-@ reflect split @-}
split :: forall m a . VMonadPlus m -> VList a -> m (VList a, VList a)
split iMonadPlus Nil = vlift_ (Nil, Nil)
 where
  vlift_  = vlift iMonad_
  iMonad_ = iMonad iMonadPlus
split iMonadPlus (Cons x xs) = vbind_
  (split_ xs)
  (\(ys, zs) ->
    vmadd_ (vlift_ (Cons x ys, zs)) (vlift_ (ys, Cons x zs))
  )
 where
  split_  = split iMonadPlus
  vmadd_  = vmadd iMonadPlus
  vlift_  = vlift iMonad_
  vbind_  = vbind iMonad_
  iMonad_ = iMonad iMonadPlus
