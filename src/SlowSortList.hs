module SlowSortList where

import Function
import Liquid.ProofCombinators
import Relation
import VList
import VMonad
import VMonadPlus
import VOrdered

-- Type. Constraints for nondeterministically interfacing with arrays of ordered
-- elements.
type VMonadPlusOrdered m a = (VMonadPlus m, VOrdered a)

-- TODO: prove termination
{-@ lazy slowsort @-}
{-@ reflect slowsort @-}
slowsort ::
  forall m a. VMonadPlusOrdered m a -> VList a -> m (VList a)
slowsort (iMonadPlus, iOrdered) =
  kleisli_
    permute_
    (mguardBy_ isSorted_)
  where
    isSorted_ = isSorted iOrdered
    permute_ = permute iMonadPlus
    mguardBy_ = mguardBy iMonadPlus
    kleisli_ = kleisli iMonad_
    iMonad_ = iMonad iMonadPlus

-- TODO: prove termination
{-@ lazy permute @-}
{-@ reflect permute @-}
permute :: forall m a. VMonadPlus m -> VList a -> m (VList a)
permute iMonadPlus Nil = vlift_ Nil
  where
    vlift_ = vlift iMonad_
    iMonad_ = iMonad iMonadPlus
permute iMonadPlus (Cons x xs) =
  vbind_
    (split_ xs)
    ( \(ys, zs) ->
        vliftF2_
          (\ys zs -> vappend ys (vappend xs zs))
          (permute_ ys)
          (permute_ zs)
    )
  where
    vbind_ = vbind iMonad_
    split_ = split iMonadPlus
    vliftF2_ = vliftF2 iMonad_
    permute_ = permute iMonadPlus
    iMonad_ = iMonad iMonadPlus

-- TODO: prove
-- Lemma. Lifting the list itself into the plus monad is a plus-monadic
-- refinement of permutations of that list.
{-@
assume identity_refines_permute ::
  forall m a.
  iMonadPlus:VMonadPlus m ->
  xs:VList a ->
  {RefinesPlusMonadic iMonadPlus (vlift (iMonad iMonadPlus) xs) (permute iMonadPlus xs)}
@-}
identity_refines_permute :: forall m a. VMonadPlus m -> VList a -> Proof
identity_refines_permute iMonadPlus xs = ()

-- TODO: prove termination
{-@ lazy isSorted @-}
{-@ reflect isSorted @-}
isSorted :: forall a. VOrdered a -> Predicate (VList a)
isSorted iOrdered Nil = True
isSorted iOrdered (Cons x xs) = vall (leq_ x) xs && isSorted_ xs
  where
    leq_ = leq iOrdered
    isSorted_ = isSorted iOrdered

{-@ reflect isSortedBetween @-}
isSortedBetween ::
  forall a. VOrdered a -> a -> (VList a, VList a) -> Bool
isSortedBetween iOrdered x (ys, zs) =
  vall (\y -> leq_ y x) ys && vall (\z -> leq_ x z) zs
  where
    leq_ = leq iOrdered

-- TODO: prove termination
{-@ lazy split @-}
{-@ reflect split @-}
split :: forall m a. VMonadPlus m -> VList a -> m (VList a, VList a)
split iMonadPlus Nil = vlift_ (Nil, Nil)
  where
    vlift_ = vlift iMonad_
    iMonad_ = iMonad iMonadPlus
split iMonadPlus (Cons x xs) =
  vbind_
    (split_ xs)
    ( \(ys, zs) ->
        vmpadd_ (vlift_ (Cons x ys, zs)) (vlift_ (ys, Cons x zs))
    )
  where
    split_ = split iMonadPlus
    vmpadd_ = vmpadd iMonadPlus
    vlift_ = vlift iMonad_
    vbind_ = vbind iMonad_
    iMonad_ = iMonad iMonadPlus
