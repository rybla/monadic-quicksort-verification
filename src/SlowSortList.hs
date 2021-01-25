module SlowSortList where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation
import VList
import VMonad
import VMonadPlus
import VOrdered
import VTuple
import Prelude hiding ((<=), (>>), (>>=))

-- Type. VConstraints for nondeterministically interfacing with arrays of ordered
-- elements.
type VMonadPlusOrdered m a = (VMonadPlus m, VOrdered a)

{-@ reflect slowsort @-}
slowsort :: forall m a. VMonadPlusOrdered m a -> VList a -> m (VList a)
slowsort (iMonadPlus, iOrdered) = permute_ >=> guardBy_ isSorted_
  where
    (>=>) = kleisli iMonad_
    iMonad_ = iMonad iMonadPlus

    permute_ = permute iMonadPlus
    guardBy_ = guardBy iMonadPlus

    isSorted_ = isSorted iOrdered

-- Function. Auxilliary for `permute`.
{-@ reflect permute_aux1 @-}
permute_aux1 :: forall m a. VMonadPlus m -> a -> VTuple2D (VList a) -> m (VList a)
permute_aux1 iMonadPlus x (ys, zs) = vmapM2_ (permute_aux2 x) (permute_ ys) (permute_ zs)
  where
    vmapM2_ = vmapM2 iMonad_
    permute_ = permute iMonadPlus
    iMonad_ = iMonad iMonadPlus

{-@ reflect permute_aux2 @-}
-- Function. Auxilliary for `permute`.
permute_aux2 :: forall a. a -> VList a -> VList a -> VList a
permute_aux2 x ys' zs' = ys' `vappend` vsingleton x `vappend` zs'

-- Function. Nondeterministicall permute a list.
{-@ reflect permute @-}
permute :: forall m a. VMonadPlus m -> VList a -> m (VList a)
permute iMonadPlus VNil = vlift_ VNil
  where
    vlift_ = vlift iMonad_
    iMonad_ = iMonad iMonadPlus
permute iMonadPlus (VCons x xs) = split_ xs >>= permute_aux1_ x
  where
    (>>=) = vbind iMonad_
    split_ = split iMonadPlus
    permute_aux1_ = permute_aux1 iMonadPlus
    iMonad_ = iMonad iMonadPlus

-- TODO: prove
-- Lemma. Lifting the list itself into the plus monad is a plus-monadic
-- refinement of permutations of that list.
{-@
assume identity_refines_permute ::
  forall m a.
  iMonadPlus:VMonadPlus m ->
  xs:VList a ->
  {RefinesPlusMonadic iMonadPlus (vlift (VMonadPlus.iMonad iMonadPlus) xs) (permute iMonadPlus xs)}
@-}
identity_refines_permute :: forall m a. VMonadPlus m -> VList a -> Proof
identity_refines_permute iMonadPlus xs = ()

-- Function. Checks is the list is sorted.
{-@ reflect isSorted @-}
isSorted :: forall a. VOrdered a -> Predicate (VList a)
isSorted iOrdered VNil = True
isSorted iOrdered (VCons x xs) = vall (x <=) xs && isSorted_ xs
  where
    (<=) = vleq iOrdered
    isSorted_ = isSorted iOrdered

-- Function. Checks if an elements can fits in order between two lists.
{-@ reflect isSortedBetween @-}
isSortedBetween ::
  forall a. VOrdered a -> Relation a (VTuple2D (VList a))
isSortedBetween iOrdered x (ys, zs) =
  isSorted_ (vappend ys (vappend (vsingleton x) zs))
  where
    isSorted_ = isSorted iOrdered

{-@ inline isSortedBetween_expansion @-}
isSortedBetween_expansion ::
  forall a. VOrdered a -> a -> VTuple2D (VList a) -> Bool
isSortedBetween_expansion iOrdered x (ys, zs) =
  vall (<= x) ys && vall (x <=) zs
  where
    (<=) = vleq iOrdered

-- TODO: prove
-- Lemma.
-- (viz. page 4, display 5)
{-@
assume isSortedBetween_expansion_correct ::
  forall a.
  iOrdered:VOrdered a ->
  x:a ->
  ys:VList a ->
  zs:VList a ->
  {isSorted iOrdered (vappend ys (vappend (vsingleton x) zs)) ==
   isSortedBetween iOrdered x (ys, zs) }
@-}
isSortedBetween_expansion_correct ::
  forall a.
  VOrdered a ->
  a ->
  VList a ->
  VList a ->
  Proof
isSortedBetween_expansion_correct iOrdered x ys zs = ()

-- Function. Auxilliary for `split`.
{-@ reflect split_aux1 @-}
split_aux1 :: VMonadPlus m -> a -> VTuple2D (VList a) -> m (VTuple2D (VList a))
split_aux1 iMonadPlus x (ys, zs) = vlift_ (VCons x ys, zs) <+> vlift_ (ys, VCons x zs)
  where
    (<+>) = vaddMP iMonadPlus
    vlift_ = vlift iMonad_
    iMonad_ = iMonad iMonadPlus

-- Function. Nondeterministically split a list into two sublists.
{-@ reflect split @-}
split :: forall m a. VMonadPlus m -> VList a -> m (VTuple2D (VList a))
split iMonadPlus VNil = vlift_ (VNil, VNil)
  where
    vlift_ = vlift iMonad_
    iMonad_ = iMonad iMonadPlus
split iMonadPlus (VCons x xs) = split_ xs >>= split_aux1_ x
  where
    split_ = split iMonadPlus
    split_aux1_ = split_aux1 iMonadPlus
    (>>=) = vbind iMonad_
    iMonad_ = iMonad iMonadPlus
