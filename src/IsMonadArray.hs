module IsMonadArray where

import           Liquid.ProofCombinators
import           Function
import           Relation
import           IsMonad
import           VUnit
import           VBool
import           VNat
import           VTuple
import           VList


-- Type. Index for monadic array.
{-@ type Index = VNat @-}
type Index = VNat


-- Data. Monadic Array
{-@
data IsMonadArray m a = IsMonadArray
  { isMonad :: IsMonad m
  , vread :: Index -> m a
  , vwrite :: Index -> a -> m ()
  , vread_vwrite :: i:Index ->
      {vbind isMonad (vread i) (vwrite i) = vlift isMonad vunit}
  , vwrite_vread :: i:Index -> x:a ->
    {vseq isMonad (vwrite i x) (vread i) = vseq isMonad (vwrite i x) (vlift isMonad x)}
  , vwrite_vwrite :: i:Index -> x:a -> x':a ->
      {vseq isMonad (vwrite i x) (vwrite i x') = vwrite i x'}
  , vread_vread :: i:Index -> f:(a -> a -> a) ->
      {vliftF2 isMonad f (vread i) (vread i) = vliftF isMonad (vdiagonalize f) (vread i)}
  , vread_commutative :: i:Index -> j:Index ->
      {IsCommutative (vseq isMonad) (vread i) (vread j)}
  , vwrite_commutative :: i:Index -> j:Index -> {i_neq_j : Proof | i /= j} -> x:a -> y:a ->
      {IsCommutative (vseq isMonad) (vwrite i x) (vwrite j y)}
  , vread_vwrite_commutative :: i:Index -> j:Index -> {i_neq_j : Proof | i /= j} -> x:a ->
      {IsCommutative (vseq isMonad) (vseq isMonad (vread i) (vlift isMonad vunit)) (vwrite j x)}
  }
@-}
data IsMonadArray m a = IsMonadArray
  { isMonad :: IsMonad m
  , vread  :: Index -> m a
  , vwrite :: Index -> a -> m ()
  , vread_vwrite :: Index -> Proof
  , vwrite_vread :: Index -> a -> Proof
  , vwrite_vwrite :: Index -> a -> a -> Proof
  , vread_vread :: Index -> (a -> a -> a) -> Proof
  , vread_commutative :: Index -> Index -> Proof -> Proof
  , vwrite_commutative :: Index -> Index -> Proof -> a -> a -> Proof
  , vread_vwrite_commutative :: Index -> Index -> Proof -> a -> Proof
  }


{-@ reflect vreadList @-}
vreadList :: IsMonadArray m a -> VNat -> VNat -> m (VList a)
vreadList isMonadArray i Zero = vlift_ Nil
 where
  vlift_   = vlift isMonad_
  isMonad_ = isMonad isMonadArray
vreadList isMonadArray i (Suc n) = vliftF2_ Cons
                                            (vread_ i)
                                            (vreadList_ (Suc i) n)
 where
  vread_     = vread isMonadArray
  vreadList_ = vreadList isMonadArray
  vliftF2_   = vliftF2 isMonad_
  isMonad_   = isMonad isMonadArray


{-@ reflect vwriteList @-}
vwriteList :: IsMonadArray m a -> VNat -> VList a -> m ()
vwriteList isMonadArray i Nil = vlift_ ()
 where
  vlift_   = vlift isMonad_
  isMonad_ = isMonad isMonadArray
vwriteList isMonadArray i (Cons x xs) = vseq_
  (vwrite_ i x)
  (vwriteList_ (Suc i) xs)
 where
  vseq_       = vseq isMonad_
  vwrite_     = vwrite isMonadArray
  vwriteList_ = vwriteList isMonadArray
  isMonad_    = isMonad isMonadArray


{-@ reflect vwriteListToLength @-}
vwriteListToLength :: IsMonadArray m a -> VNat -> VList a -> m VNat
vwriteListToLength isMonadArray i xs = vseq_ (vwriteList_ i xs)
                                             (vlift_ (vlength xs))
 where
  vwriteList_ = vwriteList isMonadArray
  vseq_       = vseq isMonad_
  vlift_      = vlift isMonad_
  isMonad_    = isMonad isMonadArray


{-@ reflect vwriteList2ToLength @-}
vwriteList2ToLength
  :: IsMonadArray m a
  -> VNat
  -> VTuple2D (VList a)
  -> m (VTuple2D VNat)
vwriteList2ToLength isMonadArray i (xs, ys) = vseq_
  (vwriteList_ i (vappend xs ys))
  (vlift_ (vlength xs, vlength ys))
 where
  vseq_       = vseq isMonad_
  vlift_      = vlift isMonad_
  vwriteList_ = vwriteList isMonadArray
  isMonad_    = isMonad isMonadArray


{-@ reflect vwriteList3ToLength @-}
vwriteList3ToLength
  :: IsMonadArray m a
  -> VNat
  -> VTuple3D (VList a)
  -> m (VTuple3D VNat)
vwriteList3ToLength isMonadArray i (xs, ys, zs) = vseq_
  (vwriteList_ i (vappend xs (vappend ys zs)))
  (vlift_ (vlength xs, vlength ys, vlength zs))
 where
  vseq_       = vseq isMonad_
  vlift_      = vlift isMonad_
  vwriteList_ = vwriteList isMonadArray
  isMonad_    = isMonad isMonadArray


{-@
vwriteList_vappend :: forall m a . isMonadArray:IsMonadArray m a -> i:Index -> xs:VList a -> ys:VList a ->
  {vwriteList isMonadArray i (vappend xs ys) = vseq isMonad (vwriteList isMonadArray i xs) (vwriteList isMonadArray (vadd i (vlength xs)) ys)}
@-}
vwriteList_vappend
  :: forall m a
   . IsMonadArray m a
  -> Index
  -> VList a
  -> VList a
  -> Proof
vwriteList_vappend isMonadArray i Nil ys =
  vwriteList_ i (vappend Nil ys)
    ==. vwriteList_ i ys
    ==. vseq_ (vlift_ vunit) (vwriteList_ i ys)
    ?   vseq_identity_ (vwriteList_ i ys)
    ==. vseq_ (vlift_ vunit) (vwriteList_ (VNat.vadd i Zero) ys)
    ?   vadd_identity i
    ==. vseq_ (vwriteList_ i Nil)
              (vwriteList_ (vadd i (vlength Nil)) ys)
    *** QED
 where
  vseq_          = vseq isMonad_
  vlift_         = vlift isMonad_
  vseq_identity_ = vseq_identity isMonad_
  vwriteList_    = vwriteList isMonadArray
  isMonad_       = isMonad isMonadArray
vwriteList_vappend isMonad i (Cons x xs) ys = ()
