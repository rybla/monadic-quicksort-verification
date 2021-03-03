module VMonadArray where

import Function
import Language.Haskell.Liquid.ProofCombinators
import VList
import VMonad
import VNat
import VTuple
import VUnit

-- Type. Index for monadic array.
{-@ type Index = VNat @-}
type Index = VNat

-- Data Class. A monadic array is TODO.
{-@
data VMonadArray m a = VMonadArray
  { iMonad :: VMonad m
  , vread :: Index -> m a
  , vwrite :: Index -> a -> m VUnit
  , vread_vwrite :: i:Index ->
      {bind iMonad (vread i) (vwrite i) = lift iMonad vunit}
  , vwrite_vread :: i:Index -> x:a ->
    {vseq iMonad (vwrite i x) (vread i) = vseq iMonad (vwrite i x) (lift iMonad x)}
  , vwrite_vwrite :: i:Index -> x:a -> x':a ->
      {vseq iMonad (vwrite i x) (vwrite i x') = vwrite i x'}
  , vread_vread :: i:Index -> f:(a -> a -> a) ->
      {vmapM2 iMonad f (vread i) (vread i) = vmapM iMonad (vdiagonalize f) (vread i)}
  , vread_commutative :: i:Index -> j:Index ->
      {IsCommutative (vseq iMonad) (vread i) (vread j)}
  , vwrite_commutative :: i:Index -> j:Index -> {i_neq_j : Proof | i /= j} -> x:a -> y:a ->
      {IsCommutative (vseq iMonad) (vwrite i x) (vwrite j y)}
  , vread_vwrite_commutative :: i:Index -> j:Index -> {i_neq_j : Proof | i /= j} -> x:a ->
      {IsCommutative (vseq iMonad) (vseq iMonad (vread i) (lift iMonad vunit)) (vwrite j x)}
  }
@-}
data VMonadArray m a = VMonadArray
  { iMonad :: VMonad m,
    vread :: Index -> m a,
    vwrite :: Index -> a -> m VUnit,
    vread_vwrite :: Index -> Proof,
    vwrite_vread :: Index -> a -> Proof,
    vwrite_vwrite :: Index -> a -> a -> Proof,
    vread_vread :: Index -> (a -> a -> a) -> Proof,
    vread_commutative :: Index -> Index -> Proof -> Proof,
    vwrite_commutative :: Index -> Index -> Proof -> a -> a -> Proof,
    vread_vwrite_commutative :: Index -> Index -> Proof -> a -> Proof
  }

{-@ reflect vreadList @-}
vreadList :: VMonadArray m a -> Index -> VNat -> m (VList a)
vreadList iMonadArray _ Zero = lift_ VNil
  where
    lift_ = lift iMonad_
    iMonad_ = iMonad iMonadArray
vreadList iMonadArray i (Suc n) =
  vmapM2_
    VCons
    (vread_ i)
    (vreadList_ (Suc i) n)
  where
    vread_ = vread iMonadArray
    vreadList_ = vreadList iMonadArray
    vmapM2_ = vmapM2 iMonad_
    iMonad_ = iMonad iMonadArray

{-@ reflect vwriteList @-}
vwriteList :: VMonadArray m a -> Index -> VList a -> m VUnit
vwriteList iMonadArray _ VNil = lift_ ()
  where
    lift_ = lift iMonad_
    iMonad_ = iMonad iMonadArray
vwriteList iMonadArray i (VCons x xs) =
  vseq_
    (vwrite_ i x)
    (vwriteList_ (Suc i) xs)
  where
    vseq_ = vseq iMonad_
    vwrite_ = vwrite iMonadArray
    vwriteList_ = vwriteList iMonadArray
    iMonad_ = iMonad iMonadArray

{-@ reflect vwriteListToLength @-}
vwriteListToLength :: VMonadArray m a -> Index -> VList a -> m VNat
vwriteListToLength iMonadArray i xs =
  vseq_
    (vwriteList_ i xs)
    (lift_ (vlength xs))
  where
    vwriteList_ = vwriteList iMonadArray
    vseq_ = vseq iMonad_
    lift_ = lift iMonad_
    iMonad_ = iMonad iMonadArray

{-@ reflect vwriteListsToLengths2 @-}
vwriteListsToLengths2 ::
  VMonadArray m a ->
  Index ->
  VTuple2D (VList a) ->
  m (VTuple2D VNat)
vwriteListsToLengths2 iMonadArray i (xs, ys) =
  vseq_
    (vwriteList_ i (vappend xs ys))
    (lift_ (vlength xs, vlength ys))
  where
    vseq_ = vseq iMonad_
    lift_ = lift iMonad_
    vwriteList_ = vwriteList iMonadArray
    iMonad_ = iMonad iMonadArray

{-@ reflect vwriteListsToLengths3 @-}
vwriteListsToLengths3 ::
  VMonadArray m a ->
  Index ->
  VTuple3D (VList a) ->
  m (VTuple3D VNat)
vwriteListsToLengths3 iMonadArray i (xs, ys, zs) =
  vseq_
    (vwriteList_ i (vappend xs (vappend ys zs)))
    (lift_ (vlength xs, vlength ys, vlength zs))
  where
    vseq_ = vseq iMonad_
    lift_ = lift iMonad_
    vwriteList_ = vwriteList iMonadArray
    iMonad_ = iMonad iMonadArray

-- TODO. prove
{-@
assume vwriteList_vappend :: forall m a . iMonadArray:VMonadArray m a -> i:Index -> xs:VList a -> ys:VList a ->
  {vwriteList iMonadArray i (vappend xs ys) = vseq (iMonad iMonadArray) (vwriteList iMonadArray i xs) (vwriteList iMonadArray (VNat.vadd i (vlength xs)) ys)}
@-}
vwriteList_vappend ::
  forall m a.
  VMonadArray m a ->
  Index ->
  VList a ->
  VList a ->
  Proof
vwriteList_vappend _ _ _ _ = ()

-- TODO: proof in progress
-- vwriteList_vappend iMonadArray i VNil ys =
--   vwriteList_ i (vappend VNil ys)
--     === vwriteList_ i ys
--     === ( vseq_ (lift_ vunit) (vwriteList_ i ys)
--             ? vseq_identity_ (vwriteList_ i ys)
--         )
--     === ( vseq_ (lift_ vunit) (vwriteList_ (VNat.vadd i Zero) ys)
--             ? vadd_identity i
--         )
--     === vseq_
--       (vwriteList_ i VNil)
--       (vwriteList_ (vadd i (vlength VNil)) ys)
--     *** QED
--   where
--     vseq_ = vseq iMonad_
--     lift_ = lift iMonad_
--     vseq_identity_ = vseq_identity iMonad_
--     vwriteList_ = vwriteList iMonadArray
--     iMonad_ = iMonad iMonadArray
-- vwriteList_vappend iMonadArray i (VCons x xs) ys = ()

{- TODO. fix error:
 /Users/henry/Documents/Projects/monadic-quicksort-verification/monadic-quicksort-verification/src/VMonadArray.hs:166:26: Error: GHC Error

 166 |     === vseq_ (vwrite_ i x) (vwriteList_ (Suc i) (vappend xs ys))
                                ^

         Occurs check: cannot construct the infinite type: a ~ VList a
make: *** [check] Error 2

-}
--  vwriteList_ i (vappend (VCons x xs) ys)
--    === vwriteList_ i (VCons x (vappend xs ys))
--    === vseq_ (vwrite_ i x) (vwriteList_ (Suc i) (vappend xs ys))
--    === vseq_
--          (vwrite_ i x)
--          (vseq_ (vwriteList_ (Suc i) xs)
--                 (vwriteList_ (vadd (Suc i) (vlength xs)) ys)
--          )
--    ?   vwriteList_vappend_ (Suc i) xs ys
--    === vseq_ (vseq_ (vwrite_ i x) (vwriteList_ (Suc i) xs))
--              (vwriteList_ (vadd (Suc i) (vlength xs)) ys)
--    === vseq_ (vwriteList_ i (VCons x xs))
--              (vwriteList_ (vadd (Suc i) (vlength xs)) ys)
--    === vseq_ (vwriteList_ i (VCons x xs))
--              (vwriteList_ (Suc (vadd i (vlength xs))) ys)
--    === vseq_ (vwriteList_ i (VCons x xs))
--              (vwriteList_ (vadd i (Suc (vlength xs))) ys)
--    === vseq_ (vwriteList_ i (VCons x xs))
--              (vwriteList_ (vadd i (vlength (VCons x xs))) ys)
--    *** QED
-- where
--  vwrite_             = vwriteList iMonadArray
--  vwriteList_         = vwriteList iMonadArray
--  vwriteList_vappend_ = vwriteList_vappend iMonadArray
--  vseq_               = vseq iMonad_
--  iMonad_             = iMonad iMonadArray

vswap :: forall m a. VMonadArray m a -> Index -> Index -> m VUnit
vswap iMonadArray i j =
  bind_
    (vread_ i)
    ( \x ->
        bind_
          (vread_ j)
          ( \y ->
              vseq_
                (vwrite_ i y)
                (vwrite_ j x)
          )
    )
  where
    bind_ = bind iMonad_
    vseq_ = vseq iMonad_
    vread_ = vread iMonadArray
    vwrite_ = vwrite iMonadArray
    iMonad_ = iMonad iMonadArray
