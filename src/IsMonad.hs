module IsMonad where

import           Liquid.ProofCombinators
import           IsFunctor
import           Function
import           VUnit


-- Class.
{-@
data IsMonad m = IsMonad
  { isFunctor :: IsFunctor m
  , vlift :: forall a . a -> m a
  , vbind :: forall a b . m a -> (a -> m b) -> m b
  , vbind_correct :: forall a b . m:m a -> f:(a -> b) ->
      {vbind m (vcomp vlift f) = vmap isFunctor f m}
  , vbind_identity :: forall a . m:m a ->
      {vbind m vlift = m}
  , vbind_vlift :: forall a b . k:(a -> m b) -> x:a ->
      {vbind (vlift x) k = k x}
  , vbind_vbind :: forall a b c . m:m a -> k1:(a -> m b) -> k2:(b -> m c) ->
      {vbind (vbind m k1) k2 = vbind m (raw_kleisli vbind k1 k2)}
  }
@-}
data IsMonad m = IsMonad
  { isFunctor :: IsFunctor m
  , vlift :: forall a . a -> m a
  , vbind :: forall a b . m a -> (a -> m b) -> m b
  , vbind_correct :: forall a b . m a -> (a -> b) -> Proof
  , vbind_identity :: forall a . m a -> Proof
  , vbind_vlift :: forall a b . (a -> m b) -> a -> Proof
  , vbind_vbind :: forall a b c . m a -> (a -> m b) -> (b -> m c) -> Proof
  }


-- Function.
{-@ reflect raw_kleisli @-}
raw_kleisli
  :: forall m a b c
   . (forall a b . m a -> (a -> m b) -> m b) -- vbind
  -> (a -> m b)
  -> (b -> m c)
  -> (a -> m c)
raw_kleisli raw_vbind f g x = raw_vbind (f x) g


-- Function.
{-@ reflect kleisli @-}
kleisli
  :: forall m a b c
   . IsMonad m
  -> (a -> m b)
  -> (b -> m c)
  -> (a -> m c)
kleisli isMonad = raw_kleisli (vbind isMonad)


-- Lemma. Function.
{-@ reflect vseq @-}
vseq :: forall m a b . IsMonad m -> m a -> m b -> m b
vseq isMonad m1 m2 = (vbind isMonad) m1 (vconst m2)


-- Term.
{-@ reflect vseq_epsilon @-}
vseq_epsilon :: forall m . IsMonad m -> m VUnit
vseq_epsilon isMonad = vlift isMonad vunit


-- Lemma.
{-@
vseq_identity_left :: forall m . isMonad:IsMonad m -> m:m VUnit ->
  {IsIdentityLeft (vseq isMonad) (vseq_epsilon isMonad) m}
@-}
vseq_identity_left :: forall m . IsMonad m -> m VUnit -> Proof
vseq_identity_left isMonad m =
  vseq_ vseq_epsilon_ m
    ==. vbind_ (vlift_ vunit) (vconst m)
    ==. vconst m vunit
    ?   vbind_vlift_ (vconst m) vunit
    ==. m
    *** QED
 where
  vseq_         = vseq isMonad
  vseq_epsilon_ = vseq_epsilon isMonad
  vbind_        = vbind isMonad
  vlift_        = vlift isMonad
  vbind_vlift_  = vbind_vlift isMonad


-- Lemma
{-@
assume vseq_identity_right :: forall m a . isMonad:IsMonad m -> m:m VUnit ->
  {IsIdentityRight (vseq isMonad) (vseq_epsilon isMonad) m}
@-}
vseq_identity_right :: forall m a . IsMonad m -> m VUnit -> Proof
vseq_identity_right isMonad m = ()
 --  vseq_ m vseq_epsilon_
 --    ==. vbind_ m (vconst vseq_epsilon_)
 --    ==. vbind_ m (vconst (vlift_ vunit))
 --    ==. vbind_ m (\() -> vlift_ ())
 --    ==. vbind_ m vlift_
 --    ==. m
 --    ?   vbind_identity_ m
 --    *** QED
 -- where
 --  vseq_           = vseq isMonad
 --  vseq_epsilon_   = vseq_epsilon isMonad
 --  vbind_          = vbind isMonad
 --  vlift_          = vlift isMonad
 --  vbind_identity_ = vbind_identity isMonad


-- Lemma.
{-@
assume vseq_identity :: forall m a . isMonad:IsMonad m -> m:m VUnit ->
  {IsIdentity (vseq isMonad) (vseq_epsilon isMonad) m}
@-}
vseq_identity :: forall m a . IsMonad m -> m VUnit -> Proof
vseq_identity isMonad m =
  let _ = vseq_identity_left isMonad m
      _ = vseq_identity_right isMonad m
  in  ()


-- Function.
{-@ reflect vliftF @-}
vliftF :: forall m a b . IsMonad m -> (a -> b) -> m a -> m b
vliftF isMonad f m = vbind' m (\x -> vlift' (f x))
 where
  vlift' = vlift isMonad
  vbind' = vbind isMonad


-- Function.
{-@ reflect vliftF2 @-}
vliftF2
  :: forall m a b c . IsMonad m -> (a -> b -> c) -> m a -> m b -> m c
vliftF2 isMonad f ma mb = vbind'
  ma
  (\x -> vbind' mb (\y -> vlift' (f x y)))
 where
  vlift' = vlift isMonad
  vbind' = vbind isMonad


-- Predicate. Commutativity for monads.
{-@ predicate IsMCommutative IMON M1 M2 F =
      vliftF2 IMON F M1 M2 = vliftF2 IMON (vflip F) M2 M1 @-}
