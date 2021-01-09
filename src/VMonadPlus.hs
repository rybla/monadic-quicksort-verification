module VMonadPlus where

import           Liquid.ProofCombinators
import           Function
import           Relation
import           VMonad
import           VBool


-- A plus-monad (there must be a better name for this...) is TODO.
{-@
data VMonadPlus m = VMonadPlus
  { iMonad :: VMonad m
  , vepsilon :: forall a . m a
  , vmadd :: forall a . Op2 (m a)
  , vbind_identity_left :: forall a b . f:(a -> m b) ->
      {vbind iMonad vepsilon f = vepsilon}
  , vseq_identity_right :: forall a . m:m a ->
      {vseq iMonad m vepsilon = vepsilon}
  , vmadd_distributive_left :: forall a b . m1:m a -> m2:m a -> f:(a -> m b) ->
      {vbind iMonad (vmadd m1 m2) f = vmadd (vbind iMonad m1 f) (vbind iMonad m2 f)}
  , vmadd_distributive_right :: forall a b . m: m a -> f:(a -> m b) -> g:(a -> m b) ->
      {vbind iMonad m (raw_vmaddF vmadd f g) = vmadd (vbind iMonad m f) (vbind iMonad m g)} }
@-}
data VMonadPlus m = VMonadPlus
  { iMonad :: VMonad m
  , vepsilon :: forall a . m a
  , vmadd :: forall a . Op2 (m a)
  , vbind_identity_left :: forall a b . (a -> m b) -> Proof
  , vseq_identity_right :: forall a . m a -> Proof
  , vmadd_distributive_left :: forall a b . m a -> m a -> (a -> m b) -> Proof
  , vmadd_distributive_right :: forall a b . m a -> (a -> m b) -> (a -> m b) -> Proof }


{-@ reflect raw_vmaddF @-}
raw_vmaddF
  :: forall m a b
   . (forall a . Op2 (m a)) -- vmadd
  -> (a -> m b)
  -> (a -> m b)
  -> (a -> m b)
raw_vmaddF raw_vmadd f g x = raw_vmadd (f x) (g x)


{-@ reflect vmaddF @-}
vmaddF
  :: forall m a b
   . VMonadPlus m
  -> (a -> m b)
  -> (a -> m b)
  -> (a -> m b)
vmaddF iMP = raw_vmaddF vmadd_ where vmadd_ = vmadd iMP


-- Function. Condition `MonadPlus` branch by a boolean.
{-@ reflect mguard @-}
mguard :: forall m . VMonadPlus m -> Bool -> m ()
mguard iMonadPlus b = if b then vlift_ () else vepsilon_
 where
  vlift_    = vlift iMonad_
  vepsilon_ = vepsilon iMonadPlus
  iMonad_   = iMonad iMonadPlus


-- Function. Condition `MonadPlus` branch by predicating a value.
{-@ reflect mguardBy @-}
mguardBy :: forall m a . VMonadPlus m -> Predicate a -> a -> m a
mguardBy iMonadPlus p x = vseq_ (mguard_ (p x)) (vlift_ x)
 where
  vseq_   = vseq iMonad_
  mguard_ = mguard iMonadPlus
  vlift_  = vlift iMonad_
  iMonad_ = iMonad iMonadPlus


-- Predicates. Plus-monadic refinement.
{-@
predicate RefinesPlusMonadic IMONADPLUS M1 M2 =
  vmadd IMONADPLUS M1 M2 = M2
@-}
{-@
predicate RefinesPlusMonadicF IMONADPLUS F G X =
  RefinesPlusMonadic IMONADPLUS (F X) (G X)
@-}


-- Lemma. `vbind` is monotonic with respect to refinement.
{-@
assume vbind_monotonic_refinement :: forall m a b .
  iMonadPlus:VMonadPlus m ->
  m1:m a -> m2: m a ->
  f:(a -> m b) ->
  {RefinesPlusMonadic iMonadPlus m1 m2 =>
   RefinesPlusMonadic iMonadPlus (vbind (iMonad iMonadPlus) m1 f) (vbind (iMonad iMonadPlus) m2 f)}
@-}
vbind_monotonic_refinement
  :: forall m a b . VMonadPlus m -> m a -> m a -> (a -> m b) -> Proof
vbind_monotonic_refinement _ _ _ _ = ()


-- Lemma. `mguard` monad-commutes with `m` since `m` has just one effect.
{-@
assume mguard_isCommutativeMonadic :: forall m a b .
  iMonadPlus:VMonadPlus m ->
  b:Bool ->
  m:m a ->
  f:(a -> b) ->
  {IsCommutativeMonadic (iMonad iMonadPlus) (mguard iMonadPlus b) m (vconstF f)}
@-}
mguard_isCommutativeMonadic
  :: forall m a b . VMonadPlus m -> Bool -> m a -> (a -> b) -> Proof
mguard_isCommutativeMonadic _ _ _ _ = ()


-- Function.
{-@ reflect mguard_and @-}
mguard_and :: forall m . VMonadPlus m -> Bool -> Bool -> m ()
mguard_and iMonadPlus b1 b2 = mguard iMonadPlus (vand b1 b2)


-- Lemma.
{-@
assume mguard_and_vseq :: forall m .
  iMonadPlus:VMonadPlus m ->
  b1:Bool -> b2:Bool ->
  {mguard_and iMonadPlus b1 b2 = vseq (iMonad iMonadPlus) (mguard iMonadPlus b1) (mguard iMonadPlus b2)}
@-}
mguard_and_vseq :: forall m . VMonadPlus m -> Bool -> Bool -> Proof
mguard_and_vseq _ _ _ = ()


-- Function.
{-@ reflect mguard_disjoint @-}
mguard_disjoint
  :: forall m a . VMonadPlus m -> Bool -> m a -> m a -> m a
mguard_disjoint iMonadPlus b m1 m2 = vmadd
  iMonadPlus
  (vseq (iMonad iMonadPlus) (mguard iMonadPlus b) m1)
  (vseq (iMonad iMonadPlus) (mguard iMonadPlus (vnot b)) m1)


-- Lemma.
-- NOTE. idk why I need to prefix `vbranch` with `VBool` here, but I do...
{-@
assume mguard_disjoint_branch :: forall m a .
  iMonadPlus:VMonadPlus m ->
  b:Bool -> m1:m a -> m2: m a ->
  {RefinesPlusMonadic iMonadPlus (mguard_disjoint iMonadPlus b m1 m2) (VBool.vbranch b m1 m2)}
@-}
mguard_disjoint_branch
  :: forall m a . VMonadPlus m -> Bool -> m a -> m a -> Proof
mguard_disjoint_branch = undefined
