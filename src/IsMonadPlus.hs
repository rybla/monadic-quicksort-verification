module IsMonadPlus where

import           Liquid.ProofCombinators
import           Function
import           Relation
import           IsMonad
import           VBool


{-@
data IsMonadPlus m = IsMonadPlus
  { isMonad :: IsMonad m
  , vepsilon :: forall a . m a
  , vmadd :: forall a . Op2 (m a)
  , vbind_identity_left :: forall a b . f:(a -> m b) ->
      {vbind isMonad vepsilon f = vepsilon}
  , vseq_identity_right :: forall a . m:m a ->
      {vseq isMonad m vepsilon = vepsilon}
  , vmadd_distributive_left :: forall a b . m1:m a -> m2:m a -> f:(a -> m b) ->
      {vbind isMonad (vmadd m1 m2) f = vmadd (vbind isMonad m1 f) (vbind isMonad m2 f)}
  , vmadd_distributive_right :: forall a b . m: m a -> f:(a -> m b) -> g:(a -> m b) ->
      {vbind isMonad m (raw_vmaddF vmadd f g) = vmadd (vbind isMonad m f) (vbind isMonad m g)} }
@-}
data IsMonadPlus m = IsMonadPlus
  { isMonad :: IsMonad m
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
   . IsMonadPlus m
  -> (a -> m b)
  -> (a -> m b)
  -> (a -> m b)
vmaddF iMP = raw_vmaddF vmadd_ where vmadd_ = vmadd iMP


-- Function. Condition `MonadPlus` branch by a boolean.
{-@ reflect mguard @-}
mguard :: forall m . IsMonadPlus m -> Bool -> m ()
mguard isMonadPlus b = if b then vlift_ () else vepsilon_
 where
  vlift_    = vlift isMonad_
  vepsilon_ = vepsilon isMonadPlus
  isMonad_  = isMonad isMonadPlus


-- Function. Condition `MonadPlus` branch by predicating a value.
{-@ reflect mguardBy @-}
mguardBy :: forall m a . IsMonadPlus m -> Predicate a -> a -> m a
mguardBy isMonadPlus p x = vseq_ (mguard_ (p x)) (vlift_ x)
 where
  vseq_    = vseq isMonad_
  mguard_  = mguard isMonadPlus
  vlift_   = vlift isMonad_
  isMonad_ = isMonad isMonadPlus


-- Predicate. `MonadPlus` refinement (i.e. "refinement").
{-@ predicate MRefines  IMONPLU M1 M2 = vmadd IMONPLU M1 M2 = M2 @-}
{-@ predicate MRefinesF IMONPLU F G X = MRefines IMONPLU (F X) (G X) @-}


-- Lemma. `vbind` is monotonic with respect to refinement.
{-@
assume vbind_monotonic_refinement :: forall m a b .
  isMonadPlus:IsMonadPlus m ->
  m1:m a -> m2: m a ->
  f:(a -> m b) ->
  {MRefines isMonadPlus m1 m2 =>
   MRefines isMonadPlus (vbind (isMonad isMonadPlus) m1 f) (vbind (isMonad isMonadPlus) m2 f)}
@-}
vbind_monotonic_refinement
  :: forall m a b . IsMonadPlus m -> m a -> m a -> (a -> m b) -> Proof
vbind_monotonic_refinement _ _ _ _ = ()


-- Lemma. `mguard` monad-commutes with `m` since `m` has just one effect.
{-@
assume isMCommutative_mguard :: forall m a b .
  isMonadPlus:IsMonadPlus m ->
  b:Bool ->
  m:m a ->
  f:(a -> b) ->
  {IsMCommutative (isMonad isMonadPlus) (mguard isMonadPlus b) m (vconstF f)}
@-}
isMCommutative_mguard
  :: forall m a b . IsMonadPlus m -> Bool -> m a -> (a -> b) -> Proof
isMCommutative_mguard _ _ _ _ = ()

-- Function.
{-@ reflect mguard_and @-}
mguard_and :: forall m . IsMonadPlus m -> Bool -> Bool -> m ()
mguard_and isMonadPlus b1 b2 = mguard isMonadPlus (vand b1 b2)


-- Lemma.
{-@
assume mguard_and_vseq :: forall m .
  isMonadPlus:IsMonadPlus m ->
  b1:Bool -> b2:Bool ->
  {mguard_and isMonadPlus b1 b2 = vseq (isMonad isMonadPlus) (mguard isMonadPlus b1) (mguard isMonadPlus b2)}
@-}
mguard_and_vseq :: forall m . IsMonadPlus m -> Bool -> Bool -> Proof
mguard_and_vseq _ _ _ = ()


-- Function.
{-@ reflect mguard_disjoint @-}
mguard_disjoint
  :: forall m a . IsMonadPlus m -> Bool -> m a -> m a -> m a
mguard_disjoint isMonadPlus b m1 m2 = vmadd
  isMonadPlus
  (vseq (isMonad isMonadPlus) (mguard isMonadPlus b) m1)
  (vseq (isMonad isMonadPlus) (mguard isMonadPlus (vnot b)) m1)


-- Lemma.
-- NOTE. idk why I need to prefix `vbranch` with `VBool` here, but I do...
{-@
assume mguard_disjoint_branch :: forall m a .
  isMonadPlus:IsMonadPlus m ->
  b:Bool -> m1:m a -> m2: m a ->
  {MRefines isMonadPlus (mguard_disjoint isMonadPlus b m1 m2) (VBool.vbranch b m1 m2)}
@-}
mguard_disjoint_branch
  :: forall m a . IsMonadPlus m -> Bool -> m a -> m a -> Proof
mguard_disjoint_branch = undefined
