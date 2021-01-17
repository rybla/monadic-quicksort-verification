module VMonadPlus where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation
import VBool
import VMonad

-- A plus-monad (there must be a better name for this...) is TODO.
-- - vmpepsilon: e.
-- - vmpadd: x <+> y.
-- - vmpaddF: f <+> g.
-- - vbind_identity_left:               e >>= f = e.
-- - vseq_identity_right:                x >> e = e.
-- - vmpadd_identity:                   x <+> e = x,
--                                      e <+> x = x.
-- - vmpadd_distributive_left:  (x <+> y) >>= f = (x >>= f) <+> (y >>= f).
-- - vmpadd_distributive_right: x >>= (f <+> g) = (x >>= f) <+> (x >>= g).
{-@
data VMonadPlus m = VMonadPlus
  { iMonad :: VMonad m
  , vmpepsilon :: forall a . m a
  , vmpadd :: forall a . Op2 (m a)
  , vmpadd_identity :: forall a. x:m a ->
      {IsIdentity vmpadd vmpepsilon x}
  , vmpadd_associative :: forall a. x: m a -> y:m a -> z:m a ->
      {IsAssociative vmpadd x y z}
  , vmpadd_distributive_left :: forall a b . x:m a -> y:m a -> f:(a -> m b) ->
      {vbind iMonad (vmpadd x y) f = vmpadd (vbind iMonad x f) (vbind iMonad y f)}
  , vmpadd_distributive_right :: forall a b . x:m a -> f:(a -> m b) -> g:(a -> m b) ->
      {vbind iMonad x (raw_vmpaddF vmpadd f g) = vmpadd (vbind iMonad x f) (vbind iMonad x g)}
  , vbind_identity_left :: forall a b . f:(a -> m b) ->
      {vbind iMonad vmpepsilon f = vmpepsilon}
  , vseq_identity_right :: forall a . x:m a ->
      {vseq iMonad x vmpepsilon = vmpepsilon} }
@-}
data VMonadPlus m = VMonadPlus
  { iMonad :: VMonad m,
    vmpepsilon :: forall a. m a,
    vmpadd :: forall a. Op2 (m a),
    vmpadd_identity :: forall a. Property (m a),
    vmpadd_associative :: forall a. Property3 (m a),
    vmpadd_distributive_left :: forall a b. m a -> m a -> (a -> m b) -> Proof,
    vmpadd_distributive_right :: forall a b. m a -> (a -> m b) -> (a -> m b) -> Proof,
    vbind_identity_left :: forall a b. (a -> m b) -> Proof,
    vseq_identity_right :: forall a. m a -> Proof
  }

{-@ reflect raw_vmpaddF @-}
raw_vmpaddF ::
  forall m a b.
  (forall a'. Op2 (m a')) -> -- vmpadd
  (a -> m b) ->
  (a -> m b) ->
  (a -> m b)
raw_vmpaddF raw_vmpadd f g x = raw_vmpadd (f x) (g x)

{-@ reflect vmpaddF @-}
vmpaddF ::
  forall m a b.
  VMonadPlus m ->
  (a -> m b) ->
  (a -> m b) ->
  (a -> m b)
vmpaddF iMP = raw_vmpaddF vmpadd_ where vmpadd_ = vmpadd iMP

-- Function. Condition `MonadPlus` branch by a boolean.
{-@ reflect mguard @-}
mguard :: forall m. VMonadPlus m -> Bool -> m ()
mguard iMonadPlus b = if b then vlift_ () else vmpepsilon_
  where
    vlift_ = vlift iMonad_
    vmpepsilon_ = vmpepsilon iMonadPlus
    iMonad_ = iMonad iMonadPlus

-- Function. Condition `MonadPlus` branch by predicating a value.
{-@ reflect mguardBy @-}
mguardBy :: forall m a. VMonadPlus m -> Predicate a -> a -> m a
mguardBy iMonadPlus p x = vseq_ (mguard_ (p x)) (vlift_ x)
  where
    vseq_ = vseq iMonad_
    mguard_ = mguard iMonadPlus
    vlift_ = vlift iMonad_
    iMonad_ = iMonad iMonadPlus

-- Predicate. Plus-monadic refinement.
{-@
predicate RefinesPlusMonadic IMONADPLUS X Y =
  vmpadd IMONADPLUS X Y = Y
@-}

-- Predicate. Function-extended plus-monadic refinement.
{-@
predicate RefinesPlusMonadicF IMONADPLUS F G X =
  RefinesPlusMonadic IMONADPLUS (F X) (G X)
@-}

-- Lemma. e refines x.
{-@
vmpepsilon_refines :: forall m a. iMonadPlus:VMonadPlus m -> x:m a ->
  {RefinesPlusMonadic iMonadPlus (vmpepsilon iMonadPlus) x}
@-}
vmpepsilon_refines :: forall m a. VMonadPlus m -> m a -> Proof
vmpepsilon_refines iMonadPlus x = vmpadd_identity_ x
  where
    vmpadd_identity_ = vmpadd_identity iMonadPlus

-- TODO: assumption?
-- Lemma. x refines x.
{-@
assume identity_refines :: forall m a. iMonadPlus:VMonadPlus m -> x:m a ->
  {RefinesPlusMonadic iMonadPlus x x}
@-}
identity_refines :: forall m a. VMonadPlus m -> m a -> Proof
identity_refines _ _ = ()

-- TODO: assumption?
-- Lemma. x refines x <+> y
{-@
assume component_left_refines ::
  forall m a.
  iMonadPlus:VMonadPlus m ->
  x:m a ->
  y:m a ->
  {RefinesPlusMonadic iMonadPlus x (vmpadd iMonadPlus x y)}
@-}
component_left_refines :: forall m a. VMonadPlus m -> m a -> m a -> Proof
component_left_refines _ _ _ = ()

-- TODO: assumption?
-- Lemma. y refines x <+> y.
{-@
assume component_right_refines ::
  forall m a.
  iMonadPlus:VMonadPlus m ->
  x:m a ->
  y:m a ->
  {RefinesPlusMonadic iMonadPlus y (vmpadd iMonadPlus x y)}
@-}
component_right_refines :: forall m a. VMonadPlus m -> m a -> m a -> Proof
component_right_refines _ _ _ = ()

-- TODO: prove
-- Lemma. `vbind` is monotonic with respect to refinement.
{-@
assume vbind_monotonic_refinement ::
  forall m a b .
  iMonadPlus:VMonadPlus m ->
  x:m a -> y: m a ->
  f:(a -> m b) ->
  {RefinesPlusMonadic iMonadPlus x y =>
   RefinesPlusMonadic iMonadPlus (vbind (VMonadPlus.iMonad iMonadPlus) x f) (vbind (VMonadPlus.iMonad iMonadPlus) y f)}
@-}
vbind_monotonic_refinement ::
  forall m a b.
  VMonadPlus m ->
  m a ->
  m a ->
  (a -> m b) ->
  Proof
vbind_monotonic_refinement _ _ _ _ = ()

-- TODO: prove
-- Lemma. `mguard` monad-commutes with `m` since `m` has just one effect.
{-@
assume mguard_isCommutativeMonadic :: forall m a b .
  iMonadPlus:VMonadPlus m ->
  b:Bool ->
  x:m a ->
  f:(a -> b) ->
  {IsCommutativeMonadic (VMonadPlus.iMonad iMonadPlus) (mguard iMonadPlus b)
    x (vconstF f)}
@-}
mguard_isCommutativeMonadic ::
  forall m a b. VMonadPlus m -> Bool -> m a -> (a -> b) -> Proof
mguard_isCommutativeMonadic _ _ _ _ = ()

-- Function.
{-@ reflect mguard_and @-}
mguard_and :: forall m. VMonadPlus m -> Bool -> Bool -> m ()
mguard_and iMonadPlus b1 b2 = mguard iMonadPlus (vand b1 b2)

-- TODO: prove
-- Lemma.
{-@
assume mguard_and_vseq :: forall m .
  iMonadPlus:VMonadPlus m ->
  b1:Bool -> b2:Bool ->
  {mguard_and iMonadPlus b1 b2 = vseq (VMonadPlus.iMonad iMonadPlus) (mguard iMonadPlus b1) (mguard iMonadPlus b2)}
@-}
mguard_and_vseq :: forall m. VMonadPlus m -> Bool -> Bool -> Proof
mguard_and_vseq _ _ _ = ()

-- Function.
{-@ reflect mguard_disjoint @-}
mguard_disjoint ::
  forall m a. VMonadPlus m -> Bool -> m a -> m a -> m a
mguard_disjoint iMonadPlus b x y =
  vmpadd
    iMonadPlus
    (vseq (VMonadPlus.iMonad iMonadPlus) (mguard iMonadPlus b) x)
    (vseq (VMonadPlus.iMonad iMonadPlus) (mguard iMonadPlus (vnot b)) y)

-- TODO: prove
-- Lemma.
-- NOTE. idk why I need to prefix `vbranch` with `VBool` here, but I do...
{-@
assume mguard_disjoint_branch :: forall m a .
  iMonadPlus:VMonadPlus m ->
  b:Bool -> x:m a -> y: m a ->
  {RefinesPlusMonadic iMonadPlus (mguard_disjoint iMonadPlus b x y) (VBool.vbranch b x y)}
@-}
mguard_disjoint_branch ::
  forall m a. VMonadPlus m -> Bool -> m a -> m a -> Proof
mguard_disjoint_branch = undefined
