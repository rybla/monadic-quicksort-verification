module VMonadPlus where

import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.Liquid.ProofCombinators (trivial, (&&&), (==!), (===))
import Relation
import VBool
import VMonad
import Prelude hiding ((>>), (>>=))

-- A plus-monad (there must be a better name for this...) is TODO.
-- - vepsilonMP: e.
-- - vaddMP: x <+> y.
-- - vaddMPF: f <+> g.
-- - vbind_zero_left:                   e >>= f = e.
-- - vseq_zero_right:                    x >> e = e.
-- - vaddMP_identity:                   x <+> e = x,
--                                      e <+> x = x.
-- - vaddMP_distributive_left:  (x <+> y) >>= f = (x >>= f) <+> (y >>= f).
-- - vaddMP_distributive_right: x >>= (f <+> g) = (x >>= f) <+> (x >>= g).
{-@
data VMonadPlus m = VMonadPlus
  { iMonad :: VMonad m
  , vepsilonMP :: forall a . m a
  , vaddMP :: forall a . Op2 (m a)
  , vaddMP_identity :: forall a. x:m a ->
      {IsIdentity vaddMP vepsilonMP x}
  , vaddMP_associative :: forall a. x: m a -> y:m a -> z:m a ->
      {IsAssociative vaddMP x y z}
  , vaddMP_distributive_left :: forall a b . x:m a -> y:m a -> f:(a -> m b) ->
      {vbind iMonad (vaddMP x y) f = vaddMP (vbind iMonad x f) (vbind iMonad y f)}
  , vaddMP_distributive_right :: forall a b . x:m a -> f:(a -> m b) -> g:(a -> m b) ->
      {vbind iMonad x (raw_vaddMPF vaddMP f g) = vaddMP (vbind iMonad x f) (vbind iMonad x g)}
  , vbind_zero_left :: forall a b . f:(a -> m b) ->
      {vbind iMonad vepsilonMP f = vepsilonMP}
  , vseq_zero_right :: forall a . x:m a ->
      {vseq iMonad x vepsilonMP = vepsilonMP} }
@-}
data VMonadPlus m = VMonadPlus
  { iMonad :: VMonad m,
    vepsilonMP :: forall a. m a,
    vaddMP :: forall a. Op2 (m a),
    vaddMP_identity :: forall a. Property (m a),
    vaddMP_associative :: forall a. Property3 (m a),
    vaddMP_distributive_left :: forall a b. m a -> m a -> (a -> m b) -> Proof,
    vaddMP_distributive_right :: forall a b. m a -> (a -> m b) -> (a -> m b) -> Proof,
    vbind_zero_left :: forall a b. (a -> m b) -> Proof,
    vseq_zero_right :: forall a. m a -> Proof
  }

{-@ reflect raw_vaddMPF @-}
raw_vaddMPF ::
  forall m a b.
  Op2 (m b) -> -- vaddMP
  (a -> m b) ->
  (a -> m b) ->
  (a -> m b)
raw_vaddMPF (<+>) f g x = f x <+> g x

{-@ reflect vaddMPF @-}
vaddMPF ::
  forall m a b.
  VMonadPlus m ->
  (a -> m b) ->
  (a -> m b) ->
  (a -> m b)
vaddMPF iMonadPlus = raw_vaddMPF (<+>)
  where
    (<+>) = vaddMP iMonadPlus

-- Function. Condition `MonadPlus` branch by a boolean.
{-@ reflect guard @-}
guard :: forall m. VMonadPlus m -> Bool -> m ()
guard iMonadPlus b = if b then vlift_ () else vepsilonMP_
  where
    vlift_ = vlift iMonad_
    vepsilonMP_ = vepsilonMP iMonadPlus
    iMonad_ = iMonad iMonadPlus

-- Function. Condition `MonadPlus` branch by predicating a value.
{-@ reflect guardBy @-}
guardBy :: forall m a. VMonadPlus m -> Predicate a -> a -> m a
guardBy iMonadPlus p x = guard_ (p x) >> vlift_ x
  where
    (>>) = vseq iMonad_
    guard_ = guard iMonadPlus
    vlift_ = vlift iMonad_
    iMonad_ = iMonad iMonadPlus

-- Predicate. Plus-monadic refinement.
{-@
predicate RefinesPlusMonadic IMONADPLUS X Y =
  vaddMP IMONADPLUS X Y = Y
@-}

-- Predicate. Function-extended plus-monadic refinement.
{-@
predicate RefinesPlusMonadicF IMONADPLUS F G X =
  RefinesPlusMonadic IMONADPLUS (F X) (G X)
@-}

-- Lemma. e refines x.
{-@
vepsilonMP_refines :: forall m a. iMonadPlus:VMonadPlus m -> x:m a ->
  {RefinesPlusMonadic iMonadPlus (vepsilonMP iMonadPlus) x}
@-}
vepsilonMP_refines :: forall m a. VMonadPlus m -> m a -> Proof
vepsilonMP_refines iMonadPlus x = vaddMP_identity_ x
  where
    vaddMP_identity_ = vaddMP_identity iMonadPlus

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
  {RefinesPlusMonadic iMonadPlus x (vaddMP iMonadPlus x y)}
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
  {RefinesPlusMonadic iMonadPlus y (vaddMP iMonadPlus x y)}
@-}
component_right_refines :: forall m a. VMonadPlus m -> m a -> m a -> Proof
component_right_refines _ _ _ = ()

-- Lemma. `vbind` is monotonic with respect to refinement.
{-@
vbind_monotonic_refinement ::
  forall m a b. iMonadPlus:VMonadPlus m ->
  x:m a -> y: m a -> f:(a -> m b) ->
  {H:() | RefinesPlusMonadic iMonadPlus x y} ->
  {RefinesPlusMonadic iMonadPlus (vbind (iMonad iMonadPlus) x f) (vbind (iMonad iMonadPlus) y f)}
@-}
vbind_monotonic_refinement ::
  forall m a b.
  VMonadPlus m ->
  m a ->
  m a ->
  (a -> m b) ->
  Proof ->
  Proof
vbind_monotonic_refinement iMonadPlus x y f ref_x_y =
  (x >>= f) <+> (y >>= f)
    ==. ((x <+> y) >>= f ? vaddMP_distributive_left_ x y f)
    ==. (y >>= f ? ref_x_y)
    *** QED
  where
    (>>=) = vbind iMonad_
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = vaddMP iMonadPlus
    iMonad_ = iMonad iMonadPlus

    vaddMP_distributive_left_ = vaddMP_distributive_left iMonadPlus

-- Lemma. `guard` monad-commutes with `m` since `m` has just one effect.
{-@
guard_isCommutativeMonadic :: forall m a b .
  iMonadPlus:VMonadPlus m ->
  b:Bool ->
  x:m a ->
  f:(a -> b) ->
  {IsCommutativeMonadic (iMonad iMonadPlus) (guard iMonadPlus b)
    x (vconstF f)}
@-}
guard_isCommutativeMonadic ::
  forall m a b. VMonadPlus m -> Bool -> m a -> (a -> b) -> Proof
-- b = True
guard_isCommutativeMonadic iMonadPlus True x f =
  vmapM2_ (vconstF f) (guard_ True) x
    -- [def] vmapM2
    ==. guard_ True >>= vmapM2_aux1_ (vconstF f) x
    -- [def] guard on True
    ==. vlift_ () >>= vmapM2_aux1_ (vconstF f) x
    -- [lem] vbind_vlift
    ==. ( vmapM2_aux1_ (vconstF f) x ()
            ? vbind_vlift_ (vmapM2_aux1_ (vconstF f) x) (())
        )
    -- [def] vmapM2_aux1
    ==. x >>= vmapM2_aux2_ (vconstF f) ()
    -- [lem]
    -- TODO: fix extensionality
    ==. ( x >>= vmapM2_aux1_ (vflip (vconstF f)) (vlift_ ())
            ? ( extensionality
                  (vmapM2_aux2_ (vconstF f) ())
                  (vmapM2_aux1_ (vflip (vconstF f)) (vlift_ ()))
                  (guard_isCommutativeMonadic_True_lem1_ f)
              )
        )
    -- [def] guard on True
    ==. x >>= vmapM2_aux1_ (vflip (vconstF f)) (guard_ True)
    -- [def] vmapM2
    ==. vmapM2_ (vflip (vconstF f)) x (guard_ True)
    *** QED
  where
    -- iMonad
    (>>) = vseq iMonad_
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = vbind iMonad_
    vlift_ = vlift iMonad_
    vmapM2_ :: forall a b c. (a -> b -> c) -> m a -> m b -> m c
    vmapM2_ = vmapM2 iMonad_
    vmapM2_aux1_ :: forall a b c. (a -> b -> c) -> m b -> a -> m c
    vmapM2_aux1_ = vmapM2_aux1 iMonad_
    vmapM2_aux2_ :: forall a b c. (a -> b -> c) -> a -> b -> m c
    vmapM2_aux2_ = vmapM2_aux2 iMonad_
    vbind_vlift_ = vbind_vlift iMonad_
    guard_isCommutativeMonadic_True_lem1_ =
      guard_isCommutativeMonadic_True_lem1
        iMonad_
    iMonad_ = iMonad iMonadPlus
    -- iMonadPlus
    guard_ = guard iMonadPlus
-- b = False
guard_isCommutativeMonadic iMonadPlus False m f =
  vmapM2_ (vconstF f) (guard_ False) m
    -- [def] guard on False
    ==. vmapM2_ (vconstF f) vepsilonMP_ m
    -- [def] vmapM2
    ==. vepsilonMP_ >>= vmapM2_aux1_ (vconstF f) m
    -- [lem] vbind_zero_left
    ==. ( vepsilonMP_
            ? vbind_zero_left_ (vmapM2_aux1_ (vconstF f) m)
        )
    -- [lem] vseq_zero_right
    ==. ( m >> vepsilonMP_
            ? vseq_zero_right_ m
        )
    -- [def] >>
    ==. m >>= vconst vepsilonMP_
    -- [lem]
    ==! ( m >>= vmapM2_aux1_ (vflip (vconstF f)) vepsilonMP_
            ? guard_isCommutativeMonadic_False_lem1_ f
        )
    -- [def] guard on False
    ==. m >>= vmapM2_aux1 iMonad_ (vflip (vconstF f)) (guard_ False)
    -- [def] vmapM2
    ==. vmapM2 iMonad_ (vflip (vconstF f)) m (guard_ False)
    *** QED
  where
    -- iMonad
    (>>) = vseq iMonad_
    (>>=) = vbind iMonad_
    vlift_ = vlift iMonad_
    vmapM2_ = vmapM2 iMonad_
    vmapM2_aux1_ = vmapM2_aux1 iMonad_
    vmapM2_aux2_ = vmapM2_aux2 iMonad_
    vbind_vlift_ = vbind_vlift iMonad_
    guard_isCommutativeMonadic_True_lem1_ =
      guard_isCommutativeMonadic_True_lem1
        iMonad_
    iMonad_ = iMonad iMonadPlus
    -- iMonadPlus
    guard_ = guard iMonadPlus
    vbind_zero_left_ = vbind_zero_left iMonadPlus
    vepsilonMP_ :: forall a. m a
    vepsilonMP_ = vepsilonMP iMonadPlus
    vseq_zero_right_ = vseq_zero_right iMonadPlus
    guard_isCommutativeMonadic_False_lem1_ =
      guard_isCommutativeMonadic_False_lem1
        iMonadPlus

{-@
guard_isCommutativeMonadic_True_lem1 ::
  forall m a b. iMonad_:VMonad m -> f:(a -> b) -> x:a ->
  {vmapM2_aux2 iMonad_ (vconstF f) VUnit.vunit x ==
   vmapM2_aux1 iMonad_ (vflip (vconstF f)) (vlift iMonad_ VUnit.vunit) x}
@-}
guard_isCommutativeMonadic_True_lem1 ::
  forall m a b.
  VMonad m ->
  (a -> b) ->
  a ->
  Proof
guard_isCommutativeMonadic_True_lem1 iMonad_ f x =
  vmapM2_aux2_ (vconstF f) ()
    ==! vmapM2_aux1_ (vflip (vconstF f)) (vlift_ ())
    *** QED
  where
    vlift_ = vlift iMonad_
    vmapM2_aux2_ = vmapM2_aux2 iMonad_
    vmapM2_aux1_ = vmapM2_aux1 iMonad_

{-@
guard_isCommutativeMonadic_False_lem1 ::
  forall m a b. iMonadPlus:VMonadPlus m ->
  f:(a -> b) -> x:a ->
  {vconst (vepsilonMP iMonadPlus) x ==
   vmapM2_aux1 (iMonad iMonadPlus) (vflip (vconstF f)) (vepsilonMP iMonadPlus) x}
@-}
guard_isCommutativeMonadic_False_lem1 ::
  forall m a b.
  VMonadPlus m ->
  (a -> b) ->
  a ->
  Proof
guard_isCommutativeMonadic_False_lem1 iMonadPlus f x =
  vconst vepsilonMP_ x
    ==. vepsilonMP_
    -- [lem] vbind_zero_left
    ==. ( vepsilonMP_ >>= vmapM2_aux2_ (vflip (vconstF f)) x
            ? vbind_zero_left_ (vmapM2_aux2_ (vflip (vconstF f)) x)
        )
    -- [def] vmapM2_aux1
    ==. vmapM2_aux1_ (vflip (vconstF f)) vepsilonMP_ x
    *** QED
  where
    (>>=) = vbind iMonad_
    vmapM2_aux1_ = vmapM2_aux1 iMonad_
    vmapM2_aux2_ = vmapM2_aux2 iMonad_
    iMonad_ = iMonad iMonadPlus
    vepsilonMP_ = vepsilonMP iMonadPlus
    vbind_zero_left_ = vbind_zero_left iMonadPlus

-- Function.
{-@ reflect guard_and @-}
guard_and :: forall m. VMonadPlus m -> Bool -> Bool -> m ()
guard_and iMonadPlus b1 b2 = guard iMonadPlus (vand b1 b2)

-- TODO: prove
-- Lemma.
{-@
assume guard_and_vseq :: forall m .
  iMonadPlus:VMonadPlus m ->
  b1:Bool -> b2:Bool ->
  {guard_and iMonadPlus b1 b2 ==
   vseq (iMonad iMonadPlus) (guard iMonadPlus b1) (guard iMonadPlus b2)}
@-}
guard_and_vseq :: forall m. VMonadPlus m -> Bool -> Bool -> Proof
guard_and_vseq _ _ _ = ()

-- Function.
{-@ reflect guard_disjoint @-}
guard_disjoint ::
  forall m a. VMonadPlus m -> Bool -> m a -> m a -> m a
guard_disjoint iMonadPlus b x y =
  vaddMP
    iMonadPlus
    (vseq (iMonad iMonadPlus) (guard iMonadPlus b) x)
    (vseq (iMonad iMonadPlus) (guard iMonadPlus (vnot b)) y)

-- TODO: prove
-- Lemma.
-- NOTE. idk why I need to prefix `vbranch` with `VBool` here, but I do...
{-@
assume guard_disjoint_branch :: forall m a .
  iMonadPlus:VMonadPlus m ->
  b:Bool -> x:m a -> y: m a ->
  {RefinesPlusMonadic iMonadPlus (guard_disjoint iMonadPlus b x y) (VBool.vbranch b x y)}
@-}
guard_disjoint_branch ::
  forall m a. VMonadPlus m -> Bool -> m a -> m a -> Proof
guard_disjoint_branch _ _ _ _ = ()
