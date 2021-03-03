module VIdentity where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation
import VFunctor
import VMonad

-- Data. The identity functor trivially wraps a type with its single
-- constructor.
{-@
data VIdentity a = VIdentity a
@-}
data VIdentity a = VIdentity a

{-@ reflect vmapF_VIdentity @-}
vmapF_VIdentity ::
  forall a b. (a -> b) -> (VIdentity a -> VIdentity b)
vmapF_VIdentity f (VIdentity x) = VIdentity (f x)

-- TODO: prove
-- {-@ automatic-instances vmapF_vid_VIdentity @-}
{-@
assume vmapF_vid_VIdentity :: forall a. x:VIdentity a ->
  {vmapF_VIdentity vid x = vid x}
@-}
vmapF_vid_VIdentity :: forall a. VIdentity a -> Proof
vmapF_vid_VIdentity _ = ()

-- TODO: prove that VIdentity is a VFunctor
-- -- TODO: why does vmapF_vid_VIdentity need to be qualified?
-- {-@ reflect iFunctor_VIdentity @-}
-- iFunctor_VIdentity :: VFunctor VIdentity
-- iFunctor_VIdentity =
--   VFunctor {vmapF = vmapF_VIdentity, vmapF_vid = VIdentity.vmapF_vid_VIdentity}

-- {-@ reflect lift_VIdentity @-}
-- lift_VIdentity :: forall a. a -> VIdentity a
-- lift_VIdentity = VIdentity

-- {-@ reflect bind_VIdentity @-}
-- bind_VIdentity ::
--   forall a b. VIdentity a -> (a -> VIdentity b) -> VIdentity b
-- bind_VIdentity (VIdentity x) k = k x

-- {-@
-- bind_correct_VIdentity :: forall a b . m:VIdentity a -> f:(a -> b) ->
--   {bind_VIdentity m (vcomp lift_VIdentity f) = vmapF iFunctor_VIdentity f m}
-- @-}
-- bind_correct_VIdentity ::
--   forall a b. VIdentity a -> (a -> b) -> Proof
-- bind_correct_VIdentity _ _ = ()

-- {-@
-- bind_identity_VIdentity :: forall a . m:VIdentity a ->
--   {bind_VIdentity m lift_VIdentity = m}
-- @-}
-- bind_identity_VIdentity :: forall a. VIdentity a -> Proof
-- bind_identity_VIdentity _ = ()

-- {-@
-- bind_lift_VIdentity :: forall a b . k:(a -> VIdentity b) -> x:a ->
--   {bind_VIdentity (lift_VIdentity x) k = k x}
-- @-}
-- bind_lift_VIdentity :: forall a b. (a -> VIdentity b) -> a -> Proof
-- bind_lift_VIdentity _ _ = ()

-- {-@
-- bind_bind_VIdentity :: forall a b c . m:VIdentity a -> k1:(a -> VIdentity b) -> k2:(b -> VIdentity c) ->
--   {bind_VIdentity (bind_VIdentity m k1) k2 = bind_VIdentity m (raw_kleisli bind_VIdentity k1 k2)}
-- @-}
-- bind_bind_VIdentity ::
--   forall a b c.
--   VIdentity a ->
--   (a -> VIdentity b) ->
--   (b -> VIdentity c) ->
--   Proof
-- bind_bind_VIdentity _ _ _ = ()

-- {-@ reflect iMonad_VIdentity @-}
-- iMonad_VIdentity :: VMonad VIdentity
-- iMonad_VIdentity =
--   VMonad
--     { iFunctor = iFunctor_VIdentity,
--       bind = bind_VIdentity,
--       lift = lift_VIdentity,
--       bind_correct = bind_correct_VIdentity,
--       bind_identity = bind_identity_VIdentity,
--       bind_lift = bind_lift_VIdentity,
--       bind_bind = bind_bind_VIdentity
--     }
