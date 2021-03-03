module VMonad where

import Equality
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.Liquid.ProofCombinators (trivial, (&&&), (==!), (===))
import VFunctor
import VUnit
import Prelude hiding ((>>), (>>=))

-- Data Class.
{-@
data VMonad m = VMonad
  { iFunctor :: VFunctor m
  , lift :: forall a . a -> m a
  , bind :: forall a b . m a -> (a -> m b) -> m b
  , bind_correct :: forall a b . m:m a -> f:(a -> b) ->
      {bind m (vcomp lift f) = vmapF iFunctor f m}
  , bind_identity :: forall a . m:m a ->
      {bind m lift = m}
  , bind_lift :: forall a b . k:(a -> m b) -> x:a ->
      {bind (lift x) k = k x}
  , bind_associative :: forall a b c . m:m a -> k1:(a -> m b) -> k2:(b -> m c) ->
      {bind (bind m k1) k2 = bind m (raw_kleisli bind k1 k2)}
  }
@-}
data VMonad m = VMonad
  { iFunctor :: VFunctor m,
    lift :: forall a. a -> m a,
    bind :: forall a b. m a -> (a -> m b) -> m b,
    bind_correct :: forall a b. m a -> (a -> b) -> Proof,
    bind_identity :: forall a. m a -> Proof,
    bind_lift :: forall a b. (a -> m b) -> a -> Proof,
    bind_associative :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> Proof
  }

-- Function.
{-@ reflect raw_kleisli @-}
raw_kleisli ::
  forall m a b c.
  (m b -> (b -> m c) -> m c) -> -- bind
  (a -> m b) ->
  (b -> m c) ->
  (a -> m c)
raw_kleisli (>>=) f g x = f x >>= g

-- Function.
{-@ reflect kleisli @-}
kleisli :: forall m a b c. VMonad m -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisli iMonad = raw_kleisli (>>=)
  where
    (>>=) = bind iMonad

--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

-- {-@ measure meq :: forall m a. VMonad m -> m a -> m a -> Bool @-}

-- {-@ type EqM m a IMONAD M1 M2 = {_:EqMB m a | meq IMONAD M1 M2} @-}

-- {-@
-- data EqMB :: (* -> *) -> * -> * where
--     EqMB_lift :: forall m a. iMonad:VMonad m ->
--       x:a -> y:a -> PEq a {x} {y} ->
--       EqM m a {lift iMonad x} {lift iMonad y}
--   | EqMB_bind :: forall m a b. iMonad:VMonad m ->
--       m1:m a -> m2:m a -> EqM m a iMonad m1 m2 ->
--       k1:(a -> m _) -> k2:(a -> m _) -> (x:a -> EqM
--         {_:EqMB m _ | meq iMonad (k1 x) (k2 x)}) ->

-- @-}
-- -- {_:EqMB m a | meq iMonad m1 m2}
-- -- {_:EqMB m _ | meq iMonad (bind iMonad m1 k2) (bind iMonad m2 k2)}
-- --
-- -- EqM m a iMonad (lift iMonad x) (lift iMonad y)
-- -- EqM m b iMonad (k1 x) (k2 x)
-- -- EqM m b iMonad (bind iMonad m1 k1) (bind iMonad m2 k2)
-- data EqMB :: (* -> *) -> * -> * where
--   EqMB_lift ::
--     forall m a.
--     VMonad m ->
--     a -> -- x
--     a -> -- y
--     Proof -> -- x = y
--     -----------------------------------
--     EqMB m a -- lift x = lift y
--   EqMB_bind ::
--     forall m a b.
--     VMonad m ->
--     m a -> -- m1
--     m a -> -- m2
--     EqMB m a -> -- m1 = m2
--     (a -> m b) -> -- k1
--     (a -> m b) -> -- k2
--     (a -> EqMB m b) -> -- forall x, k1 x = k2 x
--     EqMB m b -- m1 >>= k1 = m2 >>= k2

--------------------------------------------------------------------------------
-- Sequencing
--------------------------------------------------------------------------------

-- Function. Monadic sequencing.
{-@ reflect vseq @-}
vseq :: forall m a b. VMonad m -> m a -> m b -> m b
vseq iMonad m1 m2 = m1 >>= vconst m2
  where
    (>>=) = bind iMonad

-- Term. The unit-monadic identity for monadic sequencing.
{-@ reflect vseq_epsilon @-}
vseq_epsilon :: forall m. VMonad m -> m VUnit
vseq_epsilon iMonad = lift iMonad ()

-- Lemma.
{-@
vseq_identity_left :: forall m . iMonad:VMonad m -> m:m VUnit ->
  {IsIdentityLeft (vseq iMonad) (vseq_epsilon iMonad) m}
@-}
vseq_identity_left :: forall m. VMonad m -> m VUnit -> Proof
vseq_identity_left iMonad m =
  vseq_epsilon_ >> m
    ==. lift_ vunit >>= vconst m
    ==. (vconst m vunit ? bind_lift_ (vconst m) vunit)
    ==. m
    *** QED
  where
    (>>) = vseq iMonad
    (>>=) = bind iMonad
    lift_ = lift iMonad
    vseq_epsilon_ = vseq_epsilon iMonad
    bind_lift_ = bind_lift iMonad

-- Lemma.
{-@
vseq_identity_right :: forall m a . iMonad:VMonad m -> m:m VUnit ->
  {IsIdentityRight (vseq iMonad) (vseq_epsilon iMonad) m}
@-}
vseq_identity_right :: forall m. VMonad m -> m VUnit -> Proof
vseq_identity_right iMonad m =
  m >> vseq_epsilon_
    ==. m >>= vconst vseq_epsilon_
    ==. m >>= vconst (lift_ vunit)
    ==! m -- TODO: prove
    *** QED
  where
    (>>) = vseq iMonad
    vseq_epsilon_ = vseq_epsilon iMonad
    (>>=) = bind iMonad
    lift_ = lift iMonad
    bind_identity_ = bind_identity iMonad

-- Lemma.
{-@
vseq_identity :: forall m a . iMonad:VMonad m -> m:m VUnit ->
  {IsIdentity (vseq iMonad) (vseq_epsilon iMonad) m}
@-}
vseq_identity :: forall m. VMonad m -> m VUnit -> Proof
vseq_identity iMonad m =
  vseq_identity_left iMonad m &&& vseq_identity_right iMonad m

-- -- Lemma. Sequencing is associative.
-- {-@
-- assume vseq_associative ::
--   forall m a b c . iMonad:VMonad m -> m1:m a -> m2:m b -> m3:m c ->
--   {peq (m c) (vseq iMonad m1 (vseq iMonad m2 m3)) (vseq iMonad (vseq iMonad m1 m2) m3)}
-- @-}
-- vseq_associative :: forall m a b c. VMonad m -> m a -> m b -> m c -> PBEq (m c)
-- vseq_associative iMonad m1 m2 m3 =
--   m1 >> (m1 >> m2)
--     ==* _
--     ==* (m1 >> m2) >> m3
--     *** QED
--   where
--     (>>) :: forall a b. m a -> m b -> m b
--     (>>) = vseq iMonad
--     (>>=) :: forall a b. m a -> (a -> m b) -> m b
--     (>>=) = bind iMonad
--     (>=>) = kleisli iMonad

-- TODO: trying to use PBEq (above)
-- -- Lemma. Sequencing is associative.
-- {-@ automatic-instances vseq_associative @-}
-- {-@
-- vseq_associative ::
--   forall m a b c . iMonad:VMonad m -> m1:m a -> m2:m b -> m3:m c ->
--   {IsAssociative (vseq iMonad) m1 m2 m3}
-- @-}
-- vseq_associative :: forall m a b c. VMonad m -> m a -> m b -> m c -> Proof
-- vseq_associative iMonad m1 m2 m3 =
--   m1 >> (m2 >> m3)
--     -- [def] >>
--     ==. m1 >>= vconst (m2 >>= vconst m3)
--     ==. ( m1 >>= (vconst m2 >=> vconst m3)
--             ? extensionality
--               (vconst m2 >=> vconst m3)
--               (vconst (m2 >>= vconst m3))
--               (vseq_associative_lem1_ m2 m3)
--         )
--     -- [def] >=>
--     -- TODO: [err] invalid subtype, but I can't tell why
--     ==. ( (m1 >>= vconst m2) >>= vconst m3
--             ? bind_associative_ m1 (vconst m2) (vconst m3)
--         )
--     -- [def] >>
--     ==! (m1 >> m2) >> m3
--     *** QED
--   where
--     (>>) :: forall a b. m a -> m b -> m b
--     (>>) = vseq iMonad
--     (>>=) :: forall a b. m a -> (a -> m b) -> m b
--     (>>=) = bind iMonad
--     (>=>) = kleisli iMonad
--     bind_associative_ = bind_associative iMonad
--     vseq_associative_lem1_ = vseq_associative_lem1 iMonad

-- {-@ automatic-instances vseq_associative_lem1 @-}
-- {-@
-- vseq_associative_lem1 ::
--   forall m a b c. iMonad:VMonad m -> m2:m b -> m3:m c -> x:a ->
--   {kleisli iMonad (vconst m2) (vconst m3) x ==
--    vconst (bind iMonad m2 (vconst m3)) x}
-- @-}
-- vseq_associative_lem1 ::
--   forall m a b c.
--   VMonad m ->
--   m b ->
--   m c ->
--   a ->
--   Proof
-- vseq_associative_lem1 iMonad m2 m3 x =
--   -- (vconst m2 >=> vconst m3) x
--   (vconst m2 >=> vconst m3) x
--     -- [def] >=>
--     ==. vconst m2 x >>= vconst m3
--     -- [def] vconst
--     ==. m2 >>= vconst m3
--     -- [def] vconst
--     ==. vconst (m2 >>= vconst m3) x
--     *** QED
--   where
--     (>>=) = bind iMonad
--     (>=>) = kleisli iMonad
--     kleisli_ = kleisli iMonad

-- Function.
{-@ reflect vmapM @-}
vmapM :: forall m a b. VMonad m -> (a -> b) -> m a -> m b
vmapM iMonad f m = m >>= liftM_f_ f
  where
    (>>=) = bind iMonad
    liftM_f_ = liftM_f iMonad

vmapM_aux :: forall m a b. VMonad m -> (a -> b) -> a -> m b
vmapM_aux iMonad f x = lift_ (f x)
  where
    lift_ = lift iMonad

-- Function.
{-@ reflect vmapM2 @-}
vmapM2 :: forall m a b c. VMonad m -> (a -> b -> c) -> m a -> m b -> m c
vmapM2 iMonad f ma mb = ma >>= vmapM2_aux1_ f mb
  where
    (>>=) = bind iMonad
    vmapM2_aux1_ = vmapM2_aux1 iMonad

{-@ reflect vmapM2_aux1 @-}
vmapM2_aux1 :: forall m a b c. VMonad m -> (a -> b -> c) -> m b -> a -> m c
vmapM2_aux1 iMonad f mb x = mb >>= vmapM2_aux2_ f x
  where
    lift_ = lift iMonad
    (>>=) = bind iMonad
    vmapM2_aux2_ = vmapM2_aux2 iMonad

{-@ reflect vmapM2_aux2 @-}
vmapM2_aux2 :: forall m a b c. VMonad m -> (a -> b -> c) -> a -> b -> m c
vmapM2_aux2 iMonad f x y = lift_ (f x y)
  where
    lift_ = lift iMonad

-- Predicate. Commutativity for monads.
{-@
predicate IsCommutativeMonadic IMONAD M1 M2 F =
  vmapM2 IMONAD F M1 M2 = vmapM2 IMONAD (vflip F) M2 M1
@-}

{-@ reflect liftM_f @-}
liftM_f :: forall m a b. VMonad m -> (a -> b) -> a -> m b
liftM_f iMonad f x = lift_ (f x)
  where
    lift_ = lift iMonad

-- Function. Lifts tuple into monad, after applying a function to second
-- component.
{-@ reflect liftM_f_second @-}
liftM_f_second ::
  forall m a b c.
  VMonad m ->
  (b -> m c) ->
  (a, b) ->
  m (a, c)
liftM_f_second iMonad f (x, y) = bind_ (f y) (\y' -> lift_ (x, y'))
  where
    lift_ = lift iMonad
    bind_ = bind iMonad
