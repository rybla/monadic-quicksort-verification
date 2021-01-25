module VMonad where

import Equality
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.Liquid.ProofCombinators (trivial, (&&&), (==!), (===))
-- hiding (Proof, QED (..), (***), (==.), (?))
import VFunctor
import VUnit
import Prelude hiding ((>>), (>>=))

-- Data Class. A monad is a ...
{-@
data VMonad m = VMonad
  { iFunctor :: VFunctor m
  , vlift :: forall a . a -> m a
  , vbind :: forall a b . m a -> (a -> m b) -> m b
  , vbind_correct :: forall a b . m:m a -> f:(a -> b) ->
      {vbind m (vcomp vlift f) = vmapF iFunctor f m}
  , vbind_identity :: forall a . m:m a ->
      {vbind m vlift = m}
  , vbind_vlift :: forall a b . k:(a -> m b) -> x:a ->
      {vbind (vlift x) k = k x}
  , vbind_associative :: forall a b c . m:m a -> k1:(a -> m b) -> k2:(b -> m c) ->
      {vbind (vbind m k1) k2 = vbind m (raw_kleisli vbind k1 k2)}
  }
  @-}
data VMonad m = VMonad
  { iFunctor :: VFunctor m,
    vlift :: forall a. a -> m a,
    vbind :: forall a b. m a -> (a -> m b) -> m b,
    vbind_correct :: forall a b. m a -> (a -> b) -> Proof,
    vbind_identity :: forall a. m a -> Proof,
    vbind_vlift :: forall a b. (a -> m b) -> a -> Proof,
    vbind_associative :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> Proof
  }

-- Function.
{-@ reflect raw_kleisli @-}
raw_kleisli ::
  forall m a b c.
  (m b -> (b -> m c) -> m c) -> -- vbind
  (a -> m b) ->
  (b -> m c) ->
  (a -> m c)
raw_kleisli (>>=) f g x = f x >>= g

-- Function.
{-@ reflect kleisli @-}
kleisli :: forall m a b c. VMonad m -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisli iMonad = raw_kleisli (>>=)
  where
    (>>=) = vbind iMonad

--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

{-@ measure meq :: VMonad m -> m a -> m a -> Bool @-}

{-@ type MEq m a iMonad m1 m2 = {_:MBEq m a | meq iMonad m1 m2} @-}

{-@
data MBEq :: (* -> *) -> * -> * where
  MBEq_lift :: forall m a. iMonad:VMonad m -> x:a -> y:a -> {pf:Proof | x = y} -> MEq m a iMonad (lift iMonad x) (lift iMonad y)
@-}
data MBEq :: (* -> *) -> * -> * where
  MBEq_lift :: forall m a. VMonad m -> a -> a -> Proof -> MBEq m a

--------------------------------------------------------------------------------
-- Sequencing
--------------------------------------------------------------------------------

-- Function. Monadic sequencing.
{-@ reflect vseq @-}
vseq :: forall m a b. VMonad m -> m a -> m b -> m b
vseq iMonad m1 m2 = m1 >>= vconst m2
  where
    (>>=) = vbind iMonad

-- Term. The unit-monadic identity for monadic sequencing.
{-@ reflect vseq_epsilon @-}
vseq_epsilon :: forall m. VMonad m -> m VUnit
vseq_epsilon iMonad = vlift iMonad ()

-- Lemma.
{-@
vseq_identity_left :: forall m . iMonad:VMonad m -> m:m VUnit ->
  {IsIdentityLeft (vseq iMonad) (vseq_epsilon iMonad) m}
@-}
vseq_identity_left :: forall m. VMonad m -> m VUnit -> Proof
vseq_identity_left iMonad m =
  vseq_epsilon_ >> m
    ==. vlift_ vunit >>= vconst m
    ==. (vconst m vunit ? vbind_vlift_ (vconst m) vunit)
    ==. m
    *** QED
  where
    (>>) = vseq iMonad
    (>>=) = vbind iMonad
    vlift_ = vlift iMonad
    vseq_epsilon_ = vseq_epsilon iMonad
    vbind_vlift_ = vbind_vlift iMonad

-- Lemma.
{-@
vseq_identity_right :: forall m a . iMonad:VMonad m -> m:m VUnit ->
  {IsIdentityRight (vseq iMonad) (vseq_epsilon iMonad) m}
@-}
vseq_identity_right :: forall m. VMonad m -> m VUnit -> Proof
vseq_identity_right iMonad m =
  m >> vseq_epsilon_
    ==. m >>= vconst vseq_epsilon_
    ==. m >>= vconst (vlift_ vunit)
    ==! m -- TODO: prove
    *** QED
  where
    (>>) = vseq iMonad
    vseq_epsilon_ = vseq_epsilon iMonad
    (>>=) = vbind iMonad
    vlift_ = vlift iMonad
    vbind_identity_ = vbind_identity iMonad

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
--     (>>=) = vbind iMonad
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
--             ? vbind_associative_ m1 (vconst m2) (vconst m3)
--         )
--     -- [def] >>
--     ==! (m1 >> m2) >> m3
--     *** QED
--   where
--     (>>) :: forall a b. m a -> m b -> m b
--     (>>) = vseq iMonad
--     (>>=) :: forall a b. m a -> (a -> m b) -> m b
--     (>>=) = vbind iMonad
--     (>=>) = kleisli iMonad
--     vbind_associative_ = vbind_associative iMonad
--     vseq_associative_lem1_ = vseq_associative_lem1 iMonad

-- {-@ automatic-instances vseq_associative_lem1 @-}
-- {-@
-- vseq_associative_lem1 ::
--   forall m a b c. iMonad:VMonad m -> m2:m b -> m3:m c -> x:a ->
--   {kleisli iMonad (vconst m2) (vconst m3) x ==
--    vconst (vbind iMonad m2 (vconst m3)) x}
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
--     (>>=) = vbind iMonad
--     (>=>) = kleisli iMonad
--     kleisli_ = kleisli iMonad

-- Function.
{-@ reflect vmapM @-}
vmapM :: forall m a b. VMonad m -> (a -> b) -> m a -> m b
vmapM iMonad f m = m >>= vliftM_f_ f
  where
    (>>=) = vbind iMonad
    vliftM_f_ = vliftM_f iMonad

vmapM_aux :: forall m a b. VMonad m -> (a -> b) -> a -> m b
vmapM_aux iMonad f x = vlift_ (f x)
  where
    vlift_ = vlift iMonad

-- Function.
{-@ reflect vmapM2 @-}
vmapM2 :: forall m a b c. VMonad m -> (a -> b -> c) -> m a -> m b -> m c
vmapM2 iMonad f ma mb = ma >>= vmapM2_aux1_ f mb
  where
    (>>=) = vbind iMonad
    vmapM2_aux1_ = vmapM2_aux1 iMonad

{-@ reflect vmapM2_aux1 @-}
vmapM2_aux1 :: forall m a b c. VMonad m -> (a -> b -> c) -> m b -> a -> m c
vmapM2_aux1 iMonad f mb x = mb >>= vmapM2_aux2_ f x
  where
    vlift_ = vlift iMonad
    (>>=) = vbind iMonad
    vmapM2_aux2_ = vmapM2_aux2 iMonad

{-@ reflect vmapM2_aux2 @-}
vmapM2_aux2 :: forall m a b c. VMonad m -> (a -> b -> c) -> a -> b -> m c
vmapM2_aux2 iMonad f x y = vlift_ (f x y)
  where
    vlift_ = vlift iMonad

-- Predicate. Commutativity for monads.
{-@
predicate IsCommutativeMonadic IMONAD M1 M2 F =
  vmapM2 IMONAD F M1 M2 = vmapM2 IMONAD (vflip F) M2 M1
@-}

{-@ reflect vliftM_f @-}
vliftM_f :: forall m a b. VMonad m -> (a -> b) -> a -> m b
vliftM_f iMonad f x = vlift_ (f x)
  where
    vlift_ = vlift iMonad

-- Function. Lifts tuple into monad, after applying a function to second
-- component.
{-@ reflect vliftM_f_second @-}
vliftM_f_second ::
  forall m a b c.
  VMonad m ->
  (b -> m c) ->
  (a, b) ->
  m (a, c)
vliftM_f_second iMonad f (x, y) = vbind_ (f y) (\y' -> vlift_ (x, y'))
  where
    vlift_ = vlift iMonad
    vbind_ = vbind iMonad
