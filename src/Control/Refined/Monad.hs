{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Control.Refined.Monad where

import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Prelude hiding (Monad, pure, seq, (>>), (>>=))

{-
# Monad
-}

{-
## Data
-}

{-@
data Monad m = Monad
  { pure :: forall a. a -> m a,
    bind :: forall a b. m a -> (a -> m b) -> m b,
    pure_bind ::
      forall a b.
      x:a ->
      k:(a -> m b) ->
      EqualProp (m b)
        {bind (pure x) k}
        {k x},
    bind_identity_right ::
      forall a.
      m:m a ->
      EqualProp (m a)
        {bind m pure}
        {m},
    bind_associativity ::
      forall a b c.
      m:m a ->
      k1:(a -> m b) ->
      k2:(b -> m c) ->
      EqualProp (m c) {bind (bind m k1) k2} {bind m (bind_associativity_aux bind k1 k2)}
  }
@-}
data Monad m = Monad
  { pure :: forall a. a -> m a,
    bind :: forall a b. m a -> (a -> m b) -> m b,
    pure_bind ::
      forall a b.
      a ->
      (a -> m b) ->
      EqualityProp (m b),
    bind_identity_right ::
      forall a.
      m a ->
      EqualityProp (m a),
    bind_associativity ::
      forall a b c.
      m a ->
      (a -> m b) ->
      (b -> m c) ->
      EqualityProp (m c)
  }

{-@ reflect bind_associativity_aux @-}
bind_associativity_aux :: (m b -> (b -> m c) -> m c) -> (a -> m b) -> (b -> m c) -> a -> m c
bind_associativity_aux bind k1 k2 x = bind (k1 x) k2

{-
## Utilities
-}

{-@ reflect kleisli @-}
kleisli :: Monad m -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisli mnd k1 k2 x = bind mnd (k1 x) k2

{-@ reflect join @-}
join :: Monad m -> m (m a) -> m a
join mnd mm = bind mnd mm identity

{-@ reflect seq @-}
seq :: Monad m -> m a -> m b -> m b
seq mnd ma mb = bind mnd ma (apply (\_ -> mb))

{-@ reflect liftM @-}
liftM :: Monad m -> (a -> b) -> (m a -> m b)
liftM mnd f m = bind mnd m (apply (\x -> pure mnd (f x)))

{-@ reflect liftM2 @-}
liftM2 :: forall m a b c. Monad m -> (a -> b -> c) -> (m a -> m b -> m c)
liftM2 mnd f ma mb =
  ma >>= (apply (\x -> mb >>= apply (\y -> pure mnd (f x y))))
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd

{-@ reflect second @-}
second :: forall m a b c. Monad m -> (b -> m c) -> (a, b) -> m (a, c)
second mnd k (x, y) = k y >>= apply (\y' -> pure mnd (x, y'))
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd

{-
## Properties
-}

{-@
seq_associativity ::
  Transitivity (m c) =>
  mnd:Monad m ->
  ma:m a ->
  mb:m b ->
  mc:m c ->
  EqualProp (m c)
    {seq mnd (seq mnd ma mb) mc}
    {seq mnd ma (seq mnd mb mc)}
@-}
seq_associativity ::
  Transitivity (m c) =>
  Monad m ->
  m a ->
  m b ->
  m c ->
  EqualityProp (m c)
seq_associativity mnd ma mb mc =
  [eqpropchain|
      seq mnd (seq mnd ma mb) mc
    %==
      seq mnd (bind mnd ma (apply (\_ -> mb))) mc
        %by %smt 
        %by seq mnd ma mb 
    %==
      bind mnd (bind mnd ma (apply (\_ -> mb))) (apply (\_ -> mc))
        %by %smt 
        %by seq mnd (bind mnd ma (apply (\_ -> mb))) mc
    %==
      bind mnd ma (apply (\x -> bind mnd (apply (\_ -> mb) x) (apply (\_ -> mc))))
        %by undefined -- bind_associativity mnd ma (apply (\_ -> mb)) (apply (\_ -> mc))
        %-- TODO: why doesn't this step work?
    %==
      bind mnd ma (apply (\x -> bind mnd mb (apply (\_ -> mc))))
        %by %rewrite apply (\x -> bind mnd (apply (\_ -> mb) x) (apply (\_ -> mc)))
                 %to apply (\x -> bind mnd mb (apply (\_ -> mc)))
        %by %extend x 
        %by %reflexivity
    %==
      bind mnd ma (apply (\x -> seq mnd mb mc))
        %by %rewrite apply (\x -> bind mnd mb (apply (\_ -> mc)))
                 %to apply (\x -> seq mnd mb mc)
        %by %extend x
        %by %smt
        %by seq mnd mb mc
    %==
      seq mnd ma (seq mnd mb mc)
        %by %smt 
        %by seq mnd ma (seq mnd mb mc)
  |]
  where
    (>>) = seq mnd
    (>>=) = bind mnd

{-@
seq_identity_left ::
  Equality (m b) =>
  mnd:Monad m ->
  x:a ->
  m:m b ->
  EqualProp (m b)
    {seq mnd (pure mnd x) m}
    {m}
@-}
seq_identity_left ::
  Equality (m b) =>
  Monad m ->
  a ->
  m b ->
  EqualityProp (m b)
seq_identity_left mnd x m =
  [eqpropchain|
      seq mnd (pure mnd x) m
    %== 
      bind mnd (pure mnd x) (apply (\_ -> m))
        %by %smt 
        %by undefined -- TODO: why not `seq mnd (pure mnd ()) m`?
    %==
      apply (\_ -> m) ()
        %by pure_bind mnd (pure mnd x) (apply (\_ -> m))
    %== 
      m
  |]

{-
{-@
seq_identity_right ::
  Equality (m b) =>
  mnd:Monad m ->
  m:m a ->
  x:b ->
  EqualProp (m b)
    {seq mnd m (pure mnd x)}
    {x}
@-}
seq_identity_right ::
  Equality (m b) =>
  Monad m ->
  m a ->
  b ->
  EqualityProp (m b)
seq_identity_right mnd m x =
  [eqpropchain|
      seq mnd m (pure mnd x)
    %==
      bind mnd m (apply (\_ -> pure mnd x))
        %by %smt
        %by undefined
    %==
      bind mnd m (pure mnd x)
        %by %rewrite apply (\_ -> pure mnd x)
            %to pure mnd x
        %by %extend y
        %by apply (\_ -> pure mnd x) y
    %==

  |]
-}

{-@
kleisli_associativity ::
  forall m a b c d.
  Equality (a -> m d) =>
  mnd:Monad m ->
  k1:(a -> m b) ->
  k2:(b -> m c) ->
  k3:(c -> m d) ->
  EqualProp (a -> m d)
    {kleisli mnd (kleisli mnd k1 k2) k3}
    {kleisli mnd k1 (kleisli mnd k2 k3)}
@-}
kleisli_associativity :: forall m a b c d. Equality (a -> m d) => Monad m -> (a -> m b) -> (b -> m c) -> (c -> m d) -> EqualityProp (a -> m d)
kleisli_associativity mnd k1 k2 k3 =
  [eqpropchain|
      (k1 >=> k2) >=> k3
    %==
      apply (\ma -> ((k1 >=> k2) >=> k3) ma)
        %by %extend ma
        %by %reflexivity
    %==
      apply (\ma -> (k1 >=> k2) ma >>= k3)
        %by undefined
        %{-
        -- TODO: there is a problem with extensionally manipulating
        -- expressions inside lambdas
        
        %by %extend ma
        %by %rewrite ((k1 >=> k2) >=> k3) ma
                 %to (k1 >=> k2) ma >>= k3
        %by %smt 
        %by apply (\ma -> apply (\a -> (k1 >=> k2) a >>= k3) ma) ma
        -}%
    %==
      k1 >=> (k2 >=> k3)
        %by undefined
  |]
  where
    (>>) :: forall a. m a -> m a -> m a
    (>>) = seq mnd
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>=>) :: forall a b c. (a -> m b) -> (b -> m c) -> (a -> m c)
    (>=>) = kleisli mnd

{-
## Monadic Commutativity
-}

{-
Commutativity of monadic terms. m1 commutes with m2 iff
  m1 >>= \x -> m2 >>= \y -> k x y
    =
  m2 >>= \y -> m1 >>= \x -> k x y
-}
{-@
type CommutesM m a b c Mnd M1 M2 K =
        EqualProp (m c)
          {bind Mnd M1 (apply (\x:a -> bind Mnd M2 (apply (\y:b -> K Mnd x y))))}
          {bind Mnd M2 (apply (\y:b -> bind Mnd M1 (apply (\x:a -> K Mnd x y))))}
@-}
