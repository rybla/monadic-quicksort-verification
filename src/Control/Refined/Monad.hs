module Control.Refined.Monad where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (Monad, pure, seq)

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
    kleisli :: forall a b c. (a -> m b) -> (b -> m c) -> (a -> m c),
    kleisli_correct ::
      forall a b c.
      k1:(a -> m b) ->
      k2:(b -> m c) ->
      x:a ->
      EqualProp (m c)
        {kleisli k1 k2 x}
        {bind (k1 x) k2},
    bind_identity_left ::
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
      EqualProp (m c)
        {bind (bind m k1) k2}
        {bind m (kleisli k1 k2)}
  }
@-}
data Monad m = Monad
  { pure :: forall a. a -> m a,
    bind :: forall a b. m a -> (a -> m b) -> m b,
    kleisli :: forall a b c. (a -> m b) -> (b -> m c) -> (a -> m c),
    kleisli_correct ::
      forall a b c.
      (a -> m b) ->
      (b -> m c) ->
      a ->
      EqualityProp (m c),
    bind_identity_left ::
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

{-
## Utilities
-}

{-@ reflect join @-}
join :: Monad m -> m (m a) -> m a
join mnd mm = bind mnd mm identity

{-@ reflect seq @-}
seq :: Monad m -> m a -> m b -> m b
seq mnd ma mb = bind mnd ma (\_ -> mb)

{-@ reflect map @-}
map :: Monad m -> (a -> b) -> (m a -> m b)
map mnd f m = bind mnd m (\x -> pure mnd (f x))

{-@ reflect map2 @-}
map2 :: Monad m -> (a -> b -> c) -> (m a -> m b -> m c)
map2 mnd f ma mb = bind mnd ma (\x -> bind mnd mb (\y -> pure mnd (f x y)))

{-
## Properties
-}
{-@
seq_associativity ::
  mnd:Monad m ->
  ma:m a ->
  mb:m b ->
  mc:m c ->
  EqualProp (m c)
    {seq mnd (seq mnd ma mb) mc}
    {seq mnd ma (seq mnd mb mc)}
@-}
seq_associativity ::
  Monad m ->
  m a ->
  m b ->
  m c ->
  EqualityProp (m c)
seq_associativity mnd ma mb mc = undefined -- TODO
