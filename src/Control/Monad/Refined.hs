module Control.Monad.Refined where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (Monad, seq)

{-
# Monad
-}

{-@
data Monad m = Monad
  { unit :: forall a. a -> m a,
    bind :: forall a b. m a -> (a -> m b) -> m b,
    identityLeft ::
      forall a b.
      (y:b -> EqualProp b {y} {y}) ->
      x:a ->
      k:(a -> m b) ->
      EqualProp (m b) {bind (unit x) k} {k x},
    identityRight ::
      forall a.
      (x:a -> EqualProp a {x} {x}) ->
      m:m a ->
      EqualProp (m a) {bind m unit} {m},
    associativity ::
      forall a b c.
      (x:c -> EqualProp c {x} {x}) ->
      (x:c -> y:c -> z:c -> EqualProp c {x} {y} -> EqualProp c {y} {z} -> EqualProp c {x} {z}) ->
      m:m a ->
      k1:(a -> m b) ->
      k2:(b -> m c) ->
      EqualProp (m c) {bind (bind m k1) k2} {bind m (\x:a -> bind (k1 x) k2)}
  }
@-}
data Monad m = Monad
  { unit :: forall a. a -> m a,
    bind :: forall a b. m a -> (a -> m b) -> m b,
    identityLeft ::
      forall a b.
      (b -> EqualityProp b) ->
      a ->
      (a -> m b) ->
      EqualityProp (m b),
    identityRight ::
      forall a.
      (a -> EqualityProp a) ->
      m a ->
      EqualityProp (m a),
    associativity ::
      forall a b c.
      (c -> EqualityProp c) ->
      (c -> c -> c -> EqualityProp c -> EqualityProp c -> EqualityProp c) ->
      m a ->
      (a -> m b) ->
      (b -> m c) ->
      EqualityProp (m c)
  }

{-@ reflect kleisli @-}
kleisli :: Monad m -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisli mnd k1 k2 x = bind mnd (k1 x) k2

{-@ reflect seq @-}
seq :: Monad m -> m a -> m b -> m b
seq mnd ma mb = bind mnd ma (\_ -> mb)
