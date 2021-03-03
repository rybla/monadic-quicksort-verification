module Control.Monad.Plus.Refined where

import Control.Monad.Refined
import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (Monad, seq)

{-@
data Plus m = Plus
  { monad :: Monad m,
    epsilon :: forall a. m a,
    add :: forall a. m a -> m a -> m a,
    add_identityLeft ::
      forall a.
      m:m a ->
      EqualProp (m a)
        {add epsilon m}
        {m},
    add_associativity ::
      forall a.
      m1:m a ->
      m2:m a ->
      m3:m a ->
      EqualProp (m a)
        {add (add m1 m2) m3}
        {add m1 (add m2 m3)},
    add_distributivity_left ::
      forall a b.
      m1:m a ->
      m2:m a ->
      k:(a -> m b) ->
      EqualProp (m b)
        {bind monad (add m1 m2) k}
        {add (bind monad m1 k) (bind monad m2 k)},
    add_distributivity_right ::
      forall a b.
      m:m a ->
      k1:(a -> m b) ->
      k2:(a -> m b) ->
      EqualProp (m b)
        {bind monad m (\x:a -> add (k1 x) (k2 x))}
        {add (bind monad m k1) (bind monad m k2)},
    bind_zero_left ::
      forall a b.
      k:(a -> m b) ->
      EqualProp (m b)
        {bind monad epsilon k}
        {epsilon},
    bind_zero_right ::
      forall a b.
      m:m a ->
      EqualProp (m b)
        {seq monad m epsilon}
        {epsilon}
  }
@-}
data Plus m = Plus
  { monad :: Monad m,
    epsilon :: forall a. m a,
    add :: forall a. m a -> m a -> m a,
    add_identityLeft ::
      forall a.
      m a ->
      EqualityProp (m a),
    add_associativity ::
      forall a.
      m a ->
      m a ->
      m a ->
      EqualityProp (m a),
    add_distributivity_left ::
      forall a b.
      m a ->
      m a ->
      (a -> m b) ->
      EqualityProp (m b),
    add_distributivity_right ::
      forall a b.
      m a ->
      (a -> m b) ->
      (a -> m b) ->
      EqualityProp (m b),
    bind_zero_left ::
      forall a b.
      (a -> m b) ->
      EqualityProp (m b),
    bind_zero_right ::
      forall a b.
      m a ->
      EqualityProp (m b)
  }

{-@ reflect addF @-}
addF :: Plus m -> (a -> m b) -> (a -> m b) -> (a -> m b)
addF pls k1 k2 x = add pls (k1 x) (k2 x)

{-@ reflect guard @-}
guard :: Plus m -> Bool -> m ()
guard pls b = if b then unit mnd () else epsilon pls
  where
    mnd = monad pls

guardBy :: Plus m -> (a -> Bool) -> a -> m a
guardBy pls p x = seq mnd (guard pls (p x)) (unit mnd x)
  where
    mnd = monad pls
