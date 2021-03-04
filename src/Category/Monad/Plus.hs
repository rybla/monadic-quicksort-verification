module Category.Monad.Plus where

import Category.Monad
import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (Monad, pure, seq)

{-
# Plus monad
-}

{-
## Data
-}

{-@
data Plus m = Plus
  { monad :: Monad m,
    epsilon :: forall a. m a,
    addm :: forall a. m a -> m a -> m a,
    addm_identityLeft ::
      forall a.
      m:m a ->
      EqualProp (m a)
        {addm epsilon m}
        {m},
    addm_associativity ::
      forall a.
      m1:m a ->
      m2:m a ->
      m3:m a ->
      EqualProp (m a)
        {addm (addm m1 m2) m3}
        {addm m1 (addm m2 m3)},
    addm_distributivity_left ::
      forall a b.
      m1:m a ->
      m2:m a ->
      k:(a -> m b) ->
      EqualProp (m b)
        {bind monad (addm m1 m2) k}
        {addm (bind monad m1 k) (bind monad m2 k)},
    addm_distributivity_right ::
      forall a b.
      m:m a ->
      k1:(a -> m b) ->
      k2:(a -> m b) ->
      EqualProp (m b)
        {bind monad m (\x:a -> addm (k1 x) (k2 x))}
        {addm (bind monad m k1) (bind monad m k2)},
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
    addm :: forall a. m a -> m a -> m a,
    addm_identityLeft ::
      forall a.
      m a ->
      EqualityProp (m a),
    addm_associativity ::
      forall a.
      m a ->
      m a ->
      m a ->
      EqualityProp (m a),
    addm_distributivity_left ::
      forall a b.
      m a ->
      m a ->
      (a -> m b) ->
      EqualityProp (m b),
    addm_distributivity_right ::
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

{-
## Utilities
-}

{-@ reflect addmF @-}
addmF :: Plus m -> (a -> m b) -> (a -> m b) -> (a -> m b)
addmF pls k1 k2 x = addm pls (k1 x) (k2 x)

{-@ reflect guard @-}
guard :: Plus m -> Bool -> m ()
guard pls b = if b then pure mnd () else epsilon pls
  where
    mnd = monad pls

guardBy :: Plus m -> (a -> Bool) -> a -> m a
guardBy pls p x = seq mnd (guard pls (p x)) (pure mnd x)
  where
    mnd = monad pls
