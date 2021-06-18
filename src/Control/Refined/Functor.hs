module Control.Refined.Functor where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (Functor, map)

{-@
data Functor f = Functor {map :: forall a b. (a -> b) -> (f a -> f b)}
@-}
data Functor f = Functor {map :: forall a b. (a -> b) -> (f a -> f b)}

{-@
class FunctorLaws f where
  map_identity :: fnc:Functor f -> {map fnc identity = identity}
@-}
class FunctorLaws f where
  map_identity :: Functor f -> Proof
