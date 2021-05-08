{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Sort.ArrayOld where

import Control.Refined.Monad
import Control.Refined.Monad.Array hiding (monad)
import Control.Refined.Monad.ArrayPlus
import Control.Refined.Monad.Plus hiding (monad)
import Data.Refined.Bool
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Tuple
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Sort.List
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (*), (+), (++), (>>), (>>=))

{-
TODO: how much of the derivation do I need to verify?
or can i just verify the final result and that's fine?
-}

{-
non-tailrecursive version of partl

partl :: Elem -> (List Elem, List Elem, List Elem) -> (List Elem, List Elem)
partl p (ys, zs, xs) = (ys ++ us, zs ++ vs)
  where
    us = proj1 (partition p xs)
    vs = proj2 (partition p xs)

-}

-- -- tail-recurisve version of partl
-- {-@ reflect partl @-}
-- partl :: Elem -> (List Elem, List Elem, List Elem) -> (List Elem, List Elem)
-- partl p (ys, zs, Nil) = (ys, zs)
-- partl p (ys, zs, Cons x xs) =
--   if leq x p
--     then partl p (ys ++ Cons x Nil, zs, xs)
--     else partl p (ys, zs ++ Cons x Nil, xs)

-- {-@ reflect ipartl_spec1_aux1 @-}
-- ipartl_spec1_aux1 :: ArrayPlus m Elem -> Elem -> Index -> List Elem -> List Elem -> List Elem -> m (Natural, Natural)
-- ipartl_spec1_aux1 arp p i xs ys zs = writeList arr i (ys ++ zs ++ xs) >> ipartl arp p i (length ys, length zs, length xs)
--   where
--     (>>) = seq mnd
--     arr = array arp
--     pls = plusm arp
--     mnd = monad arp

-- {-@ reflect ipartl_spec1_aux2 @-}
-- ipartl_spec1_aux2 :: ArrayPlus m Elem -> Elem -> Index -> List Elem -> List Elem -> List Elem -> m (Natural, Natural)
-- ipartl_spec1_aux2 arp p i xs ys zs = second mnd (permute pls) (partl p (ys, zs, xs)) >>= writeListToLength2 arr i
--   where
--     (>>=) = bind mnd
--     arr = array arp
--     pls = plusm arp
--     mnd = monad arp

-- {-@
-- ipartl_spec1 ::
--   Monad m ->
--   Array m a ->
--   Plus m ->
--   arp:ArrayPlus m Elem ->
--   p:Elem ->
--   i:Index ->
--   xs:List Elem ->
--   ys:List Elem ->
--   zs:List Elem ->
--   RefinesPlus m (Natural, Natural) {plusm arp}
--     {ipartl_spec1_aux1 arp p i xs ys zs}
--     {ipartl_spec1_aux2 arp p i xs ys zs}
-- @-}
-- ipartl_spec1 :: Monad m -> Array m a -> Plus m -> ArrayPlus m Elem -> Elem -> Index -> List Elem -> List Elem -> List Elem -> EqualityProp (m (Natural, Natural))
-- ipartl_spec1 _ _ _ arp p i xs ys zs = undefined
--   where
--     (>>=) = bind mnd
--     arr = array arp
--     pls = plusm arp
--     mnd = monad arp

-- {-@ reflect ipartl @-}
-- ipartl :: forall m. ArrayPlus m Elem -> Elem -> Index -> (Natural, Natural, Natural) -> m (Natural, Natural)
-- ipartl arp p i (ny, nz, Z) = pure mnd (ny, nz)
--   where
--     mnd = monad arp
-- ipartl arp p i (ny, nz, S k) =
--   read arr (i + ny + nz)
--     >>= apply
--       ( \x ->
--           if leq x p
--             then swap arr (i + ny) (i + ny + nz) >> ipartl arp p i (S ny, nz, k)
--             else ipartl arp p i (ny, S nz, k)
--       )
--   where
--     (>>=) :: forall a b. m a -> (a -> m b) -> m b
--     (>>=) = bind mnd
--     (>>) :: forall a b. m a -> m b -> m b
--     (>>) = seq mnd
--     arr = array arp
--     pls = plusm arp
--     mnd = monad arp
