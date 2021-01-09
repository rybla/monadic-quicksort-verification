module QuickSortArray where

import Function
import Liquid.ProofCombinators
import qualified QuickSortList as QSL
import Relation
import VList
import VMonad
import VMonadArray
import VMonadPlus
import VOrdered

--------------------------------------------------------------------------------
-- Quick Sort
--------------------------------------------------------------------------------

-- TODO

--------------------------------------------------------------------------------
-- Partitioning
--------------------------------------------------------------------------------

-- Function. Tail-recursive partition.
{-@ reflect partition @-}
partition ::
  forall a.
  VOrdered a ->
  a ->
  (VList a, VList a) ->
  VList a ->
  (VList a, VList a)
partition iOrdered p (ys, zs) Nil = (ys, zs)
partition iOrdered p (ys, zs) (Cons x xs) =
  if leq_ x p
    then partition_ p (vappend ys (vsingleton x), zs) xs
    else partition_ p (ys, vappend zs (vsingleton x)) xs
  where
    partition_ = partition iOrdered
    leq_ = leq iOrdered