{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Sort.Array where

import Data.Refined.Bool
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Tuple
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.TH.Syntax
import Placeholder.M
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Sort.List
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (*), (+), (++), (>>), (>>=))

{-
## Functions. `ipartl` and relatives

-}

{-@ reflect partl' @-}
partl' :: Int -> (List Int, List Int, List Int) -> M (List Int, List Int)
partl' p (ys, zs, Nil) = pure (ys, zs)
partl' p (ys, zs, Cons x xs) = dispatch x p (ys, zs, xs) >>= partl' p

{-@ reflect dispatch @-}
dispatch :: Int -> Int -> (List Int, List Int, List Int) -> M (List Int, List Int, List Int)
dispatch x p (ys, zs, xs) =
  if leq x p
    then permute zs >>= \zs' -> pure (ys ++ Cons x Nil, zs', xs)
    else permute (zs ++ Cons x Nil) >>= \zs' -> pure (ys, zs', xs)

-- final derivation of `ipartl`
{-@ reflect ipartl @-}
ipartl :: Int -> Natural -> (Natural, Natural, Natural) -> M (Natural, Natural)
ipartl p i (ny, nz, Z) = pure (ny, nz)
ipartl p i (ny, nz, S k) =
  read (i + ny + nz) >>= \x ->
    if leq x p
      then swap (i + ny) (i + ny + nz) >> ipartl p i (S ny, nz, k)
      else ipartl p i (ny, S nz, k)

{-
## Theorem. `ipartl_spec`

-}

{-@ reflect ipartl_spec_aux1 @-}
ipartl_spec_aux1 :: Int -> Natural -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_aux1 p i xs ys zs = writeList i (ys ++ zs ++ xs) >> ipartl p i (length ys, length zs, length xs)

{-@ reflect ipartl_spec_aux2 @-}
ipartl_spec_aux2 :: Int -> Natural -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_aux2 p i xs ys zs = partl' p (ys, zs, xs) >>= writeListToLength2 i

-- [ref] display 10
{-@
ipartl_spec ::
  Equality (M (Natural, Natural)) =>
  p:Int ->
  i:Natural ->
  xs:List Int ->
  ys:List Int ->
  zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_aux1 p i xs ys zs}
    {ipartl_spec_aux2 p i xs ys zs}
@-}
ipartl_spec :: Equality (M (Natural, Natural)) => Int -> Natural -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec p i xs ys zs =
  [eqpropchain|
      (writeList i (ys ++ zs ++ xs) >> ipartl p i (length ys, length zs, length xs))
        <+> (partl' p (ys, zs, xs) >>= writeListToLength2 i)
    %==
      partl' p (ys, zs, xs) >>= writeListToLength2 i
        %by undefined 
  |]

{-@ reflect ipartl_spec_lemma_aux1 @-}
ipartl_spec_lemma_aux1 :: Natural -> Int -> List Int -> M ()
ipartl_spec_lemma_aux1 i x zs =
  writeList i (zs ++ Cons x Nil) >> swap i (i + length zs)

{-@ reflect ipartl_spec_lemma_aux2 @-}
ipartl_spec_lemma_aux2 :: Natural -> Int -> List Int -> M ()
ipartl_spec_lemma_aux2 i x zs =
  permute zs >>= \zs' -> writeList i (Cons x Nil ++ zs')

-- [ref] display 11
-- TODO: do they give a proof of this somewhere?
{-@
ipartl_spec_lemma ::
  Equality (M Unit) =>
  i:Natural ->
  x:Int ->
  zs:List Int ->
  RefinesPlus Unit {ipartl_spec_lemma_aux1 i x zs} {ipartl_spec_lemma_aux2 i x zs}
@-}
ipartl_spec_lemma :: Equality (M ()) => Natural -> Int -> List Int -> EqualityProp (M ())
ipartl_spec_lemma i x zs =
  [eqpropchain|
      (writeList i (zs ++ Cons x Nil) >> swap i (i + length zs))
        <+> (permute zs >>= \zs' -> writeList i (Cons x Nil ++ zs'))
    %==
      permute zs >>= \zs' -> writeList i (Cons x Nil ++ zs')
        %by undefined -- TODO 
  |]

{-
## Functions. `iqsort` and relatives

-}

-- `iqsort i n` sorts the `n` elements in the array starting from index `i`.
-- TODO: need to prove termination?
{-@ lazy iqsort @-}
{-@ reflect iqsort @-}
iqsort :: Natural -> Natural -> M ()
iqsort i Z = pure ()
iqsort i (S n) =
  read i >>= \p ->
    ipartl p (S i) (Z, Z, n) >>= \(ny, nz) ->
      swap i (i + ny)
        >> iqsort i ny
        >> iqsort (S (i + ny)) nz
