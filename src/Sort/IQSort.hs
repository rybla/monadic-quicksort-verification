-- {-@ LIQUID "--compile-spec" @-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Sort.IQSort where

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
import Sort.IPartl
import Sort.List
import Prelude hiding (all, foldl, length, pure, read, readList, seq)

--
-- # IQSort (in-place quicksort)
--

--
-- ## Functions
--

--
-- iqsort
--

-- `iqsort i n` sorts the `n` elements in the array starting from index `i`.
{-@ lazy iqsort @-}
{-@ reflect iqsort @-}
iqsort :: Natural -> Natural -> M ()
iqsort i Z = pure ()
iqsort i (S n) =
  bind
    (read i)
    (iqsort_aux1 i n)

{-@ lazy iqsort_aux1 @-}
{-@ reflect iqsort_aux1 @-}
iqsort_aux1 :: Natural -> Natural -> Int -> M ()
iqsort_aux1 i n p =
  bind
    (ipartl (S i) p (Z, Z, n))
    (iqsort_aux2 i n)

{-@ lazy iqsort_aux2 @-}
{-@ reflect iqsort_aux2 @-}
iqsort_aux2 :: Natural -> Natural -> (Natural, Natural) -> M ()
iqsort_aux2 i n (ny, nz) =
  seq
    ( seq
        (swap i (add i ny))
        (iqsort i ny)
    )
    (iqsort (S (add i ny)) nz)

--
-- ## Proofs
--

--
-- iqsort_spec steps
--

-- iqsort_spec_step1

{-@ reflect iqsort_spec_step1 @-}
iqsort_spec_step1 :: Natural -> Int -> List Int -> M ()
iqsort_spec_step1 i p xs =
  bind
    ( seq
        (writeList i (Cons p xs))
        (ipartl (S i) p (Z, Z, length xs))
    )
    (iqsort_spec_step1_aux i)

{-@ reflect iqsort_spec_step1_aux @-}
iqsort_spec_step1_aux :: Natural -> (Natural, Natural) -> M ()
iqsort_spec_step1_aux i (ny, nz) =
  seq
    ( seq
        (swap i (add i ny))
        (iqsort i ny)
    )
    (iqsort (S (add i ny)) nz)

-- iqsort_spec_step2

{-@ reflect iqsort_spec_step2 @-}
iqsort_spec_step2 :: Natural -> Int -> List Int -> M ()
iqsort_spec_step2 i p xs =
  bind
    (partl' p (Nil, Nil, xs))
    (iqsort_spec_step2_aux i p)

{-@ reflect iqsort_spec_step2_aux @-}
iqsort_spec_step2_aux :: Natural -> Int -> (List Int, List Int) -> M ()
iqsort_spec_step2_aux i p (ys, zs) =
  bind
    (permute ys)
    (iqsort_spec_step2_aux_aux i p ys zs)

{-@ reflect iqsort_spec_step2_aux_aux @-}
iqsort_spec_step2_aux_aux :: Natural -> Int -> List Int -> List Int -> List Int -> M ()
iqsort_spec_step2_aux_aux i p ys zs ys' =
  seq
    ( seq
        (writeList i (sandwich ys' p zs))
        (iqsort i (length ys))
    )
    (iqsort (S (add i (length ys))) (length zs))

-- iqsort_spec_step3

{-@ reflect iqsort_spec_step3 @-}
iqsort_spec_step3 :: Natural -> Int -> List Int -> M ()
iqsort_spec_step3 i p xs = iqsort_spec_aux2 i (Cons p xs)

--
-- iqsort_spec_lemma1 : 2 refines 3
--

-- iqsort_spec_lemma1

{-@
iqsort_spec_lemma1 ::
  i:Natural -> p:Int -> xs:List Int ->
  RefinesPlus (())
    {iqsort_spec_step2 i p xs}
    {iqsort_spec_step3 i p xs}
@-}
iqsort_spec_lemma1 :: Natural -> Int -> List Int -> EqualityProp (M ())
iqsort_spec_lemma1 i p xs = undefined -- TODO

--
-- iqsort_spec_lemma2 (used in iqsort_spec_lemma3)
--

-- iqsort_spec_lemma2_aux1

{-@ reflect iqsort_spec_lemma2_aux1 @-}
iqsort_spec_lemma2_aux1 :: Natural -> Int -> List Int -> M ()
iqsort_spec_lemma2_aux1 i p ys =
  seq
    (writeList i (Cons p ys))
    (swap i (add i (length ys)))

-- iqsort_spec_lemma2_aux2

{-@ reflect iqsort_spec_lemma2_aux2 @-}
iqsort_spec_lemma2_aux2 :: Natural -> Int -> List Int -> M ()
iqsort_spec_lemma2_aux2 i p ys =
  bind
    (permute ys)
    (iqsort_spec_lemma2_aux2_aux i p)

{-@ reflect iqsort_spec_lemma2_aux2_aux @-}
iqsort_spec_lemma2_aux2_aux :: Natural -> Int -> List Int -> M ()
iqsort_spec_lemma2_aux2_aux i p ys' =
  writeList i (snoc ys' p)

-- iqsort_spec_lemma2

-- [ref 13]
{-@
iqsort_spec_lemma2 ::
  i:Natural -> p:Int -> ys:List Int ->
  RefinesPlus (())
    {iqsort_spec_lemma2_aux1 i p ys}
    {iqsort_spec_lemma2_aux2 i p ys}
@-}
iqsort_spec_lemma2 :: Natural -> Int -> List Int -> EqualityProp (M ())
iqsort_spec_lemma2 = undefined -- TODO

--
-- iqsort_spec_lemma3
--

-- iqsort_spec_lemma3 : 1 refines 2

{-@
iqsort_spec_lemma3 ::
  i:Natural -> p:Int -> xs:List Int ->
  RefinesPlus (())
    {iqsort_spec_step1 i p xs}
    {iqsort_spec_step2 i p xs}
@-}
iqsort_spec_lemma3 :: Natural -> Int -> List Int -> EqualityProp (M ())
iqsort_spec_lemma3 i p xs = undefined -- TODO

--
-- iqsort_spec
--

{-@ reflect iqsort_spec_aux1 @-}
iqsort_spec_aux1 :: Natural -> List Int -> M ()
iqsort_spec_aux1 i xs =
  seq
    (writeList i xs)
    (iqsort i (length xs))

{-@ reflect iqsort_spec_aux2 @-}
iqsort_spec_aux2 :: Natural -> List Int -> M ()
iqsort_spec_aux2 i xs =
  bind
    (slowsort xs)
    (writeList i)

-- from [ref 12]
{-@
iqsort_spec ::
  Equality (M ()) =>
  i:Natural -> xs:List Int ->
  RefinesPlus (())
    {iqsort_spec_aux1 i xs}
    {iqsort_spec_aux2 i xs}
@-}
iqsort_spec :: Equality (M ()) => Natural -> List Int -> EqualityProp (M ())
iqsort_spec i Nil = undefined -- TODO: easy (look at def of iqsort)
iqsort_spec i (Cons p xs) =
  refinesplus_transitivity (iqsort_spec_aux1 i (Cons p xs)) (iqsort_spec_step1 i p xs) (iqsort_spec_aux2 i (Cons p xs)) (iqsort_spec_lemma4 i p xs) $
    refinesplus_transitivity (iqsort_spec_step1 i p xs) (iqsort_spec_step2 i p xs) (iqsort_spec_aux2 i (Cons p xs)) (iqsort_spec_lemma3 i p xs) $
      refinesplus_transitivity (iqsort_spec_step2 i p xs) (iqsort_spec_step3 i p xs) (iqsort_spec_aux2 i (Cons p xs)) (iqsort_spec_lemma1 i p xs) (iqsort_spec_lemma0 i p xs)

{-@
iqsort_spec_lemma4 ::
  i:Natural -> p:Int -> xs:List Int ->
  RefinesPlus (())
    {iqsort_spec_aux1 i (Cons p xs)}
    {iqsort_spec_step1 i p xs}
@-}
iqsort_spec_lemma4 :: Natural -> Int -> List Int -> EqualityProp (M ())
iqsort_spec_lemma4 i p xs = undefined --TODO

{-@
iqsort_spec_lemma0 ::
  i:Natural -> p:Int -> xs:List Int ->
  RefinesPlus (())
    {iqsort_spec_step3 i p xs}
    {iqsort_spec_aux2 i (Cons p xs)}
@-}
iqsort_spec_lemma0 :: Natural -> Int -> List Int -> EqualityProp (M ())
iqsort_spec_lemma0 i p xs = undefined -- TODO
