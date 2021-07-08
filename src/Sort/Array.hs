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
import Prelude hiding (all, foldl, length, pure, read, readList, seq)

--
-- # Functions
--

-- {-@ reflect partl @-}
-- partl :: Int -> (List Int, List Int, List Int) -> (List Int, List Int)
-- partl p (ys, zs, xs) =
--   let (us, vs) = partition p xs
--    in (append ys us, append zs vs)

-- partl

{-@ reflect partl @-}
partl :: Int -> (List Int, List Int, List Int) -> (List Int, List Int)
partl p (ys, zs, Nil) = (ys, zs)
partl p (ys, zs, Cons x xs) =
  if leq x p
    then partl p (append ys (single x), zs, xs)
    else partl p (ys, append zs (single x), xs)

-- partl'

{-@ reflect partl' @-}
partl' :: Int -> (List Int, List Int, List Int) -> M (List Int, List Int)
partl' p (ys, zs, Nil) = pure (ys, zs)
partl' p (ys, zs, Cons x xs) = bind (dispatch x p (ys, zs, xs)) (partl' p)

{-@ reflect dispatch @-}
dispatch :: Int -> Int -> (List Int, List Int, List Int) -> M (List Int, List Int, List Int)
dispatch x p (ys, zs, xs) =
  if leq x p
    then bind (permute zs) (dispatch_aux1 x xs ys)
    else bind (permute (snoc zs x)) (dispatch_aux2 xs ys)

{-@ reflect dispatch_aux1 @-}
dispatch_aux1 :: Int -> List Int -> List Int -> List Int -> M (List Int, List Int, List Int)
dispatch_aux1 x xs ys zs' = pure (snoc ys x, zs', xs)

{-@ reflect dispatch_aux2 @-}
dispatch_aux2 :: List Int -> List Int -> List Int -> M (List Int, List Int, List Int)
dispatch_aux2 xs ys zs' = pure (ys, zs', xs)

-- ipartl

{-@ reflect ipartl @-}
ipartl :: Int -> Natural -> (Natural, Natural, Natural) -> M (Natural, Natural)
ipartl p i (ny, nz, Z) = pure (ny, nz)
ipartl p i (ny, nz, S k) =
  bind (read (add (add i ny) nz)) (ipartl_aux p i ny nz k)

{-@ reflect ipartl_aux @-}
ipartl_aux :: Int -> Natural -> Natural -> Natural -> Natural -> Int -> M (Natural, Natural)
ipartl_aux p i ny nz k x' =
  if leq x' p
    then
      seq
        (swap (add i ny) (add (add i ny) nz))
        (ipartl p i (S ny, nz, k))
    else ipartl p i (ny, S nz, k)

--
-- ipartl_spec
--

{-@ reflect ipartl_spec_aux1 @-}
ipartl_spec_aux1 :: Int -> Natural -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_aux1 p i xs ys zs = seq (writeList i (append (append ys zs) xs)) (ipartl p i (length ys, length zs, length xs))

{-@ reflect ipartl_spec_aux2 @-}
ipartl_spec_aux2 :: Int -> Natural -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_aux2 p i xs ys zs = bind (second permute (partl p (ys, zs, xs))) (writeListToLength2 i)

{-@
ipartl_spec ::
  p:Int -> i:Natural -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_aux1 p i xs ys zs}
    {ipartl_spec_aux2 p i xs ys zs}
@-}
ipartl_spec :: Int -> Natural -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec p i xs ys zs = undefined

--
-- ipartl_spec_lemma10
--

-- ipartl_spec_lemma10_aux1

{-@ reflect ipartl_spec_lemma10_aux1 @-}
ipartl_spec_lemma10_aux1 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma10_aux1 p i x xs ys zs =
  seq
    (writeList (add (add (add i (length ys)) (length zs)) one) xs)
    ( if leq x p
        then bind (permute zs) (ipartl_spec_lemma10_aux1_aux1 p i x xs ys)
        else bind (permute (append zs (single x))) (ipartl_spec_lemma10_aux1_aux2 p i x xs ys)
    )

{-@ reflect ipartl_spec_lemma10_aux1_aux1 @-}
ipartl_spec_lemma10_aux1_aux1 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma10_aux1_aux1 p i x xs ys zs' =
  seq
    (writeList i (append (append ys (single x)) zs'))
    (ipartl p i (S (length ys), length zs', length xs))

{-@ reflect ipartl_spec_lemma10_aux1_aux2 @-}
ipartl_spec_lemma10_aux1_aux2 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma10_aux1_aux2 p i x xs ys zs' =
  seq
    (writeList i (append ys zs'))
    (ipartl p i (length ys, length zs', length xs))

-- ipartl_spec_lemma10_aux2

{-@ reflect ipartl_spec_lemma10_aux2 @-}
ipartl_spec_lemma10_aux2 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma10_aux2 p i x xs ys zs = bind (partl' p (ys, zs, Cons x xs)) (writeListToLength2 i)

-- ipartl_spec_lemma10

{-@
ipartl_spec_lemma10 ::
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_lemma10_aux1 p i x xs ys zs}
    {ipartl_spec_lemma10_aux2 p i x xs ys zs}
@-}
ipartl_spec_lemma10 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma10 = undefined -- TODO

{-@
ipartl_spec_lemma10_step1 ::
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_lemma10_aux1 p i x xs ys zs}
    {ipartl_spec_lemma10_aux2 p i x xs ys zs}
@-}
ipartl_spec_lemma10_step1 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma10_step1 = undefined -- TODO

{-@
ipartl_spec_lemma10_step2 ::
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_lemma10_aux1 p i x xs ys zs}
    {ipartl_spec_lemma10_aux2 p i x xs ys zs}
@-}
ipartl_spec_lemma10_step2 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma10_step2 = undefined -- TODO

{-@
ipartl_spec_lemma10_step3 ::
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_lemma10_aux1 p i x xs ys zs}
    {ipartl_spec_lemma10_aux2 p i x xs ys zs}
@-}
ipartl_spec_lemma10_step3 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma10_step3 = undefined -- TODO

{-@
ipartl_spec_lemma10_step4 ::
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_lemma10_aux1 p i x xs ys zs}
    {ipartl_spec_lemma10_aux2 p i x xs ys zs}
@-}
ipartl_spec_lemma10_step4 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma10_step4 = undefined -- TODO
