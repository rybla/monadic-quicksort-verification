{-@ LIQUID "--no-termination" @-}
-- needed this because `partl` threw termination checking errors even with lazy annotation
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Sort.IPartlWork where

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
import Prelude hiding (all, concat, foldl, length, pure, read, readList, seq)

{-@
ipartl_spec_lemma1_aux1to2 ::
  (Equality (M (List Int, List Int, List Int)), Equality (M (Natural, Natural))) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_lemma1_aux1 i p x xs ys zs}
    {ipartl_spec_lemma1_step2 i p x xs ys zs}
@-}
ipartl_spec_lemma1_aux1to2 :: (Equality (M (List Int, List Int, List Int)), Equality (M (Natural, Natural))) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_aux1to2 i p x xs ys zs =
  (refinesplus_equalprop (ipartl_spec_lemma1_aux1 i p x xs ys zs) (ipartl_spec_lemma1_step2 i p x xs ys zs))
    [eqp| ipartl_spec_lemma1_aux1 i p x xs ys zs
      
      %== ipartl_spec_lemma1_aux1A i p x xs ys zs
            %by ipartl_spec_lemma1_aux1to1A i p x xs ys zs
      
      %== ipartl_spec_lemma1_aux1B i p x xs ys zs
            %by ipartl_spec_lemma1_aux1Ato1B i p x xs ys zs
      
      %== ipartl_spec_lemma1_step2 i p x xs ys zs
            %by ipartl_spec_lemma1_aux1Bto2 i p x xs ys zs
    |]

{-@
ipartl_spec_lemma1_aux1to1A ::
  (Equality (M (List Int, List Int, List Int)), Equality (M (Natural, Natural)), Equality (M (List Int, List Int, List Int))) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  EqualProp (M (Natural, Natural))
    {ipartl_spec_lemma1_aux1  i p x xs ys zs}
    {ipartl_spec_lemma1_aux1A i p x xs ys zs}
@-}
ipartl_spec_lemma1_aux1to1A :: (Equality (M (List Int, List Int, List Int)), Equality (M (Natural, Natural)), Equality (M (List Int, List Int, List Int))) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_aux1to1A i p x xs ys zs =
  [eqp| ipartl_spec_lemma1_aux1 i p x xs ys zs

    %== seq
          (writeList (add (add (add i (length ys)) (length zs)) one) xs)
          ( if leq x p
              then bind (permute zs) (ipartl_spec_lemma1_aux1_aux1 i p x xs ys)
              else bind (permute (concat zs (single x))) (ipartl_spec_lemma1_aux1_aux2 i p x xs ys)
          )

    %== seq
          (writeList (S (add (add i (length ys)) (length zs))) xs)
          ( bind
              ( if leq x p
                  then bind (permute zs) (dispatch_aux1 x xs ys)
                  else bind (permute (snoc zs x)) (dispatch_aux2 xs ys)
              )
              (ipartl_spec_lemma1_aux1A_aux i p x)
          )
      %by distribute_if
            (leq x p)
            (bind (permute zs) (dispatch_aux1 x xs ys))
            (bind (permute (snoc zs x)) (dispatch_aux2 xs ys))
            (ipartl_spec_lemma1_aux1A_aux i p x)

    %== seq
          (writeList (S (add (add i (length ys)) (length zs))) xs)
          ( bind
              (dispatch x p (ys, zs, xs))
              (ipartl_spec_lemma1_aux1A_aux i p x)
          )
      %by %rewrite if leq x p then bind (permute zs) (dispatch_aux1 x xs ys) else bind (permute (snoc zs x)) (dispatch_aux2 xs ys)
              %to dispatch x p (ys, zs, xs)
      %by %symmetry
      %by %reflexivity

    %== ipartl_spec_lemma1_aux1A i p x xs ys zs
  |]

{-@
ipartl_spec_lemma1_aux1Ato1B ::
  Equality (M (Natural, Natural)) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  EqualProp (M (Natural, Natural))
    {ipartl_spec_lemma1_aux1A i p x xs ys zs}
    {ipartl_spec_lemma1_aux1B i p x xs ys zs}
@-}
ipartl_spec_lemma1_aux1Ato1B :: Equality (M (Natural, Natural)) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_aux1Ato1B i p x xs ys zs =
  [eqp| ipartl_spec_lemma1_aux1A i p x xs ys zs
    %== seq
          (writeList (S (add (add i (length ys)) (length zs))) xs)
          ( bind
              (dispatch x p (ys, zs, xs))
              (ipartl_spec_lemma1_aux1A_aux i p x)
          )
    %== seq
          (writeList (S (add (add i (length ys)) (length zs))) xs)
          ( if leq x p
              then 
                  bind
                    (permute zs)
                    (ipartl_spec_lemma1_aux1_aux1 i p x xs ys)
              else
                bind
                  (permute (concat zs (single x)))
                  (ipartl_spec_lemma1_aux1_aux2 i p x xs ys)
          )
      %by permute_preserves_length zs
    %== ipartl_spec_lemma1_aux1 i p x xs ys zs
    %== ipartl_spec_lemma1_aux1B i p x xs ys zs
  |]

{-@
ipartl_spec_lemma1_aux1Bto2 ::
  Equality (M (Natural, Natural)) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  EqualProp (M (Natural, Natural))
    {ipartl_spec_lemma1_aux1B i p x xs ys zs}
    {ipartl_spec_lemma1_step2  i p x xs ys zs}
@-}
ipartl_spec_lemma1_aux1Bto2 :: Equality (M (Natural, Natural)) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_aux1Bto2 i p x xs ys zs =
  [eqp| ipartl_spec_lemma1_aux1B i p x xs ys zs
    %== ipartl_spec_lemma1_aux1 i p x xs ys zs
    %== seq
          (writeList (S (add (add i (length ys)) (length zs))) xs)
          ( if leq x p
              then 
                  bind
                    (permute zs)
                    (ipartl_spec_lemma1_aux1_aux1 i p x xs ys)
              else
                bind
                  (permute (concat zs (single x)))
                  (ipartl_spec_lemma1_aux1_aux2 i p x xs ys)
          )
    %== bind
          ( if leq x p
              then bind (permute zs) (dispatch_aux1 x xs ys)
              else bind (permute (snoc zs x)) (dispatch_aux2 xs ys)
          )
          (ipartl_spec_lemma1_step2_aux i p x)
      %by distribute_if (leq x p) (bind (permute zs) (dispatch_aux1 x xs ys)) (bind (permute (snoc zs x)) (dispatch_aux2 xs ys)) ((ipartl_spec_lemma1_step2_aux i p x))
    %== bind
          (dispatch x p (ys, zs, xs))
          (ipartl_spec_lemma1_step2_aux i p x)
    %== ipartl_spec_lemma1_step2 i p x xs ys zs
  |]

{-@
ipartl_spec_lemma1_step2to3 ::
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_lemma1_step2 i p x xs ys zs}
    {ipartl_spec_lemma1_step3 i p x xs ys zs}
@-}
ipartl_spec_lemma1_step2to3 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_step2to3 = undefined -- TODO

{-@
ipartl_spec_lemma1_step3to4 ::
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_lemma1_step3 i p x xs ys zs}
    {ipartl_spec_aux2 i p (Cons x xs) ys zs}
@-}
ipartl_spec_lemma1_step3to4 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_step3to4 = undefined -- TODO
