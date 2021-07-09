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
ipartl_spec ::
  (Equality (M ()), Equality (M (List Int)), (Equality (() -> M (Natural, Natural))), Equality (M (Natural, Natural))) =>
  i:Natural -> p:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_aux1 i p xs ys zs}
    {ipartl_spec_aux2 i p xs ys zs}
@-}
ipartl_spec :: (Equality (M ()), Equality (M (List Int)), (Equality (() -> M (Natural, Natural))), Equality (M (Natural, Natural))) => Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec i p Nil ys zs =
  refinesplus_equalprop
    (ipartl_spec_aux1 i p Nil ys zs)
    (ipartl_spec_aux2 i p Nil ys zs)
    [eqp| ipartl_spec_aux1 i p Nil ys zs
      %== seq
            (writeList i (concat (concat ys zs) Nil))
            (ipartl i p (length ys, length zs, length Nil))
      %== seq
            (writeList i (concat (concat ys zs) Nil))
            (ipartl i p (length ys, length zs, Z))
      %== seq
            (writeList i (concat (concat ys zs) Nil))
            (pure (length ys, length zs))
      %== seq
            (writeList i (concat ys zs))
            (pure (length ys, length zs))
        %by %smt
        %by concat_identity (concat ys zs)
      %== undefined -- writeListToLength2 i (ys, zs)
      %== bind
            (pure (ys, zs))
            (writeListToLength2 i)
        %by pure_bind (ys, zs) (writeListToLength2 i)
      %== bind
            (partl' p (ys, zs, Nil))
            (writeListToLength2 i)
    |]
ipartl_spec i p (Cons x xs) ys zs =
  refinesplus_transitivity step1 step2 step4 step1to2 $
    refinesplus_transitivity step2 step3 step4 step2to3 step3to4
  where
    step1 = ipartl_spec_aux1 i p (Cons x xs) ys zs
    step1to2 = ipartl_spec_lemma6 i p x xs ys zs
    step2 = ipartl_spec_lemma6_aux2 i p x xs ys zs
    step2to3 = ipartl_spec_lemma5 i p x xs ys zs
    step3 = ipartl_spec_lemma1_aux1 i p x xs ys zs
    step3to4 = ipartl_spec_lemma1 i p x xs ys zs
    step4 = ipartl_spec_aux2 i p (Cons x xs) ys zs
