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

--
-- ipartl_spec_lemma5
--

-- uses ipartl_spec_lemma2, ipartl_spec_lemma3, ipartl_spec_lemma4
{-@
ipartl_spec_lemma5 ::
  Equality (M (Natural, Natural)) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_lemma6_aux2  i p x xs ys zs}
    {ipartl_spec_lemma1_aux1 i p x xs ys zs}
@-}
ipartl_spec_lemma5 :: Equality (M (Natural, Natural)) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma5 i p x xs ys zs =
  [eqp| ipartl_spec_lemma6_aux2 i p x xs ys zs
    %== seq
          (writeList (S (add (add i (length ys)) (length zs))) xs)
          ( if leq x p
              then
                seq
                  ( seq
                      (writeList i (concat (concat ys zs) (single x)))
                      (swap (add i (length ys)) (add (add i (length ys)) (length zs)))
                  )
                  (ipartl i p (S (length ys), length zs, length xs))
              else
                seq
                  (writeList i (concat (concat ys zs) (single x)))
                  (ipartl i p (length ys, S (length zs), length xs))
          )

    %== undefined %-- TODO

    %== ipartl_spec_lemma1_aux1 i p x xs ys zs  
  |]
