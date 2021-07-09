{-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--no-termination" @-}
-- needed this because `partl` threw termination checking errors even with lazy annotation
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Sort.IPartl where

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
import Sorr.IPartlWork
import Sort.IPartl
import Sort.List
import Prelude hiding (all, concat, foldl, length, pure, read, readList, seq)

--
-- ipartl_spec_lemma5
--

-- after applying lemma 3
{-@ reflect ipartl_spec_lemma5_step2 @-}
ipartl_spec_lemma5_step2 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma5_step2 i p x xs ys zs =
  seq
    (writeList (S (add (add i (length ys)) (length zs))) xs)
    ( if leq x p
        then
          seq
            (ipartl_spec_lemma3_aux2 i p x xs ys zs)
            (ipartl i p (S (length ys), length zs, length xs))
        else ipartl_spec_lemma2_aux1 i p x xs ys zs
    )

-- after applying lemma 2 and 3
{-@ reflect ipartl_spec_lemma5_step3 @-}
ipartl_spec_lemma5_step3 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma5_step3 i p x xs ys zs =
  seq
    (writeList (S (add (add i (length ys)) (length zs))) xs)
    ( if leq x p
        then
          seq
            (ipartl_spec_lemma3_aux2 i p x xs ys zs)
            (ipartl i p (S (length ys), length zs, length xs))
        else ipartl_spec_lemma2_aux2 i p x xs ys zs
    )

-- uses ipartl_spec_lemma2, ipartl_spec_lemma3, ipartl_spec_lemma4
{-@
ipartl_spec_lemma5 ::
  (Equality (M (Natural, Natural)), Equality (M ())) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_lemma6_aux2  i p x xs ys zs}
    {ipartl_spec_lemma1_aux1 i p x xs ys zs}
@-}
ipartl_spec_lemma5 :: (Equality (M (Natural, Natural)), Equality (M ())) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma5 i p x xs ys zs =
  refinesplus_transitivity step1 step2 step4 step1to2 $
    refinesplus_transitivity step2 step3 step4 step2to3 step3to4
  where
    step1 = ipartl_spec_lemma6_aux2 i p x xs ys zs
    step1to2 =
      refinesplus_substitutability
        step1to2_cont
        (ipartl_spec_lemma3_aux1 i p x xs ys zs)
        (ipartl_spec_lemma3_aux2 i p x xs ys zs)
        step1to2_cont_morphism
        (ipartl_spec_lemma3 i p x xs ys zs)
    step2 =
      ipartl_spec_lemma5_step2 i p x xs ys zs
    step2to3 =
      refinesplus_substitutability
        step2to3_cont
        (ipartl_spec_lemma2_aux1 i p x xs ys zs)
        (ipartl_spec_lemma2_aux2 i p x xs ys zs)
        step2to3_cont_morphism
        (ipartl_spec_lemma2 i p x xs ys zs)
    step3 = ipartl_spec_lemma5_step3 i p x xs ys zs
    step3to4 =
      refinesplus_equalprop
        (ipartl_spec_lemma5_step3 i p x xs ys zs)
        (ipartl_spec_lemma1_aux1 i p x xs ys zs)
        [eqp| ipartl_spec_lemma5_step3 i p x xs ys zs

          %== seq
                (writeList (S (add (add i (length ys)) (length zs))) xs)
                ( if leq x p
                    then seq
                          (ipartl_spec_lemma3_aux2 i p x xs ys zs)
                          (ipartl i p (S (length ys), length zs, length xs))
                    else
                        ipartl_spec_lemma2_aux2 i p x xs ys zs
                )

          %== seq
                (writeList (S (add (add i (length ys)) (length zs))) xs)
                ( if leq x p
                    then bind 
                          (permute zs)
                          (ipartl_spec_lemma1_aux1_aux1 i p x xs ys)
                    else
                        ipartl_spec_lemma2_aux2 i p x xs ys zs
                )

            %by %rewrite seq (ipartl_spec_lemma3_aux2 i p x xs ys zs) (ipartl i p (S (length ys), length zs, length xs))
                     %to bind (permute zs) (ipartl_spec_lemma1_aux1_aux1 i p x xs ys)
            %by undefined -- TODO

          %== seq
                (writeList (add (add (add i (length ys)) (length zs)) one) xs)
                ( if leq x p
                    then bind 
                          (permute zs)
                          (ipartl_spec_lemma1_aux1_aux1 i p x xs ys)
                    else bind
                          (permute (concat zs (single x)))
                          (ipartl_spec_lemma1_aux1_aux2 i p x xs ys)
                )
            
            %by %rewrite ipartl_spec_lemma2_aux2 i p x xs ys zs
                     %to bind (permute (concat zs (single x))) (ipartl_spec_lemma1_aux1_aux2 i p x xs ys)
            %by undefined -- TODO

          %== ipartl_spec_lemma1_aux1 i p x xs ys zs
        |]
    step4 = ipartl_spec_lemma1_aux1 i p x xs ys zs
    --
    step1to2_cont hole =
      seq
        (writeList (S (add (add i (length ys)) (length zs))) xs)
        ( if leq x p
            then
              seq
                hole
                (ipartl i p (S (length ys), length zs, length xs))
            else ipartl_spec_lemma2_aux1 i p x xs ys zs
        )
    --
    step1to2_cont_morphism = undefined -- TODO
    --
    step2to3_cont hole =
      seq
        (writeList (S (add (add i (length ys)) (length zs))) xs)
        ( if leq x p
            then
              seq
                (ipartl_spec_lemma3_aux2 i p x xs ys zs)
                (ipartl i p (S (length ys), length zs, length xs))
            else hole
        )
    --
    step2to3_cont_morphism = undefined -- TODO

-- ipartl_spec_lemma6

{-@
ipartl_spec_lemma6 ::
  (Equality (M (Natural, Natural)), Equality (() -> M (Natural, Natural))) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_aux1        i p (Cons x xs) ys zs}
    {ipartl_spec_lemma6_aux2 i p       x xs  ys zs}
@-}
ipartl_spec_lemma6 :: (Equality (M (Natural, Natural)), Equality (() -> M (Natural, Natural))) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma6 i p x xs ys zs =
  refinesplus_equalprop
    (ipartl_spec_aux1 i p (Cons x xs) ys zs)
    (ipartl_spec_lemma6_aux2 i p x xs ys zs)
    [eqp| ipartl_spec_aux1 i p (Cons x xs) ys zs

      %== seq
            (writeList i (concat (concat ys zs) (Cons x xs)))
            (ipartl i p (length ys, length zs, length (Cons x xs)))

        %by %reflexivity

      %== seq
            (writeList i (concat (concat ys zs) (Cons x xs)))
            (ipartl i p (length ys, length zs, S (length xs)))

        %by %rewrite length (Cons x xs)
                %to S (length xs)
        %by undefined %-- TODO: Liquid Type Mismatch
        %-- %by %reflexivity

      %== seq
            (writeList i (concat (concat ys zs) (Cons x xs)))
            (bind
              (read (add (add i (length ys)) (length zs)))
              (ipartl_aux i p (length ys) (length zs) (length xs)))

        %by %rewrite ipartl i p (length ys, length zs, S (length xs))
                %to bind (read (add (add i (length ys)) (length zs))) (ipartl_aux i p (length ys) (length zs) (length xs))
        %by %reflexivity

      %== bind 
            (seq
              (writeList i (concat (concat ys zs) (Cons x xs)))
              (read (add (add i (length ys)) (length zs)))
            )
            (ipartl_aux i p (length ys) (length zs) (length xs))

        %by %symmetry
        %by seq_bind_associativity
              (writeList i (concat (concat ys zs) (Cons x xs)))
              (read (add (add i (length ys)) (length zs)))
              (ipartl_aux i p (length ys) (length zs) (length xs))

      %== seq
            (writeList i (concat (concat ys zs) (Cons x xs)))
            (ipartl_aux i p (length ys) (length zs) (length xs) x)

        %by bind_seq_writeList_read_k i ys zs x xs
              (ipartl_aux i p (length ys) (length zs) (length xs))

      %== seq
            (writeList i (concat (concat ys zs) (Cons x xs)))
            (if leq x p
              then
                seq
                  (swap (add i (length ys)) (add (add i (length ys)) (length zs)))
                  (ipartl i p (S (length ys), length zs, length xs))
              else ipartl i p (length ys, S (length zs), (length xs)))

        %by %rewrite ipartl_aux i p (length ys) (length zs) (length xs) x
                %to if leq x p then seq (swap (add i (length ys)) (add (add i (length ys)) (length zs))) (ipartl i p (S (length ys), length zs, length xs)) else ipartl i p (length ys, S (length zs), (length xs))
        %by %reflexivity

      %-- TODO: need to actually fold in definitions of 
      %-- ipartl_spec_lemma2_aux1
      %-- ipartl_spec_lemma3_aux1

      %== ipartl_spec_lemma6_aux2 i p x xs ys zs
            
        %by %symmetry
        %by undefined
        %-- %by %reflexivity
  |]

{-@
bind_seq_writeList_read_k ::
  i:Natural -> ys:List Int -> zs:List Int -> x:Int -> xs:List Int -> k:(Int -> M a) ->
  EqualProp (M a)
    {bind (seq (writeList i (concat (concat ys zs) (Cons x xs))) (read (add (add i (length ys)) (length zs)))) k}
    {seq (writeList i (concat (concat ys zs) (Cons x xs))) (k x)}
@-}
bind_seq_writeList_read_k :: Natural -> List Int -> List Int -> Int -> List Int -> (Int -> M a) -> EqualityProp (M a)
bind_seq_writeList_read_k i ys zs x xs k = undefined -- TODO
