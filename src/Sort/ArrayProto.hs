{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Sort.ArrayProto where

import Data.Refined.Bool
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Tuple
import Data.Refined.Unit
import Data.Text (Text, unpack)
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.TH.Ppr (pprint)
import Language.Haskell.TH.Syntax
import NeatInterpolation (text)
import Placeholder.M
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Sort.Array
import Sort.List
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (*), (+), (++), (>>), (>>=))

--
-- ipartl_spec_steps7to8_lemma
--

{-@ reflect ipartl_spec_steps7to8_lemma_aux1 @-}
ipartl_spec_steps7to8_lemma_aux1 :: Int -> Natural -> (List Int, List Int, List Int) -> M (Natural, Natural)
ipartl_spec_steps7to8_lemma_aux1 p i (ys', zs', xs) =
  kleisli
    (writeListToLength3 i)
    (ipartl p i)
    (ys', zs', xs)

{-@ reflect ipartl_spec_steps7to8_lemma_aux2 @-}
ipartl_spec_steps7to8_lemma_aux2 :: Int -> Natural -> (List Int, List Int, List Int) -> M (Natural, Natural)
ipartl_spec_steps7to8_lemma_aux2 p i (ys', zs', xs) =
  kleisli
    (partl' p)
    (writeListToLength2 i)
    (ys', zs', xs)

{-@
ipartl_spec_steps7to8_lemma ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> ys'_zs'_xs:(List Int, List Int, List Int) ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_steps7to8_lemma_aux1 p i ys'_zs'_xs}
    {ipartl_spec_steps7to8_lemma_aux2 p i ys'_zs'_xs}
@-}
ipartl_spec_steps7to8_lemma :: Equality (M (Natural, Natural)) => Int -> Natural -> (List Int, List Int, List Int) -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps7to8_lemma p i (ys', zs', xs) =
  (refinesplus_transitivity aux1 aux2 aux4)
    step1
    ( (refinesplus_transitivity aux2 aux3 aux4)
        step2
        step3
    )
  where
    aux1 = kleisli (writeListToLength3 i) (ipartl p i) (ys', zs', xs)
    aux2 = ipartl_spec_aux1 p i xs ys' zs'
    aux3 = ipartl_spec_aux2 p i xs ys' zs'
    aux4 = kleisli (partl' p) (writeListToLength2 i) (ys', zs', xs)
    step1 =
      (refinesplus_equalprop aux1 aux2)
        [eqpropchain|
              kleisli
                (writeListToLength3 i)
                (ipartl p i)
                (ys', zs', xs)

            %== -- defn kleisli
              writeListToLength3 i (ys', zs', xs) >>=
                ipartl p i

                %by %reflexivity

            %== -- defn writeListToLength3
              writeList i (ys' ++ zs' ++ xs) >>
                pure (length ys', length zs', length xs) >>=
                  ipartl p i

                %by %rewrite writeListToLength3 i (ys', zs', xs)
                        %to writeList i (ys' ++ zs' ++ xs) >> pure (length ys', length zs', length xs)
                %by %reflexivity

            %== -- seq_bind_associativity
              writeList i (ys' ++ zs' ++ xs) >>
                ( pure (length ys', length zs', length xs) >>=
                    ipartl p i
                )

                %by seq_bind_associativity
                      (writeList i (ys' ++ zs' ++ xs))
                      (pure (length ys', length zs', length xs))
                      (ipartl p i)


            %== -- pure_bind
              writeList i (ys' ++ zs' ++ xs) >>
                ipartl p i (length ys', length zs', length xs)

                %by %rewrite pure (length ys', length zs', length xs) >>= ipartl p i
                        %to ipartl p i (length ys', length zs', length xs)
                %by pure_bind (length ys', length zs', length xs) (ipartl p i)

            %== -- defn ipartl_spec_aux1
              ipartl_spec_aux1 p i xs ys' zs'

                %by %symmetry
                %by %reflexivity
        |]
    step2 = ipartl_spec p i xs ys' zs'
    step3 =
      (refinesplus_equalprop aux3 aux4)
        [eqpropchain|
            ipartl_spec_aux2 p i xs ys' zs'

          %== -- defn ipartl_spec_aux2
            partl' p (ys', zs', xs) >>=
              writeListToLength2 i

              %by %reflexivity

          %== -- defn kleisli
            kleisli
              (partl' p)
              (writeListToLength2 i)
              (ys', zs', xs)

              %by %symmetry
              %by %reflexivity
        |]

--
-- ipartl_spec_steps7to8
--

-- uses:
-- - monad laws
-- - inductive hypothesis
{-@
ipartl_spec_steps7to8 ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step7 p i x xs ys zs}
    {ipartl_spec_step8 p i x xs ys zs}
@-}
ipartl_spec_steps7to8 :: Equality (M (Natural, Natural)) => Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps7to8 p i x xs ys zs =
  (refinesplus_transitivity aux1 aux2 aux4)
    step1
    ( (refinesplus_transitivity aux2 aux3 aux4)
        step2
        step3
    )
  where
    aux1 = ipartl_spec_step7 p i x xs ys zs
    aux2 = dispatch x p (ys, zs, xs) >>= ipartl_spec_steps7to8_lemma_aux1 p i
    aux3 = dispatch x p (ys, zs, xs) >>= ipartl_spec_steps7to8_lemma_aux2 p i
    aux4 = ipartl_spec_step8 p i x xs ys zs
    step1 =
      (refinesplus_equalprop aux1 aux2)
        [eqpropchain|
            ipartl_spec_step7 p i x xs ys zs

          %== -- defn ipartl_spec_step7
            dispatch x p (ys, zs, xs) >>=
              writeListToLength3 i >>=
                ipartl p i

              %by %reflexivity

          %== -- bind_associativity
            dispatch x p (ys, zs, xs) >>=
              kleisli
                (writeListToLength3 i)
                (ipartl p i)

              %by bind_associativity_nofix
                    (dispatch x p (ys, zs, xs))
                    (writeListToLength3 i)
                    (ipartl p i)

          %== -- eta-equivalence
            dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
              kleisli
                (writeListToLength3 i)
                (ipartl p i)
                (ys', zs', xs)

              %by %rewrite kleisli (writeListToLength3 i) (ipartl p i)
                       %to \(ys', zs', xs) -> kleisli (writeListToLength3 i) (ipartl p i) (ys', zs', xs)
              %by %extend (ys', zs', xs)
              %by %symmetry
              %by %reflexivity
      |]
    step2 =
      refinesplus_substitutabilityF
        step2_aux
        (ipartl_spec_steps7to8_lemma_aux1 p i)
        (ipartl_spec_steps7to8_lemma_aux2 p i)
        (ipartl_spec_steps7to8_lemma p i)
    step2_aux k = dispatch x p (ys, zs, xs) >>= k
    step3 =
      (refinesplus_equalprop aux3 aux4)
        [eqpropchain|
            dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
              kleisli
                (partl' p)
                (writeListToLength2 i)
                (ys', zs', xs)

          %== -- eta-equivalence
            dispatch x p (ys, zs, xs) >>=
              kleisli
                (partl' p)
                (writeListToLength2 i)

              %by %rewrite \(ys', zs', xs) -> kleisli (partl' p) (writeListToLength2 i) (ys', zs', xs)
                       %to kleisli (partl' p) (writeListToLength2 i)
              %by %extend (ys', zs', xs)
              %by %reflexivity

          %== -- bind_associativity
            dispatch x p (ys, zs, xs) >>=
              partl' p >>=
                writeListToLength2 i

              %by %symmetry
              %by bind_associativity_nofix
                    (dispatch x p (ys, zs, xs))
                    (partl' p)
                    (writeListToLength2 i)

          %== -- defn ipartl_spec_step8
            ipartl_spec_step8 p i x xs ys zs

              %by %symmetry
              %by %reflexivity
        |]

-- uses:
-- - defn of `partl`'
{-@
ipartl_spec_steps8to9 ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step8 p i x xs ys zs}
    {ipartl_spec_step9 p i x xs ys zs}
@-}
ipartl_spec_steps8to9 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps8to9 = undefined -- TODO

{-@
ipartl_spec_steps ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step1 p i x xs ys zs}
    {ipartl_spec_step9 p i x xs ys zs}
@-}
ipartl_spec_steps :: Equality (M (Natural, Natural)) => Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps p i x xs ys zs = undefined

{- -- * correct
  (refinesplus_transitivity step1 step3 step9)
    -- 1 refines 3
    (ipartl_spec_steps_1_to_3 p i x xs ys zs)
    ( (refinesplus_transitivity step3 step4 step9)
        -- 3 refines 4
        (ipartl_spec_steps_3_to_4 p i x xs ys zs)
        ( (refinesplus_transitivity step4 step7 step9)
            -- 4 refines 7
            (ipartl_spec_steps_4_to_7 p i x xs ys zs)
            ( (refinesplus_transitivity step7 step8 step9)
                -- 7 refines 8
                (ipartl_spec_steps7to8 p i x xs ys zs)
                -- 8 refines 9
                (ipartl_spec_steps8to9 p i x xs ys zs)
            )
        )
    )
  where
    -- steps
    step1 = ipartl_spec_step1 p i x xs ys zs
    step3 = ipartl_spec_step3 p i x xs ys zs
    step4 = ipartl_spec_step4 p i x xs ys zs
    step7 = ipartl_spec_step7 p i x xs ys zs
    step8 = ipartl_spec_step8 p i x xs ys zs
    step9 = ipartl_spec_step9 p i x xs ys zs
-}

-- [ref 10]
-- I am ignoring the previous spec for ipartl given at the top of the same page
-- as [ref 10], but I'm pretty sure that's ok. That spec isn't used anywhere
-- right?
{-@
ipartl_spec ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_aux1 p i xs ys zs}
    {ipartl_spec_aux2 p i xs ys zs}
@-}
ipartl_spec :: Equality (M (Natural, Natural)) => Int -> Natural -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec p i Nil ys zs = undefined
ipartl_spec p i (Cons x xs) ys zs = undefined
