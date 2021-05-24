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
ipartl_spec_steps7to8 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps7to8 = undefined -- TODO
{-
ipartl_spec_step7 p i x xs ys zs
-- defn ipartl_spec_step7
dispatch x p (ys, zs, xs) >>=
  writeListToLength3 i >>=
    ipartl p i
-- bind_associativity
dispatch x p (ys, zs, xs) >>=
  kleisli
    (writeListToLength3 i)
    (ipartl p i)
-- eta-equivalence
dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
  kleisli
    (writeListToLength3 i)
    (ipartl p i)
    (ys', zs', xs)
-- ipartl_spec_steps7to8_lemma
dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
  kleisli
    (partl' p)
    (writeListToLength2 i)
    (ys', zs', xs)
-- eta-equivalence
dispatch x p (ys, zs, xs) >>=
  kleisli
    (partl' p)
    (writeListToLength2 i)
-- bind_associativity
dispatch x p (ys, zs, xs) >>=
  partl' p >>=
    writeListToLength2 i
-- defn ipartl_spec_step8
ipartl_spec_step8 p i x xs ys zs
-}

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
