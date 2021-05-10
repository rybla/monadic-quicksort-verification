{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

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

{-@ reflect ipartl_spec_step1 @-}
ipartl_spec_step1 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_step1 p i x xs ys zs = ipartl_spec_aux1 p i (Cons x xs) ys zs

-- TODO: do I need this? or just use `ipartl_spec_aux1` above
-- writeList i (ys ++ zs ++ Cons x xs)
--   >> read (i + length ys + length zs) >>= \x ->
--     if x <= p
--       then
--         swap (i + length ys) (i + length ys + length zs)
--           >> ipartl p i (S (length ys), length zs, length xs)
--       else ipartl p i (length ys, S (length zs), length xs)

{-@ reflect ipartl_spec_step3 @-}
ipartl_spec_step3 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_step3 p i x xs ys zs =
  writeList (S (i + length ys + length zs)) xs
    >> if x <= p
      then
        writeList i (ys ++ zs ++ Cons x Nil)
          >> swap (i + length ys) (i + length ys + length zs)
          >> ipartl p i (S (length ys), length zs, length xs)
      else
        writeList i (ys ++ zs ++ Cons x Nil)
          >> ipartl p i (length ys, S (length zs), length xs)

{-@ reflect ipartl_spec_step4 @-}
ipartl_spec_step4 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_step4 p i x xs ys zs =
  writeList (S (i + length ys + length zs)) xs
    >> if x <= p
      then
        permute zs >>= \zs' ->
          writeList i (ys ++ Cons x Nil ++ zs')
            >> ipartl p i (S (length ys), length zs', length xs)
      else
        permute (zs ++ Cons x Nil) >>= \zs' ->
          writeList i (ys ++ zs')
            >> ipartl p i (length ys, length zs', length xs)

{-@ reflect ipartl_spec_step7 @-}
ipartl_spec_step7 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_step7 p i x xs ys zs =
  dispatch x p (ys, zs, xs)
    >>= writeListToLength3 i
    >>= ipartl p i

{-@ reflect ipartl_spec_step8 @-}
ipartl_spec_step8 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_step8 p i x xs ys zs =
  dispatch x p (ys, zs, xs)
    >>= partl' p
    >>= writeListToLength2 i

{-@ reflect ipartl_spec_step9 @-}
ipartl_spec_step9 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_step9 p i x xs ys zs = ipartl_spec_aux2 p i (Cons x xs) ys zs

-- TODO: do I need this? or just use `ipartl_spec_aux2` above
-- partl' p (ys, zs, Cons x xs)
--   >>= writeListToLength2 i

-- uses:
-- - `seq_write_read`
-- - defn of `writeList`
-- - distributivity of `if`
-- - [ref 9]
{-@
ipartl_spec_steps_1_to_3 ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step1 p i x xs ys zs}
    {ipartl_spec_step3 p i x xs ys zs}
@-}
ipartl_spec_steps_1_to_3 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps_1_to_3 = undefined

-- uses:
-- - `ipartl_spec_lemma1`,
-- - `ipartl_spec_lemma2`
{-@
ipartl_spec_steps_3_to_4 ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step3 p i x xs ys zs}
    {ipartl_spec_step4 p i x xs ys zs}
@-}
ipartl_spec_steps_3_to_4 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps_3_to_4 = undefined

-- uses:
-- - defn of `dispatch`
-- - function calls distribute into `if` -- TODO: define lemma
-- - `permute_preserves_length`
-- - commutativity
-- - [ref 9]
{-@
ipartl_spec_steps_4_to_7 ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step4 p i x xs ys zs}
    {ipartl_spec_step7 p i x xs ys zs}
@-}
ipartl_spec_steps_4_to_7 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps_4_to_7 = undefined

-- uses:
-- - monad laws
-- - inductive hypothesis
{-@
ipartl_spec_steps_7_to_8 ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step7 p i x xs ys zs}
    {ipartl_spec_step8 p i x xs ys zs}
@-}
ipartl_spec_steps_7_to_8 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps_7_to_8 = undefined

-- uses:
-- - defn of `partl`'
{-@
ipartl_spec_steps_8_to_9 ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step8 p i x xs ys zs}
    {ipartl_spec_step9 p i x xs ys zs}
@-}
ipartl_spec_steps_8_to_9 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps_8_to_9 = undefined

{-@
ipartl_spec_steps ::
  Equality (M (Natural, Natural)) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step1 p i x xs ys zs}
    {ipartl_spec_step9 p i x xs ys zs}
@-}
ipartl_spec_steps :: Equality (M (Natural, Natural)) => Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps p i x xs ys zs =
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
                (ipartl_spec_steps_7_to_8 p i x xs ys zs)
                -- 8 refines 9
                (ipartl_spec_steps_8_to_9 p i x xs ys zs)
            )
        )
    )
  where
    -- steps
    step1 = ipartl_spec_step1 p i x xs ys zs
    step2 = ipartl_spec_step2 p i x xs ys zs
    step3 = ipartl_spec_step3 p i x xs ys zs
    step4 = ipartl_spec_step4 p i x xs ys zs
    step5 = ipartl_spec_step5 p i x xs ys zs
    step6 = ipartl_spec_step6 p i x xs ys zs
    step7 = ipartl_spec_step7 p i x xs ys zs
    step8 = ipartl_spec_step8 p i x xs ys zs
    step9 = ipartl_spec_step9 p i x xs ys zs

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
ipartl_spec p i (Cons x xs) ys zs =
  (refinesplus_transitivity aux1 step1 aux2)
    aux1_refines_step1
    ( (refinesplus_transitivity step1 step9 aux2)
        step1_refines_step9
        step9_refines_aux2
    )
  where
    -- steps
    aux1 = ipartl_spec_aux1 p i (Cons x xs) ys zs
    step1 = ipartl_spec_step1 p i x xs ys zs
    step9 = ipartl_spec_step9 p i x xs ys zs
    aux2 = ipartl_spec_aux2 p i (Cons x xs) ys zs
    -- proofs
    aux1_refines_step1 = refinesplus_equalprop aux1 step1 (symmetry step1 aux1 (reflexivity step1))
    step1_refines_step9 = ipartl_spec_steps p i x xs ys zs
    step9_refines_aux2 = refinesplus_equalprop step9 aux2 (reflexivity step9)

{-
  [eqpropchain|
      ipartl_spec_aux1 p i (Cons x xs) ys zs
    %{-
    %==
      writeList i (ys ++ zs ++ Cons x xs) >>
        ipartl p i (length ys, length zs, length (Cons x xs))
    %==
      writeList i (ys ++ zs ++ Cons x xs) >>
        ipartl p i (length ys, length zs, S (length xs))
        %by %rewrite length (Cons x xs)
                %to S (length xs)
        %by %reflexivity
    %==
      writeList i (ys ++ zs ++ Cons x xs) >>
        read (i + length ys + length zs) >>=
          ipartl_aux p i (length ys) (length zs) (length xs)
        %by %rewrite ipartl p i (length ys, length zs, S (length xs))
                 %to read (i + length ys + length zs) >>= ipartl_aux p i (length ys) (length zs) (length xs)
        %by undefined
        %-- TODO: %by %reflexivity
    %==
      %-- (1)
      writeList i (ys ++ zs ++ Cons x xs) >>
        read (i + length ys + length zs) >>= \x ->
          if x <= p then
            swap (i + length ys) (i + length ys + length zs) >>
              ipartl p i (S (length ys), length zs, length xs)
          else
            ipartl p i (length ys, S (length zs), length xs)
        %by %rewrite ipartl_aux p i (length ys) (length zs) (length xs)
                 %to \x -> if x <= p then swap (i + length ys) (i + length ys + length zs) >> ipartl p i (S (length ys), length zs, length xs) else ipartl p i (length ys, S (length zs), length xs)
        %by %extend x
        %by %reflexivity
    -}%
    %==
      undefined
    %==
      %-- (2)
      writeList i (ys ++ zs ++ Cons x xs) >>
        if x <= p then
          swap (i + length ys) (i + length ys + length zs) >>
            ipartl p i (S (length ys), length zs, length xs)
        else
          ipartl p i (length ys, S (length zs), length xs)
        %by undefined %-- TODO
        %-- distributivity of `if`, [ref 9]
    %==
      undefined
    %==
    %{-
      %-- applying ipartl_spec_lemma2
      writeList (S (i + length ys + length zs)) xs >>
        if x <= p then
          writeList i (ys ++ zs ++ Cons x Nil) >>
            swap (i + length ys) (i + length ys + length zs) >>
              ipartl p i (S (length ys), length zs, length xs)
        else
          writeList i (ys ++ zs ++ Cons x Nil) >>
            ipartl p i (length ys, S (length zs), length xs)
        %by undefined %-- TODO
        %-- by ipartl_spec_lemma2
    %==
      %-- applying ipartl_spec_lemma1
      writeList (S (i + length ys + length zs)) xs >>
        if x <= p then
          permute zs >>= \zs' ->
            writeList i (ys ++ Cons x Nil ++ zs') >>
              ipartl p i (S (length ys), length zs', length xs)
        else
          writeList i (ys ++ zs ++ Cons x Nil) >>
            ipartl p i (length ys, S (length zs), length xs)
        %by undefined %-- TODO
        %-- by ipartl_spec_lemma1
    %==
      %-- (4)
      writeList (S (i + length ys + length zs)) xs >>
        if x <= p then
          permute zs >>= \zs' ->
            writeList i (ys ++ Cons x Nil ++ zs') >>
              ipartl p i (S (length ys), length zs', length xs)
        else
          permute (zs ++ Cons x Nil) >>= \zs' ->
            writeList i (ys ++ zs') >>
              ipartl p i (length ys, length zs', length xs)
        %by undefined %-- TODO
        %-- defn of `dispatch`, function calls distribute into `if`
    %==
      %-- (5)
      writeList (S (i + length ys + length zs)) xs >>
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i (ys' ++ zs') >>
            ipartl p i (length ys', length zs', length xs)
        %by undefined %-- TODO
        %-- `permute` preserves length, commutativity
    %==
      %-- (6)
      dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
        writeList i (ys' ++ zs') >>
          writeList (i + length (ys' ++ zs')) xs >>
            ipartl p i (length ys', length zs', length xs)
        %by undefined %-- TODO
        %-- monad laws, [ref 9]
    %==
      %-- (7)
      dispatch x p (ys, zs, xs) >>= writeListToLength3 i >>= ipartl p i
        %by undefined %-- TODO
        %-- monad laws, inductive hypothesis
    %==
      %-- (8)
      dispatch x p (ys, zs, xs) >>= partl' p >>= writeListToLength2 i
        %by undefined %-- TODO
    %==
      %-- (9)
      partl' p (ys, zs, Cons x xs) >>= writeListToLength2 i
        %by %symmetry
        %by %reflexivity
    %==
    -}%
      ipartl_spec_aux2 p i (Cons x xs) ys zs
        %by %symmetry
        %by %reflexivity
  |]
-}

{- -- * definitions

ipartl_spec_aux1 p i xs ys zs = writeList i (ys ++ zs ++ xs) >> ipartl p i (length ys, length zs, length xs)

ipartl_spec_aux2 p i xs ys zs = partl' p (ys, zs, xs) >>= writeListToLength2 i
-}

-- [ref 12]
{-@
iqsort_spec ::
  (Equality (M Unit), Equality (M (List Int))) =>
  i:Natural ->
  xs:List Int ->
  RefinesPlus (Unit)
    {iqsort_spec_aux1 i xs}
    {iqsort_spec_aux2 i xs}
@-}
iqsort_spec :: (Equality (M ()), Equality (M (List Int))) => Natural -> List Int -> EqualityProp (M ())
iqsort_spec i Nil = undefined
{- -- * correct
  [eqpropchain|
      iqsort_spec_aux1 i Nil <+> iqsort_spec_aux2 i Nil
    %==
      pure it <+> iqsort_spec_aux2 i Nil
        %by %rewrite iqsort_spec_aux1 i Nil %to pure it
        %by iqsort_spec_aux1_Nil i
    %==
      pure it <+> pure it
        %by %rewrite iqsort_spec_aux2 i Nil %to pure it
        %by iqsort_spec_aux2_Nil i
    %==
      pure it
        %by refinesplus_reflexivity (pure it)
    %==
      iqsort_spec_aux2 i Nil
        %by %symmetry
        %by iqsort_spec_aux2_Nil i
  |]
-}
-- outline:
--   iqsort_spec_aux1 i (Cons p xs) refines
--   iqsort_spec_lemma3_aux1 i p xs refines
--   iqsort_spec_lemma1_aux1 i p xs refines
--   iqsort_spec_aux2 i (Cons p xs).
iqsort_spec i (Cons p xs) = undefined

{- --* correct
  refinesplus_transitivity
    (iqsort_spec_aux1 i (Cons p xs)) -- (1)
    (iqsort_spec_lemma3_aux1 i p xs) -- (2)
    (iqsort_spec_aux2 i (Cons p xs)) -- (4)
    (iqsort_spec_lemma4 i p xs) -- (1) refines (2)
    ( refinesplus_transitivity -- (2) refines (4)
        (iqsort_spec_lemma3_aux1 i p xs) -- (2)
        (iqsort_spec_lemma1_aux1 i p xs) -- (3)
        (iqsort_spec_aux2 i (Cons p xs)) -- (4)
        (iqsort_spec_lemma3 i p xs) -- (2) refines (3)
        ( refinesplus_equalprop -- (3) refines (4)
            (iqsort_spec_lemma1_aux1 i p xs)
            (iqsort_spec_aux2 i (Cons p xs))
            ( symmetry -- (3) eqprop (4)
                (iqsort_spec_aux2 i (Cons p xs))
                (iqsort_spec_lemma1_aux1 i p xs)
                (iqsort_spec_lemma1 i p xs)
            )
        )
    )
-}

{- -- * definitions
iqsort_spec_aux1 i xs = writeList i xs >> iqsort i (length xs)
iqsort_spec_aux1_Cons_aux i p xs =
  (write i p >> writeList (S i) xs)
    >> (read i >>= iqsort_aux1 i n)
  where
    n = length xs

iqsort_spec_aux2 i xs = slowsort xs >>= writeList i
iqsort_spec_aux2_Cons_aux i p xs =
  split xs
    >>= permute_aux1 p
    >>= guardBy sorted
    >>= writeList i

iqsort_spec_lemma1_aux1 i p xs =
  partl' p (Nil, Nil, xs) >>= iqsort_spec_lemma1_aux2 i p
iqsort_spec_lemma1_aux2 i p (ys, zs) =
  permute ys >>= iqsort_spec_lemma1_aux3 i p ys zs
iqsort_spec_lemma1_aux3 i p ys zs ys' =
  writeList i (ys' ++ Cons p Nil ++ zs)
    >> iqsort i (length ys)
    >> iqsort (S (i + length ys)) (length zs)
-}
