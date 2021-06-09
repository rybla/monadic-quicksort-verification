{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Sort.ArrayProtoProto where

import Array.Proto
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

-- [ref 12]
{-@
iqsort_spec ::
  (Equality (() -> M ()), Equality (M Unit), Equality (M (List Int))) =>
  i:Natural ->
  xs:List Int ->
  RefinesPlus (Unit)
    {iqsort_spec_aux1 i xs}
    {iqsort_spec_aux2 i xs}
@-}
iqsort_spec :: (Equality (() -> M ()), Equality (M ()), Equality (M (List Int))) => Natural -> List Int -> EqualityProp (M ())
iqsort_spec i Nil =
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
iqsort_spec i (Cons p xs) =
  (refinesplus_transitivity aux1 aux2 aux4)
    step1
    ( (refinesplus_transitivity aux2 aux3 aux4)
        step2
        step3
    )
  where
    aux1 = iqsort_spec_aux1 i (Cons p xs)
    aux2 = iqsort_spec_lemma3_aux p i xs
    aux3 = iqsort_spec_lemma1_aux p i xs
    aux4 = iqsort_spec_aux2 i (Cons p xs)

    step1 = iqsort_spec_lemma4 p i xs
    step2 = iqsort_spec_lemma3 p i xs
    step3 = undefined -- iqsort_spec_lemma1 p i xs

-- !OLD, before reframing iqsort_spec_lemma1 in the correct direction
-- ( refinesplus_equalprop
--     aux3
--     aux4
--     ( symmetry
--         (iqsort_spec_aux2 i (Cons p xs))
--         (iqsort_spec_lemma1_aux p i xs)
--         (iqsort_spec_lemma1 p i xs)
--     )
-- )
