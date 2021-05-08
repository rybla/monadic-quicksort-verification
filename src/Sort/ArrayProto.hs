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
