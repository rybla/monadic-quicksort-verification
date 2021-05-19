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

{-@
ipartl_spec_steps5to6 ::
  (Equality (M (Natural, Natural)), Equality (M (Natural, Natural, Natural)), Equality (M (List Int, List Int, List Int))) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  EqualProp (M (Natural, Natural))
    {ipartl_spec_step5 p i x xs ys zs}
    {ipartl_spec_step6 p i x xs ys zs}
@-}
ipartl_spec_steps5to6 :: (Equality (M (Natural, Natural)), Equality (M (Natural, Natural, Natural)), Equality (M (List Int, List Int, List Int))) => Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps5to6 = undefined -- TODO

{-
  ipartl_spec_step5 p i x xs ys zs
  -- defn ipartl_spec_step5
  writeList (S (i + length ys + length zs)) xs >>
    dispatch x p (ys, zs, xs) >>=
      ipartl_spec_step5_aux p i
  --
  writeList (S (i + length ys + length zs)) xs >>
    dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
      writeList i (ys' ++ zs') >>
        ipartl p i (length ys', length zs', length xs)
  --
  undefined -- TODO
  --
  dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
    writeList i (ys' ++ zs') >>
      writeList (i + length (ys' ++ zs')) xs >>
        ipartl p i (length ys', length zs', length xs)
  -- defn ipartl_spec_step6_aux
  dispatch x p (ys, zs, xs) >>=
    ipartl_spec_step6_aux p i
  -- defn ipartl_spec_step6
  ipartl_spec_step6 p i x xs ys zs

additionally, need some sort of lemma like this?

  m1 >> m2 >>= \x -> k1 x >> k2 x
  m2 >>= \x -> k1 x >> m1 >> k2 x

  -- m1' is like m1, but without the S
-}

-- uses:
-- - defn of `dispatch`
-- - function calls distribute into `if`
-- - `permute_preserves_length`
-- - commutativity
-- - [ref 9]
{-@
ipartl_spec_steps4to7 ::
  (Equality (M (Natural, Natural)), Equality (M (Natural, Natural, Natural)), Equality (M (List Int, List Int, List Int))) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step4 p i x xs ys zs}
    {ipartl_spec_step7 p i x xs ys zs}
@-}
ipartl_spec_steps4to7 :: (Equality (M (Natural, Natural)), Equality (M (Natural, Natural, Natural)), Equality (M (List Int, List Int, List Int))) => Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps4to7 p i x xs ys zs = undefined

{- -- * correct
  (refinesplus_equalprop (ipartl_spec_step4 p i x xs ys zs) (ipartl_spec_step7 p i x xs ys zs))
    [eqpropchain|
        ipartl_spec_step4 p i x xs ys zs
      %==
        ipartl_spec_step5 p i x xs ys zs
          %by undefined %-- TODO: either this is wrong: ipartl_spec_steps4to5 p i x xs ys zs
      %==
        ipartl_spec_step6 p i x xs ys zs
          %by undefined %-- TODO: or this is wrong: ipartl_spec_steps5to6 p i x xs ys zs
      %==
        ipartl_spec_step7 p i x xs ys zs
          %by ipartl_spec_steps6to7 p i x xs ys zs
    |]
-}

{- -- * correct
  (refinesplus_equalprop (ipartl_spec_step4 p i x xs ys zs) (ipartl_spec_step7 p i x xs ys zs))
    [eqpropchain|
        ipartl_spec_step4 p i x xs ys zs

      %==
        undefined

      %{-

        %-- step4
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then
              ipartl_spec_lemma2_aux2 p i x xs ys zs
            else
              ipartl_spec_lemma1_aux2 p i x xs ys zs

        %by %reflexivity

      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then ipartl_spec_steps4to7_lemma1_aux2 p i x xs ys zs
            else ipartl_spec_lemma1_aux2 p i x xs ys zs

          %by undefined
          %[- -- ! LH reject
          %by %rewrite ipartl_spec_lemma2_aux2 p i x xs ys zs
                  %to ipartl_spec_steps4to7_lemma1_aux2 p i x xs ys zs
          %by ipartl_spec_steps4to7_lemma1 p i x xs ys zs
          -]%

      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then ipartl_spec_steps4to7_lemma1_aux2 p i x xs ys zs
            else ipartl_spec_steps4to7_lemma2_aux2 p i x xs ys zs

          %by %rewrite ipartl_spec_lemma1_aux2 p i x xs ys zs
                   %to ipartl_spec_steps4to7_lemma2_aux2 p i x xs ys zs
          %by ipartl_spec_steps4to7_lemma2 p i x xs ys zs

      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then
              permute zs >>=
                dispatch_aux1 x xs ys >>=
                  ipartl_spec_steps4to7_lemma1_aux2_aux p i
            else ipartl_spec_steps4to7_lemma2_aux2 p i x xs ys zs

          %by %rewrite ipartl_spec_steps4to7_lemma1_aux2 p i x xs ys zs
                   %to permute zs >>= dispatch_aux1 x xs ys >>= ipartl_spec_steps4to7_lemma1_aux2_aux p i
          %by %reflexivity

      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then
              permute zs >>=
                dispatch_aux1 x xs ys >>= \(ys', zs', xs) ->
                  writeList i (ys' ++ zs') >>
                    ipartl p i (length ys', length zs', length xs)
            else ipartl_spec_steps4to7_lemma2_aux2 p i x xs ys zs

          %by %rewrite ipartl_spec_steps4to7_lemma1_aux2_aux p i
                   %to \(ys', zs', xs) -> writeList i (ys' ++ zs') >> ipartl p i (length ys', length zs', length xs)
          %by %reflexivity

      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then
              permute zs >>=
                dispatch_aux1 x xs ys >>= \(ys', zs', xs) ->
                  writeList i (ys' ++ zs') >>
                    ipartl p i (length ys', length zs', length xs)
            else
              permute (zs ++ Cons x Nil) >>=
                dispatch_aux2 xs ys >>=
                  ipartl_spec_step5_aux p i

          %by %rewrite ipartl_spec_steps4to7_lemma2_aux2 p i x xs ys zs
                   %to permute (zs ++ Cons x Nil) >>= dispatch_aux2 xs ys >>= ipartl_spec_step5_aux p i
          %by %reflexivity

      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then
              permute zs >>=
                dispatch_aux1 x xs ys >>= \(ys', zs', xs) ->
                  writeList i (ys' ++ zs') >>
                    ipartl p i (length ys', length zs', length xs)
            else
              permute (zs ++ Cons x Nil) >>=
                dispatch_aux2 xs ys >>= \(ys', zs', xs) ->
                  writeList i (ys' ++ zs') >>
                    ipartl p i (length ys', length zs', length xs)

          %by %rewrite ipartl_spec_step5_aux p i
                   %to  \(ys', zs', xs) -> writeList i (ys' ++ zs') >> ipartl p i (length ys', length zs', length xs)
          %by %reflexivity

      %==
        writeList (S (i + length ys + length zs)) xs >>
          ( if x <= p
              then permute zs >>= dispatch_aux1 x xs ys
              else permute (zs ++ Cons x Nil) >>= dispatch_aux2 xs ys
          ) >>= \(ys', zs', xs) ->
            writeList i (ys' ++ zs') >>
              ipartl p i (length ys', length zs', length xs)

          %by %symmetry
          %by bind_if
                (x <= p)
                (permute zs >>= dispatch_aux1 x xs ys)
                (permute (zs ++ Cons x Nil) >>= dispatch_aux2 xs ys)
                (\(ys', zs', xs) -> writeList i (ys' ++ zs') >> ipartl p i (length ys', length zs', length xs))

      -}%
      %==
        %-- step5
        writeList (S (i + length ys + length zs)) xs >>
          dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
            writeList i (ys' ++ zs') >>
              ipartl p i (length ys', length zs', length xs)

          %by %rewrite if x <= p then permute zs >>= dispatch_aux1 x xs ys else permute (zs ++ Cons x Nil) >>= dispatch_aux2 xs ys
                   %to dispatch x p (ys, zs, xs)
          %by %symmetry
          %by %reflexivity

      %==
        %-- step6
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i (ys' ++ zs') >>
            writeList (i + length (ys' ++ zs')) xs >>
              ipartl p i (length ys', length zs', length xs)

          %by undefined -- TODO: not sure...

      %==
        dispatch x p (ys, zs, xs) >>=
          ipartl_spec_steps4to7_lemma3_aux1 p i

        %by %rewrite \(ys', zs', xs) -> writeList i (ys' ++ zs') >> writeList (i + length (ys' ++ zs')) xs >> ipartl p i (length ys', length zs', length xs)
                 %to ipartl_spec_steps4to7_lemma3_aux1 p i
        %by %extend (ys', zs', xs)
        %by %symmetry
        %by %reflexivity

      %==
        dispatch x p (ys, zs, xs) >>=
          ipartl_spec_steps4to7_lemma3_aux2 p i

          %by %rewrite ipartl_spec_steps4to7_lemma3_aux1 p i
                   %to ipartl_spec_steps4to7_lemma3_aux2 p i
          %by %extend (ys', zs', xs)
          %by ipartl_spec_steps4to7_lemma3 p i (ys', zs', xs)

      %==
        dispatch x p (ys, zs, xs) >>=
          ( writeListToLength3 i >=>
            ipartl p i )

        %by %rewrite ipartl_spec_steps4to7_lemma3_aux2 p i
                 %to (writeListToLength3 i >=> ipartl p i)
        %by %extend (ys', zs', xs)
        %by %reflexivity

      %==
        %-- step7
        dispatch x p (ys, zs, xs) >>=
          writeListToLength3 i >>=
            ipartl p i

          %by %symmetry
          %by bind_associativity (dispatch x p (ys, zs, xs)) (writeListToLength3 i) (ipartl p i)

      %==
        ipartl_spec_step7 p i x xs ys zs
          %by %symmetry
          %by %reflexivity
    |]
-}
