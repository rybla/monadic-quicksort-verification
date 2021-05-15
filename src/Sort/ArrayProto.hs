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

{-@ reflect ipartl_spec_steps_4_to_7_lemma2_aux @-}
ipartl_spec_steps_4_to_7_lemma2_aux :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_steps_4_to_7_lemma2_aux p i x xs ys zs =
  permute (zs ++ Cons x Nil)
    >>= dispatch_aux2 xs ys
    >>= \(ys', zs', xs) ->
      writeList i (ys' ++ zs')
        >> ipartl p i (length ys', length zs', length xs)

{-@
ipartl_spec_steps_4_to_7_lemma2 ::
  (Equality (M (Natural, Natural)), Equality (M (List Int, List Int, List Int))) =>
    p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
    EqualProp (M (Natural, Natural))
      {ipartl_spec_lemma1_aux2 p i x xs ys zs}
      {ipartl_spec_steps_4_to_7_lemma2_aux p i x xs ys zs}
@-}
ipartl_spec_steps_4_to_7_lemma2 :: (Equality (M (Natural, Natural)), Equality (M (List Int, List Int, List Int))) => Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps_4_to_7_lemma2 p i x xs ys zs = undefined -- TODO

-- uses:
-- - defn of `dispatch`
-- - function calls distribute into `if` -- TODO: define lemma
-- - `permute_preserves_length`
-- - commutativity
-- - [ref 9]
{-@
ipartl_spec_steps_4_to_7 ::
  (Equality (M (Natural, Natural)), Equality (M (List Int, List Int, List Int))) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step4 p i x xs ys zs}
    {ipartl_spec_step7 p i x xs ys zs}
@-}
ipartl_spec_steps_4_to_7 :: (Equality (M (Natural, Natural)), Equality (M (List Int, List Int, List Int))) => Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps_4_to_7 p i x xs ys zs = undefined

{-
  (refinesplus_equalprop (ipartl_spec_step4 p i x xs ys zs) (ipartl_spec_step7 p i x xs ys zs))
    [eqpropchain|
        ipartl_spec_step4 p i x xs ys zs
      %==
        %-- step4
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then
              ipartl_spec_lemma2_aux2 i x xs ys zs
            else
              ipartl_spec_lemma1_aux2 p i x xs ys zs
        %by %reflexivity
      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then ipartl_spec_steps_4_to_7_lemma1_aux2 p i x xs ys zs
            else ipartl_spec_lemma1_aux2 p i x xs ys zs
        %by %rewrite ipartl_spec_lemma2_aux2 i x ys zs
                 %to ipartl_spec_steps_4_to_7_lemma1_aux2 p i x xs ys zs
        %by ipartl_spec_steps_4_to_7_lemma1 p i x xs ys zs
      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then ipartl_spec_steps_4_to_7_lemma1_aux2 p i x xs ys zs
            else ipartl_spec_steps_4_to_7_lemma2_aux p i x xs ys zs
          %by %rewrite ipartl_spec_lemma1_aux2 p i x xs ys zs
                   %to ipartl_spec_steps_4_to_7_lemma2_aux p i x xs ys zs
          %by ipartl_spec_steps_4_to_7_lemma2 p i x xs ys zs
      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then
              permute zs
                >>= dispatch_aux1 x xs ys
                  >>= \(ys', zs', xs) ->
                    writeList i (ys' ++ zs')
                      >> ipartl p i (length ys', length zs', length xs)
            else
              permute (zs ++ Cons x Nil)
                >>= dispatch_aux2 xs ys
                  >>= \(ys', zs', xs) ->
                    writeList i (ys' ++ zs')
                      >> ipartl p i (length ys', length zs', length xs)
          %by undefined %-- TODO: unfold to lambdas, using auxs?
      %==
        writeList (S (i + length ys + length zs)) xs >>
          (if x <= p
            then permute zs >>= dispatch_aux1 x xs ys
            else permute (zs ++ Cons x Nil) >>= dispatch_aux2 xs ys)
            >>= \(ys', zs', xs) ->
              writeList i (ys' ++ zs') >>
                ipartl p i (length ys', length zs', length xs)
          %by undefined %-- TODO: function calls distribute into `if`
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
          %by undefined
      %==
        %-- step7
        dispatch x p (ys, zs, xs) >>=
          writeListToLength3 i >>=
            ipartl p i
          %by undefined
      %==
        ipartl_spec_step7 p i x xs ys zs
          %by %symmetry
          %by %reflexivity
    |]
-}
