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

{-@ reflect ipartl_spec_steps_4_to_7_lemma2_aux2 @-}
ipartl_spec_steps_4_to_7_lemma2_aux2 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs =
  permute (zs ++ Cons x Nil)
    >>= dispatch_aux2 xs ys
    >>= ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i

{-@ reflect ipartl_spec_steps_4_to_7_lemma2_aux2_aux @-}
ipartl_spec_steps_4_to_7_lemma2_aux2_aux :: Int -> Natural -> (List Int, List Int, List Int) -> M (Natural, Natural)
ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i (ys', zs', xs) =
  writeList i (ys' ++ zs')
    >> ipartl p i (length ys', length zs', length xs)

{-@
ipartl_spec_steps_4_to_7_lemma2 ::
  (Equality (M (Natural, Natural)), Equality (M (List Int, List Int, List Int))) =>
    p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
    EqualProp (M (Natural, Natural))
      {ipartl_spec_lemma1_aux2 p i x xs ys zs}
      {ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs}
@-}
ipartl_spec_steps_4_to_7_lemma2 :: (Equality (M (Natural, Natural)), Equality (M (List Int, List Int, List Int))) => Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps_4_to_7_lemma2 p i x xs ys zs = undefined

{- -- * correct
  [eqpropchain|
      ipartl_spec_lemma1_aux2 p i x xs ys zs

    %==
      permute (zs ++ Cons x Nil) >>=
        ipartl_spec_lemma1_aux2_aux i p ys xs

    %==
      permute (zs ++ Cons x Nil) >>= \zs' ->
        writeList i (ys ++ zs') >>
          ipartl p i (length ys, length zs', length xs)

        %by undefined
        %{- -- TODO
        %by %rewrite ipartl_spec_lemma1_aux2_aux i p ys xs
                 %to \zs' -> writeList i (ys ++ zs') >> ipartl p i (length ys, length zs', length xs)
        %by %reflexivity
        -}%

    %==
      permute (zs ++ Cons x Nil) >>= \zs' ->
        ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i (ys, zs', xs)

        %by %rewrite \zs' -> writeList i (ys ++ zs') >> ipartl p i (length ys, length zs', length xs)
                 %to \zs' -> ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i (ys, zs', xs)
        %by %extend zs'
        %by %symmetry
        %by %reflexivity

    %==
      permute (zs ++ Cons x Nil) >>= \zs' ->
        (pure (ys, zs', xs) >>=
          ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i)

    %==
      permute (zs ++ Cons x Nil) >>= \zs' ->
        (dispatch_aux2 xs ys zs' >>=
          ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i)

        %by %rewrite \zs' -> (pure (ys, zs', xs) >>= ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i)
                 %to \zs' -> (dispatch_aux2 xs ys zs' >>= ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i)
        %by %extend zs'
        %by %rewrite pure (ys, zs', xs)
                 %to dispatch_aux2 xs ys zs'
        %by %symmetry
        %by %reflexivity

    %==
      permute (zs ++ Cons x Nil) >>= \zs' ->
        ( dispatch_aux2 xs ys >=>
          ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i)
        zs'

        %by %rewrite \zs' -> (dispatch_aux2 xs ys zs' >>= ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i)
                 %to \zs' -> (dispatch_aux2 xs ys >=> ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i) zs'
        %by %extend zs'
        %by %symmetry
        %by %reflexivity

    %==
      permute (zs ++ Cons x Nil) >>=
        ( dispatch_aux2 xs ys >=>
          ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i)

        %by %rewrite \zs' -> (dispatch_aux2 xs ys >=> ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i) zs'
                 %to (dispatch_aux2 xs ys >=> ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i)
        %by %extend zs'
        %by %reflexivity

    %==
      permute (zs ++ Cons x Nil) >>=
        dispatch_aux2 xs ys >>=
          ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i

        %by %symmetry
        %by bind_associativity (permute (zs ++ Cons x Nil)) (dispatch_aux2 xs ys) (ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i)

    %==
      ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs

        %by %symmetry
        %by %reflexivity
  |]
-}

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
ipartl_spec_steps_4_to_7 p i x xs ys zs =
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
            then ipartl_spec_steps_4_to_7_lemma1_aux2 p i x xs ys zs
            else ipartl_spec_lemma1_aux2 p i x xs ys zs

          %by undefined
          %[- -- TODO
          %by %rewrite ipartl_spec_lemma2_aux2 p i x xs ys zs
                  %to ipartl_spec_steps_4_to_7_lemma1_aux2 p i x xs ys zs
          %by ipartl_spec_steps_4_to_7_lemma1 p i x xs ys zs
          -]%

      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then ipartl_spec_steps_4_to_7_lemma1_aux2 p i x xs ys zs
            else ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs

          %by %rewrite ipartl_spec_lemma1_aux2 p i x xs ys zs
                   %to ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs
          %by ipartl_spec_steps_4_to_7_lemma2 p i x xs ys zs

      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then
              permute zs >>=
                dispatch_aux1 x xs ys >>=
                  ipartl_spec_steps_4_to_7_lemma1_aux2_aux p i
            else ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs
          
          %by %rewrite ipartl_spec_steps_4_to_7_lemma1_aux2 p i x xs ys zs
                   %to permute zs >>= dispatch_aux1 x xs ys >>= ipartl_spec_steps_4_to_7_lemma1_aux2_aux p i
          %by %reflexivity
      
      %==
        writeList (S (i + length ys + length zs)) xs >>
          if x <= p
            then
              permute zs >>=
                dispatch_aux1 x xs ys >>= \(ys', zs', xs) ->
                  writeList i (ys' ++ zs') >>
                    ipartl p i (length ys', length zs', length xs)
            else ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs

          %by %rewrite ipartl_spec_steps_4_to_7_lemma1_aux2_aux p i
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
                  ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i

          %by %rewrite ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs
                   %to permute (zs ++ Cons x Nil) >>= dispatch_aux2 xs ys >>= ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i
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
          
          %by %rewrite ipartl_spec_steps_4_to_7_lemma2_aux2_aux p i
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

          %by undefined -- TODO

      %==
        undefined
        %{- -- TODO: need to make these two the same somehow
        
          writeList i (ys' ++ zs') >>
            writeList (i + length (ys' ++ zs')) xs >>
          
        %==
        
          writeList i ys' >>
            writeList (add i (length ys')) zs' >>
          
        -}%

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i ys' >>
            writeList (add i (length ys')) zs' >>
              ipartl p i (length ys', length zs', length xs)

          %by undefined -- TODO

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          ( writeList i ys' >>
              ( writeList (add i (length ys')) zs' >>
                  ipartl p i (length ys', length zs', length xs)
              )
          )

          %by undefined -- TODO: seq_associativity4

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          ( writeList i ys' >>
              ( writeList (add i (length ys')) zs' >>= \() ->
                  ipartl p i (length ys', length zs', length xs)
              )
          )

          %by undefined -- TODO: defn (>>)

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i ys' >>= \() ->
            writeList (add i (length ys')) zs' >>= \() ->
              ipartl p i (length ys', length zs', length xs)
              
          %by undefined -- TODO: defn (>>)

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i ys' >>= \() ->
            writeList (add i (length ys')) zs' >>= \() ->
              pure (length ys', length zs', length xs) >>=
                  ipartl p i 
              
          %by undefined -- TODO: pure_bind

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i ys' >>= \() ->
            writeList (add i (length ys')) zs' >>= \() ->
              ( (\_ -> pure (length ys', length zs', length xs)) >=>
                  ipartl p i 
              ) ()

          %by undefined -- TODO: apply 

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i ys' >>= \() ->
            writeList (add i (length ys')) zs' >>=
              ( (\_ -> pure (length ys', length zs', length xs)) >=>
                  ipartl p i 
              )

          %by undefined -- TODO: eta-equivalence

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i ys' >>= \() ->
            ( (\_ -> writeList (add i (length ys')) zs') >=>
                ( (\_ -> pure (length ys', length zs', length xs)) >=>
                    ipartl p i 
                )
            ) ()

          %by undefined -- TODO: apply 

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i ys' >>=
            ( (\_ -> writeList (add i (length ys')) zs') >=>
                ( (\_ -> pure (length ys', length zs', length xs)) >=>
                    ipartl p i 
                )
            )

          %by undefined -- TODO: eta-equivalence

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i ys' >>=
            (\_ -> writeList (add i (length ys')) zs') >>=
              (\_ -> pure (length ys', length zs', length xs)) >>=
                ipartl p i
        
        %by undefined -- TODO: bind_associativity4

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i ys' >>=
            (\_ -> writeList (add i (length ys')) zs') >>
              pure (length ys', length zs', length xs) >>=
                ipartl p i
        
        %by undefined -- TODO: defn (>>)

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i ys' >> 
            writeList (add i (length ys')) zs' >>
              pure (length ys', length zs', length xs) >>=
                ipartl p i
        
        %by undefined -- TODO: defn (>>)

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeList i (ys' ++ zs') >>
            pure (length ys', length zs', length xs) >>=
              ipartl p i
        
        %by undefined -- TODO: writeList_append

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          writeListToLength3 i (ys', zs', xs) >>=
            ipartl p i
        
        %by undefined -- TODO: defn writeListToLength3

      %==
        dispatch x p (ys, zs, xs) >>= \(ys', zs', xs) ->
          ( writeListToLength3 i >=>
            ipartl p i
          ) (ys', zs', xs)
        
        %by undefined -- TODO: defn (>=>)

      %==
        dispatch x p (ys, zs, xs) >>=
          ( writeListToLength3 i >=>
            ipartl p i )
        
        %by undefined -- TODO: eta-equivalence

      %==
        %-- step7
        dispatch x p (ys, zs, xs) >>=
          writeListToLength3 i >>=
            ipartl p i

          %by undefined -- TODO: defn (>=>)

      %==
        ipartl_spec_step7 p i x xs ys zs
          %by %symmetry
          %by %reflexivity
    |]
