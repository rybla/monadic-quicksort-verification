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
import Sort.List
import Prelude hiding (all, concat, foldl, length, pure, read, readList, seq)

--
-- # IPartl (in-place partl)
--

--
-- ## Functions
--

--
-- partl (not tail-recursive)
--

-- {-@ reflect partl @-}
-- partl :: Int -> (List Int, List Int, List Int) -> (List Int, List Int)
-- partl p (ys, zs, xs) =
--   let (us, vs) = partition p xs
--    in (concat ys us, concat zs vs)

--
-- partl (tail-recursive)
--

-- TODO: still fails termination checking??
{-@ lazy permute @-}
{-@ reflect partl @-}
partl :: Int -> (List Int, List Int, List Int) -> (List Int, List Int)
partl p (ys, zs, Nil) = (ys, zs)
partl p (ys, zs, Cons x xs) =
  if leq x p
    then partl p (concat ys (single x), zs, xs)
    else partl p (ys, concat zs (single x), xs)

--
-- partl'
--

{-@ lazy partl' @-}
{-@ reflect partl' @-}
partl' :: Int -> (List Int, List Int, List Int) -> M (List Int, List Int)
partl' p (ys, zs, Nil) = pure (ys, zs)
partl' p (ys, zs, Cons x xs) = bind (dispatch x p (ys, zs, xs)) (partl' p)

{-@ reflect dispatch @-}
dispatch :: Int -> Int -> (List Int, List Int, List Int) -> M (List Int, List Int, List Int)
dispatch x p (ys, zs, xs) =
  if leq x p
    then bind (permute zs) (dispatch_aux1 x xs ys)
    else bind (permute (snoc zs x)) (dispatch_aux2 xs ys)

{-@ reflect dispatch_aux1 @-}
dispatch_aux1 :: Int -> List Int -> List Int -> List Int -> M (List Int, List Int, List Int)
dispatch_aux1 x xs ys zs' = pure (snoc ys x, zs', xs)

{-@ reflect dispatch_aux2 @-}
dispatch_aux2 :: List Int -> List Int -> List Int -> M (List Int, List Int, List Int)
dispatch_aux2 xs ys zs' = pure (ys, zs', xs)

--
-- ipartl
--

{-@ lazy ipartl @-}
{-@ reflect ipartl @-}
ipartl :: Natural -> Int -> (Natural, Natural, Natural) -> M (Natural, Natural)
ipartl i p (ny, nz, Z) = pure (ny, nz)
ipartl i p (ny, nz, S k) =
  bind
    (read (add (add i ny) nz))
    (ipartl_aux i p ny nz k)

{-@ lazy ipartl_aux @-}
{-@ reflect ipartl_aux @-}
ipartl_aux :: Natural -> Int -> Natural -> Natural -> Natural -> Int -> M (Natural, Natural)
ipartl_aux i p ny nz k x' =
  if leq x' p
    then
      seq
        (swap (add i ny) (add (add i ny) nz))
        (ipartl i p (S ny, nz, k))
    else ipartl i p (ny, S nz, k)

--
-- ## Proofs
--

--
-- ipartl_spec_lemma1
--

-- ipartl_spec_lemma1_aux1

{-@ reflect ipartl_spec_lemma1_aux1 @-}
ipartl_spec_lemma1_aux1 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma1_aux1 i p x xs ys zs =
  seq
    (writeList (add (add (add i (length ys)) (length zs)) one) xs)
    ( if leq x p
        then bind (permute zs) (ipartl_spec_lemma1_aux1_aux1 i p x xs ys)
        else bind (permute (concat zs (single x))) (ipartl_spec_lemma1_aux1_aux2 i p x xs ys)
    )

{-@ reflect ipartl_spec_lemma1_aux1_aux1 @-}
ipartl_spec_lemma1_aux1_aux1 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma1_aux1_aux1 i p x xs ys zs' =
  seq
    (writeList i (concat (concat ys (single x)) zs'))
    (ipartl i p (S (length ys), length zs', length xs))

{-@ reflect ipartl_spec_lemma1_aux1_aux2 @-}
ipartl_spec_lemma1_aux1_aux2 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma1_aux1_aux2 i p x xs ys zs' =
  seq
    (writeList i (concat ys zs'))
    (ipartl i p (length ys, length zs', length xs))

-- ipartl_spec_lemma1

{-@
ipartl_spec_lemma1 ::
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_lemma1_aux1 i p       x xs  ys zs}
    {ipartl_spec_aux2        i p (Cons x xs) ys zs}
@-}
ipartl_spec_lemma1 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1 i p x xs ys zs = undefined -- TODO

-- ipartl_spec_lemma1 steps

{-@ reflect ipartl_spec_lemma1_aux1A @-}
ipartl_spec_lemma1_aux1A :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma1_aux1A i p x xs ys zs =
  seq
    (writeList (S (add (add i (length ys)) (length zs))) xs)
    ( bind
        (dispatch x p (ys, zs, xs))
        (ipartl_spec_lemma1_aux1A_aux i p x)
    )

{-@ reflect ipartl_spec_lemma1_aux1A_aux @-}
ipartl_spec_lemma1_aux1A_aux :: Natural -> Int -> Int -> (List Int, List Int, List Int) -> M (Natural, Natural)
ipartl_spec_lemma1_aux1A_aux i p x (ys', zs', xs) =
  seq
    (writeList i (concat ys' zs'))
    (ipartl i p (length ys', length zs', length xs))

{-@ reflect ipartl_spec_lemma1_aux1B @-}
ipartl_spec_lemma1_aux1B :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma1_aux1B i p x xs ys zs = ipartl_spec_lemma1_aux1 i p x xs ys zs

{-@ reflect ipartl_spec_lemma1_step2 @-}
ipartl_spec_lemma1_step2 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma1_step2 i p x xs ys zs =
  bind
    (dispatch x p (ys, zs, xs))
    (ipartl_spec_lemma1_step2_aux i p x)

{-@ reflect ipartl_spec_lemma1_step2_aux @-}
ipartl_spec_lemma1_step2_aux :: Natural -> Int -> Int -> (List Int, List Int, List Int) -> M (Natural, Natural)
ipartl_spec_lemma1_step2_aux i p x (ys', zs', xs) =
  seq
    ( seq
        (writeList i (concat ys' zs'))
        (writeList (add i (length (concat ys' zs'))) xs)
    )
    (ipartl i p (length ys', length zs', length xs))

{-@ reflect ipartl_spec_lemma1_step3 @-}
ipartl_spec_lemma1_step3 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma1_step3 i p x xs ys zs =
  bind
    ( bind
        (dispatch x p (ys, zs, xs))
        (partl' p)
    )
    (writeListToLength2 i)

{-@
ipartl_spec_lemma1_aux1to2 ::
  Equality (M (Natural, Natural)) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_lemma1_aux1 i p x xs ys zs}
    {ipartl_spec_lemma1_step2 i p x xs ys zs}
@-}
ipartl_spec_lemma1_aux1to2 :: Equality (M (Natural, Natural)) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_aux1to2 i p x xs ys zs =
  (refinesplus_equalprop (ipartl_spec_lemma1_aux1 i p x xs ys zs) (ipartl_spec_lemma1_step2 i p x xs ys zs))
    [eqp| ipartl_spec_lemma1_aux1 i p x xs ys zs
      
      %== ipartl_spec_lemma1_aux1A i p x xs ys zs
            %by ipartl_spec_lemma1_aux1to1A i p x xs ys zs
      
      %== ipartl_spec_lemma1_aux1B i p x xs ys zs
            %by ipartl_spec_lemma1_aux1Ato1B i p x xs ys zs
      
      %== ipartl_spec_lemma1_step2 i p x xs ys zs
            %by ipartl_spec_lemma1_aux1Bto2 i p x xs ys zs
    |]

{-@
ipartl_spec_lemma1_aux1to1A ::
  Equality (M (Natural, Natural)) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  EqualProp (M (Natural, Natural))
    {ipartl_spec_lemma1_aux1  i p x xs ys zs}
    {ipartl_spec_lemma1_aux1A i p x xs ys zs}
@-}
ipartl_spec_lemma1_aux1to1A :: Equality (M (Natural, Natural)) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_aux1to1A i p x xs yz zs = undefined -- TODO

{-@
ipartl_spec_lemma1_aux1Ato1B ::
  Equality (M (Natural, Natural)) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  EqualProp (M (Natural, Natural))
    {ipartl_spec_lemma1_aux1A i p x xs ys zs}
    {ipartl_spec_lemma1_aux1B i p x xs ys zs}
@-}
ipartl_spec_lemma1_aux1Ato1B :: Equality (M (Natural, Natural)) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_aux1Ato1B i p x xs yz zs = undefined -- TODO

{-@
ipartl_spec_lemma1_aux1Bto2 ::
  Equality (M (Natural, Natural)) =>
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  EqualProp (M (Natural, Natural))
    {ipartl_spec_lemma1_aux1B i p x xs ys zs}
    {ipartl_spec_lemma1_step2  i p x xs ys zs}
@-}
ipartl_spec_lemma1_aux1Bto2 :: Equality (M (Natural, Natural)) => Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_aux1Bto2 i p x xs yz zs = undefined -- TODO

{-@
ipartl_spec_lemma1_step2to3 ::
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_lemma1_step2 i p x xs ys zs}
    {ipartl_spec_lemma1_step3 i p x xs ys zs}
@-}
ipartl_spec_lemma1_step2to3 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_step2to3 = undefined -- TODO

{-@
ipartl_spec_lemma1_step3to4 ::
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_lemma1_step3 i p x xs ys zs}
    {ipartl_spec_aux2 i p (Cons x xs) ys zs}
@-}
ipartl_spec_lemma1_step3to4 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma1_step3to4 = undefined -- TODO

--
-- ipartl_spec_lemma2
--

{-@ reflect ipartl_spec_lemma2_aux1 @-}
ipartl_spec_lemma2_aux1 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma2_aux1 i p x xs ys zs =
  seq
    (writeList i (concat (concat ys zs) (single x)))
    (ipartl i p (length ys, S (length zs), length xs))

{-@ reflect ipartl_spec_lemma2_aux2 @-}
ipartl_spec_lemma2_aux2 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma2_aux2 i p x xs ys zs =
  bind
    (permute (snoc zs x))
    (ipartl_spec_lemma2_aux2_aux i p x xs ys)

{-@ reflect ipartl_spec_lemma2_aux2_aux @-}
ipartl_spec_lemma2_aux2_aux :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma2_aux2_aux i p x xs ys zs' =
  seq
    (writeList i (concat ys zs'))
    (ipartl i p (length ys, length zs', length xs))

{-@
ipartl_spec_lemma2 ::
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus ((Natural, Natural))
    {ipartl_spec_lemma2_aux1 i p x xs ys zs}
    {ipartl_spec_lemma2_aux2 i p x xs ys zs}
@-}
ipartl_spec_lemma2 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_lemma2 i p x xs ys zs = undefined -- TODO

--
-- ipartl_spec_lemma3
--

{-@ reflect ipartl_spec_lemma3_aux1 @-}
ipartl_spec_lemma3_aux1 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M ()
ipartl_spec_lemma3_aux1 i p x xs ys zs =
  seq
    (writeList i (concat (concat ys zs) (single x)))
    (swap (add i (length ys)) (add (add i (length ys)) (length zs)))

{-@ reflect ipartl_spec_lemma3_aux2 @-}
ipartl_spec_lemma3_aux2 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M ()
ipartl_spec_lemma3_aux2 i p x xs ys zs =
  bind
    (permute zs)
    (ipartl_spec_lemma3_aux2_aux i p x xs ys)

{-@ reflect ipartl_spec_lemma3_aux2_aux @-}
ipartl_spec_lemma3_aux2_aux :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M ()
ipartl_spec_lemma3_aux2_aux i p x xs ys zs' =
  writeList i (sandwich ys x zs')

{-@
ipartl_spec_lemma3 ::
  i:Natural -> p:Int -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (())
    {ipartl_spec_lemma3_aux1 i p x xs ys zs}
    {ipartl_spec_lemma3_aux2 i p x xs ys zs}
@-}
ipartl_spec_lemma3 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> EqualityProp (M ())
ipartl_spec_lemma3 i p x xs ys zs = undefined -- TODO

--
-- ipartl_spec_lemma4
--

{-@ reflect ipartl_spec_lemma4_aux1@-}
ipartl_spec_lemma4_aux1 :: Natural -> Int -> List Int -> M ()
ipartl_spec_lemma4_aux1 i x zs =
  seq
    (writeList i (snoc zs x))
    (swap i (add i (length zs)))

{-@ reflect ipartl_spec_lemma4_aux2 @-}
ipartl_spec_lemma4_aux2 :: Natural -> Int -> List Int -> M ()
ipartl_spec_lemma4_aux2 i x zs =
  bind (permute zs) (ipartl_spec_lemma4_aux2_aux i x)

{-@ reflect ipartl_spec_lemma4_aux2_aux @-}
ipartl_spec_lemma4_aux2_aux :: Natural -> Int -> List Int -> M ()
ipartl_spec_lemma4_aux2_aux i x zs' =
  writeList i (Cons x zs')

{-@
ipartl_spec_lemma4 ::
  i:Natural -> x:Int -> zs:List Int ->
  RefinesPlus (())
    {ipartl_spec_lemma4_aux1 i x zs}
    {ipartl_spec_lemma4_aux2 i x zs}
@-}
ipartl_spec_lemma4 :: Natural -> Int -> List Int -> EqualityProp (M ())
ipartl_spec_lemma4 i x zs = undefined -- TODO

-- ! INSERT ipartl_spec_lemma5

--
-- ipartl_spec_lemma6
--

-- ipartl_spec_lemma6_aux1

{-@ reflect ipartl_spec_lemma6_aux2 @-}
ipartl_spec_lemma6_aux2 :: Natural -> Int -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_lemma6_aux2 i p x xs ys zs =
  seq
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
        %by undefined
        %-- TODO: Liquid Type Mismatch
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

      %== ipartl_spec_lemma6_aux2 i p x xs ys zs
            
        %by %symmetry
        %by %reflexivity
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

--
-- ipartl_spec
--

{-@ reflect ipartl_spec_aux1 @-}
ipartl_spec_aux1 :: Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_aux1 i p xs ys zs =
  seq
    (writeList i (concat (concat ys zs) xs))
    (ipartl i p (length ys, length zs, length xs))

{-@ reflect ipartl_spec_aux2 @-}
ipartl_spec_aux2 :: Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_aux2 i p xs ys zs =
  bind
    (partl' p (ys, zs, xs))
    (writeListToLength2 i)

-- ! INSERT: ipartl_spec
