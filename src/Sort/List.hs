{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Sort.List where

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
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (++), (>>), (>>=))

{-
## Slowsort
-}

{-@ reflect slowsort @-}
slowsort :: List Int -> M (List Int)
slowsort = permute >=> guardBy sorted

{-@ reflect sorted @-}
sorted :: List Int -> Bool
sorted Nil = True
sorted (Cons x xs) = all (leq x) xs && sorted xs

-- [ref] display 5
{-@ automatic-instances sorted_middle @-}
{-@
sorted_middle ::
  ys:List Int -> x:Int -> zs:List Int ->
  {sorted (append ys (append (Cons x Nil) zs)) <=>
   sorted ys && sorted zs && all (geq x) ys && all (leq x) zs}
@-}
sorted_middle :: List Int -> Int -> List Int -> Proof
sorted_middle Nil x zs = ()
sorted_middle (Cons y ys) x zs = undefined

-- TODO: prove termination?
{-@ lazy permute @-}
{-@ reflect permute @-}
permute :: List a -> M (List a)
permute Nil = pure Nil
permute (Cons x xs) =
  split xs >>= \(ys, zs) ->
    liftM2 (\ys' zs' -> ys' ++ Cons x Nil ++ zs') (permute ys) (permute zs)

{-@ reflect split @-}
split :: List a -> M (List a, List a)
split Nil = pure (Nil, Nil)
split (Cons x xs) =
  split xs >>= \(ys, zs) ->
    pure (Cons x ys, zs) <+> pure (ys, Cons x zs)

{-
## Divide-and-Conquer
-}

-- [ref] divide and conquer equation chain
{-@ reflect divide_and_conquer_lemma1_aux @-}
divide_and_conquer_lemma1_aux :: Int -> List Int -> M (List Int)
divide_and_conquer_lemma1_aux x xs =
  split xs
    >>= \(ys, zs) ->
      guard (all (leq x) ys && all (geq x) zs)
        >> (permute ys >>= guardBy sorted)
          >>= \ys' ->
            (permute zs >>= guardBy sorted)
              >>= \zs' ->
                pure (ys' ++ Cons x Nil ++ zs')

{-@
divide_and_conquer_lemma1 ::
  Equality (M (List Int)) =>
  x:Int -> xs:List Int ->
  EqualProp (M (List Int))
    {slowsort (Cons x xs)}
    {divide_and_conquer_lemma1_aux x xs}
@-}
divide_and_conquer_lemma1 :: Equality (M (List Int)) => Int -> List Int -> EqualityProp (M (List Int))
divide_and_conquer_lemma1 x xs =
  [eqpropchain|
      slowsort (Cons x xs)
    %==
      (permute >=> guardBy sorted) (Cons x xs)
    %==
      permute (Cons x xs) >>= guardBy sorted
        %by undefined
        %-- TODO: why?
        %-- def of (>=>)
    %==
      (split xs >>= \(ys, zs) ->
          liftM2 (\ys' zs' -> ys' ++ Cons x Nil ++ zs') (permute ys) (permute zs))
      >>= guardBy sorted
        %-- def of permute
    %==
      (split xs >>= \(ys, zs) ->
        permute ys >>= \ys' ->
          permute zs >>= \zs' ->
            pure (ys' ++ Cons x Nil ++ zs'))
      >>= guardBy sorted
    %==
      split xs >>= \(ys, zs) ->
        permute ys >>= \ys' ->
          permute zs >>= \zs' ->
            pure (ys' ++ Cons x Nil ++ zs') >>= guardBy sorted
      %by undefined
      %-- TODO: several bind_associativity steps
    %==
      split xs >>= \(ys, zs) ->
        permute ys >>= \ys' ->
          permute zs >>= \zs' ->
            guardBy sorted (ys' ++ Cons x Nil ++ zs')
        %by undefined
        %{-
        %by %rewrite \(ys, zs) -> permute ys >>= \ys' -> permute zs >>= \zs' -> pure (ys' ++ Cons x Nil ++ zs') >>= guardBy sorted
                %to \(ys, zs) -> permute ys >>= \ys' -> permute zs >>= \zs' -> guardBy sorted (ys' ++ Cons x Nil ++ zs')
        %by %extend (ys, zs)
        %by %rewrite \ys' -> permute zs >>= \zs' -> pure (ys' ++ Cons x Nil ++ zs') >>= guardBy sorted
                %to \ys' -> permute zs >>= \zs' -> guardBy sorted (ys' ++ Cons x Nil ++ zs')
        %by %extend ys'
        %by %rewrite \zs' -> pure (ys' ++ Cons x Nil ++ zs') >>= guardBy sorted
                %to \zs' -> guardBy sorted (ys' ++ Cons x Nil ++ zs')
        %by %extend zs' 
        %by bind_identity_left (ys' ++ Cons x Nil ++ zs') (guardBy sorted)
        -}%
    %==
      split xs >>= \(ys, zs) ->
        permute ys >>= \ys' -> 
          permute zs >>= \zs' ->
            guard (sorted (ys' ++ Cons x Nil ++ zs')) >>
              pure (ys' ++ Cons x Nil ++ zs')
        %by undefined
        %{-
        %by %rewrite \(ys, zs) -> permute ys >>= \ys' -> permute zs >>= \zs' -> guardBy sorted (ys' ++ Cons x Nil ++ zs')
                 %to \(ys, zs) -> permute ys >>= \ys' ->  permute zs >>= \zs' -> guard (sorted (ys' ++ Cons x Nil ++ zs')) >> pure (ys' ++ Cons x Nil ++ zs')
        %by %extend (ys, zs)
        %by %rewrite \ys' -> permute zs >>= \zs' -> guardBy sorted (ys' ++ Cons x Nil ++ zs')
                 %to \ys' -> permute zs >>= \zs' -> guard (sorted (ys' ++ Cons x Nil ++ zs')) >> pure (ys' ++ Cons x Nil ++ zs')
        %by %extend ys' 
        %by %rewrite \zs' -> guardBy sorted (ys' ++ Cons x Nil ++ zs')
                 %to \zs' -> guard (sorted (ys' ++ Cons x Nil ++ zs')) >> pure (ys' ++ Cons x Nil ++ zs')
        %by %reflexivity
        -}%
    %==
      split xs >>= \(ys, zs) ->
        permute ys >>= \ys' -> 
          permute zs >>= \zs' ->
            guard (sorted ys' && sorted zs' && all (geq x) ys' && all (leq x) zs') >>
              pure (ys' ++ Cons x Nil ++ zs')
        %by undefined
        %{-
        %by %rewrite \(ys, zs) -> permute ys >>= \ys' -> permute zs >>= \zs' -> guard (sorted (ys' ++ Cons x Nil ++ zs')) >> pure (ys' ++ Cons x Nil ++ zs')
                 %to \(ys, zs) -> permute ys >>= \ys' ->  permute zs >>= \zs' -> guard (sorted ys' && sorted zs' && all (geq x) ys' && all (leq x) zs') >> pure (ys' ++ Cons x Nil ++ zs')
        %by %extend (ys, zs)
        %by %rewrite \ys' -> permute zs >>= \zs' -> guard (sorted (ys' ++ Cons x Nil ++ zs')) >> pure (ys' ++ Cons x Nil ++ zs')
                 %to \ys' -> permute zs >>= \zs' -> guard (sorted ys' && sorted zs' && all (geq x) ys' && all (leq x) zs') >> pure (ys' ++ Cons x Nil ++ zs')
        %by %extend ys' 
        %by %rewrite \zs' -> guard (sorted (ys' ++ Cons x Nil ++ zs')) >> pure (ys' ++ Cons x Nil ++ zs')
                 %to \zs' -> guard (sorted ys' && sorted zs' && all (geq x) ys' && all (leq x) zs') >> pure (ys' ++ Cons x Nil ++ zs')
        %by %extend zs'
        %by %smt 
        %by sorted_middle ys' x zs' 
        -}%
    %==
      split xs >>= \(ys, zs) ->
        permute ys >>= \ys' ->
          permute zs >>= \zs' ->
            (guard (sorted ys') >> guard (sorted zs') >> guard (all (geq x) ys' && all (leq x) zs')) >>
              pure (ys' ++ Cons x Nil ++ zs')
        %by undefined 
        %-- TODO: several guard_and steps 
    %==
      split xs >>= \(ys, zs) ->
        permute ys >>= \ys' ->
          permute zs >>= \zs' ->
            guard (all (geq x) ys' && all (leq x) zs') >>
              guard (sorted ys') >>
              guard (sorted zs') >>
              pure (ys' ++ Cons x Nil ++ zs')
        %by undefined
        %-- TODO: rearrange the sequences guards 
    %==
      split xs >>= \(ys, zs) ->
        guard (all (leq x) ys && all (geq x) zs) >>
          (permute ys >>= guardBy sorted) >>= \ys' ->
            (permute zs >>= guardBy sorted) >>= \zs' ->
                pure (ys' ++ Cons x Nil ++ zs')
        %by undefined
        %-- TODO
    %==
      divide_and_conquer_lemma1_aux x xs
  |]

{-@ reflect divide_and_conquer_aux @-}
divide_and_conquer_aux :: Int -> List Int -> M (List Int)
divide_and_conquer_aux x xs =
  pure (partition x xs)
    >>= \(ys, zs) ->
      slowsort ys
        >>= \ys' ->
          slowsort zs
            >>= \zs' ->
              pure (ys' ++ Cons x Nil ++ zs')

-- TODO: prove
-- [ref] display 8
{-@
divide_and_conquer ::
  Equality (M (List Int, List Int)) =>
  x:Int -> xs:List Int ->
  RefinesPlus (List Int, List Int)
    {divide_and_conquer_aux x xs}
    {slowsort (Cons x xs)}
@-}
divide_and_conquer :: Int -> List Int -> EqualityProp (M (List Int, List Int))
divide_and_conquer = undefined

{-@ reflect partition @-}
partition :: Int -> List Int -> (List Int, List Int)
partition x' Nil = (Nil, Nil)
partition x' (Cons x xs) =
  if leq x x' then (Cons x ys, zs) else (ys, Cons x zs)
  where
    ys = proj1 (partition x' xs)
    zs = proj2 (partition x' xs)

{-@ reflect divide_and_conquer_lemma2_aux @-}
divide_and_conquer_lemma2_aux :: Int -> List Int -> M (List Int, List Int)
divide_and_conquer_lemma2_aux x xs =
  split xs >>= guardBy (\(ys, zs) -> all (leq x) ys && all (geq x) zs)

-- TODO: migrate proof from old Sort.List
{-@
divide_and_conquer_lemma2 ::
  Equality (M (List Int, List Int)) =>
  x:Int ->
  xs:List Int ->
  RefinesPlus (List Int, List Int)
    {pure (partition x xs)}
    {divide_and_conquer_lemma2_aux x xs}
@-}
divide_and_conquer_lemma2 :: Equality (M (List Int, List Int)) => Int -> List Int -> EqualityProp (M (List Int, List Int))
divide_and_conquer_lemma2 = undefined

{-
## Quicksort
-}

{-@ reflect quicksort @-}
quicksort :: List Int -> List Int
quicksort Nil = Nil
quicksort (Cons x xs) = quicksort ys ++ Cons x Nil ++ quicksort zs
  where
    ys = proj1 (partition x xs)
    zs = proj2 (partition x xs)

-- TODO: migrate proof from old Sort.Test
{-@
quicksort_refines_slowsort ::
  Equality (M (List Int)) =>
  xs:List Int ->
  RefinesPlus (List Int)
    {compose pure quicksort xs}
    {slowsort xs}
@-}
quicksort_refines_slowsort :: Equality (M (List Int)) => List Int -> EqualityProp (M (List Int))
quicksort_refines_slowsort = undefined
