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
slowsort xs = permute xs >>= guardBy sorted

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
permute :: List Int -> M (List Int)
permute Nil = pure Nil
permute (Cons x xs) = split xs >>= permute_aux1 x

{-@ reflect permute_aux1 @-}
permute_aux1 :: Int -> (List Int, List Int) -> M (List Int)
permute_aux1 x (ys, zs) = liftM2 (permute_aux2 x) (permute ys) (permute zs)

{-@ reflect permute_aux2 @-}
permute_aux2 :: Int -> List Int -> List Int -> List Int
permute_aux2 x ys' zs' = ys' ++ Cons x Nil ++ zs'

{-@
permute_preserves_length ::
  Equality Int =>
  xs:List Int ->
  EqualProp Int
    {pure (length xs)}
    {liftM length (permute xs)}
@-}
permute_preserves_length :: Equality Int => List Int -> EqualityProp Int
permute_preserves_length xs = undefined -- TODO

{-@ reflect split @-}
split :: List Int -> M (List Int, List Int)
split Nil = pure (Nil, Nil)
split (Cons x xs) = split xs >>= split_aux x

{-- TODO
I've found that I needed to un-lambda some functions for
`divide_and_conquer_lemma2` to work. maybe there are others I need to do this to
as well. it seems to come up when I am for some reason unable to unfold a
definition (where the definition has lambdas in it).
-}
{-@ reflect split_aux @-}
split_aux :: Int -> (List Int, List Int) -> M (List Int, List Int)
split_aux x (ys, zs) = pure (Cons x ys, zs) <+> pure (ys, Cons x zs)

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
      kleisli permute (guardBy sorted) (Cons x xs)
    %==
      permute (Cons x xs) >>= guardBy sorted
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

{-@ reflect divide_and_conquer_lemma2_aux1 @-}
divide_and_conquer_lemma2_aux1 :: Int -> List Int -> M (List Int, List Int)
divide_and_conquer_lemma2_aux1 p xs =
  split xs >>= guardBy (divide_and_conquer_lemma2_aux2 p)

{-@ reflect divide_and_conquer_lemma2_aux2 @-}
divide_and_conquer_lemma2_aux2 :: Int -> (List Int, List Int) -> Bool
divide_and_conquer_lemma2_aux2 p (ys', zs') = all (leq p) ys' && all (geq p) zs'

{-@
divide_and_conquer_lemma2 ::
  Equality (M (List Int, List Int)) =>
  p:Int -> xs:List Int ->
  RefinesPlus (List Int, List Int)
    {pure (partition p xs)}
    {divide_and_conquer_lemma2_aux1 p xs}
@-}
divide_and_conquer_lemma2 :: Equality (M (List Int, List Int)) => Int -> List Int -> EqualityProp (M (List Int, List Int))
divide_and_conquer_lemma2 p Nil =
  [eqpropchain|
      pure (partition p Nil) <+> divide_and_conquer_lemma2_aux1 p Nil
    %==
      pure (partition p Nil) <+> (split Nil >>= guardBy (divide_and_conquer_lemma2_aux2 p))
    %==
      pure (partition p Nil) <+> (pure (Nil, Nil) >>= guardBy (divide_and_conquer_lemma2_aux2 p))
        %by %rewrite split Nil %to pure (Nil, Nil)
        %by undefined
        %-- TODO: why not? by def of split     
    %==
      pure (partition p Nil) <+> guardBy (divide_and_conquer_lemma2_aux2 p) (Nil, Nil)
        %by %rewrite pure (Nil, Nil) >>= guardBy (divide_and_conquer_lemma2_aux2 p)
                 %to guardBy (divide_and_conquer_lemma2_aux2 p) (Nil, Nil)
        %by bind_identity_left (Nil, Nil) (guardBy (divide_and_conquer_lemma2_aux2 p))
    %==
      pure (partition p Nil) <+> (guard (divide_and_conquer_lemma2_aux2 p (Nil, Nil)) >> pure (Nil, Nil))
        %by %rewrite guardBy (divide_and_conquer_lemma2_aux2 p) (Nil, Nil)
                 %to guard (divide_and_conquer_lemma2_aux2 p (Nil, Nil)) >> pure (Nil, Nil)
        %by %reflexivity
    %==
      pure (partition p Nil) <+> (guard (all (leq p) Nil && all (geq p) Nil) >> pure (Nil, Nil))
        %by %rewrite guard (divide_and_conquer_lemma2_aux2 p (Nil, Nil)) >> pure (Nil, Nil)
                 %to guard (all (leq p) Nil && all (geq p) Nil) >> pure (Nil, Nil)
        %by %reflexivity
    %==
      pure (partition p Nil) <+> (guard True >> pure (Nil, Nil))
        %by %rewrite all (leq p) Nil && all (geq p) Nil
                 %to True
        %by %reflexivity
    %==
      pure (partition p Nil) <+> (pure () >> pure (Nil, Nil))
        %by %rewrite guard True %to pure ()
        %by %reflexivity
    %==
      pure (partition p Nil) <+> pure (Nil, Nil)
        %by %rewrite pure () >> pure (Nil, Nil) %to pure (Nil, Nil) 
        %by seq_identity_left () (pure (Nil, Nil))
    %==
      pure (Nil, Nil) <+> pure (Nil, Nil)
        %by %rewrite pure (partition p Nil)
                 %to pure (Nil, Nil)
        %by %reflexivity
    %==
      pure (Nil, Nil)
        %by plus_identity_left (pure (Nil, Nil))
    %==
      pure () >> pure (Nil, Nil)
        %by %symmetry
        %by seq_identity_left () (pure (Nil, Nil))
    %==
      guard True >> pure (Nil, Nil)
        %by %rewrite pure () %to guard True
        %by %reflexivity
    %==
      guard ((\(ys, zs) -> (all (leq p) ys && all (geq p) zs)) (Nil, Nil)) >> pure (Nil, Nil)
        %by %rewrite True %to (\(ys, zs) -> (all (leq p) ys && all (geq p) zs)) (Nil, Nil)
        %by %reflexivity
    %==
      guardBy (\(ys, zs) -> (all (leq p) ys && all (geq p) zs)) (Nil, Nil)
    %==
      pure (Nil, Nil) >>= guardBy (\(ys, zs) -> (all (leq p) ys && all (geq p) zs))
        %by %symmetry
        %by bind_identity_left (Nil, Nil) (guardBy (\(ys, zs) -> (all (leq p) ys && all (geq p) zs)))
    %==
      split Nil >>= guardBy (\(ys, zs) -> (all (leq p) ys && all (geq p) zs))
        %by %rewrite pure (Nil, Nil) %to split Nil
        %by %reflexivity
    %==
      divide_and_conquer_lemma2_aux1 p Nil
        %by undefined
  |]
divide_and_conquer_lemma2 p (Cons x xs) =
  [eqpropchain|
      pure (partition p (Cons x xs))
        <+> divide_and_conquer_lemma2_aux1 p (Cons x xs)
    %==
      pure (partition p (Cons x xs))
        <+> (split (Cons x xs)
              >>= guardBy (divide_and_conquer_lemma2_aux2 p))
        %by %rewrite divide_and_conquer_lemma2_aux1 p (Cons x xs)
                 %to split (Cons x xs) >>= guardBy (divide_and_conquer_lemma2_aux2 p)
        %by %reflexivity
    %==
      pure (if leq x p then (Cons x ys, zs) else (ys, Cons x zs))
        <+> (split (Cons x xs)
              >>= guardBy (divide_and_conquer_lemma2_aux2 p))
        %by %rewrite partition p (Cons x xs)
                 %to if leq x p then (Cons x ys, zs) else (ys, Cons x zs)
        %by %reflexivity
    %==
      pure (if leq x p then (Cons x ys, zs) else (ys, Cons x zs))
        <+> ((split xs >>= split_aux x)
                >>= guardBy (divide_and_conquer_lemma2_aux2 p))
        %by %rewrite split (Cons x xs)
                 %to split xs >>= split_aux x
        %by %reflexivity
    %==
    %-- TODO: not sure how to progress; `guard` properties?
      split (Cons x xs)
        >>= guardBy (divide_and_conquer_lemma2_aux2 p)
        %by undefined
    %==
      divide_and_conquer_lemma2_aux1 p (Cons x xs)
  |]
  where
    ys = proj1 (partition p xs)
    zs = proj2 (partition p xs)

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

{-@
slowsort_Nil ::
  Equality (M (List Int)) =>
  EqualProp (M (List Int))
    {slowsort Nil}
    {pure Nil}
@-}
slowsort_Nil :: Equality (M (List Int)) => EqualityProp (M (List Int))
slowsort_Nil =
  [eqpropchain|
      slowsort Nil 
    %==
      kleisli permute (guardBy sorted) Nil
        %by undefined
        %-- TODO: why not? by def of slowsort
    %==
      permute Nil >>= guardBy sorted
        %by kleisli_unfold permute (guardBy sorted) Nil
    %==
      pure Nil >>= guardBy sorted 
        %by %rewrite permute Nil 
                 %to pure Nil
        %by %reflexivity
    %==
      guardBy sorted Nil 
        %by bind_identity_left Nil (guardBy sorted)
    %==
      guard (sorted Nil) >> pure Nil
    %==
      guard True >> pure Nil
        %by %rewrite sorted Nil 
                 %to True 
        %by %reflexivity
    %==
      pure () >> pure Nil
        %by %rewrite guard True 
                 %to pure ()
        %by %reflexivity
    %==
      pure Nil
        %by seq_identity_left () (pure Nil)
  |]

{-@
quicksort_refines_slowsort ::
  Equality (M (List Int)) =>
  xs:List Int ->
  RefinesPlus (List Int)
    {compose pure quicksort xs}
    {slowsort xs}
@-}
quicksort_refines_slowsort :: Equality (M (List Int)) => List Int -> EqualityProp (M (List Int))
quicksort_refines_slowsort Nil =
  [eqpropchain|
      compose pure quicksort Nil <+> slowsort Nil
    %==
      pure (quicksort Nil) <+> slowsort Nil
        %by %rewrite compose pure quicksort Nil
                %to pure (quicksort Nil)
        %by %reflexivity
    %==
      pure Nil <+> slowsort Nil
        %by %rewrite quicksort Nil
                %to Nil
        %by %reflexivity
    %==
      slowsort Nil <+> slowsort Nil
        %by %rewrite pure Nil
                %to slowsort Nil
        %by %symmetry
        %by slowsort_Nil
    %==
      slowsort Nil
        %by refinesplus_reflexivity (slowsort Nil)
  |]
quicksort_refines_slowsort (Cons x xs) =
  [eqpropchain|
      compose pure quicksort (Cons x xs) <+> slowsort (Cons x xs)
    %==
      pure (quicksort (Cons x xs)) <+> slowsort (Cons x xs)
        %by %rewrite compose pure quicksort (Cons x xs)
                 %to pure (quicksort (Cons x xs))
        %by %reflexivity
    %==
      pure (quicksort ys ++ Cons x Nil ++ quicksort zs)
        <+> slowsort (Cons x xs)
        %by %rewrite pure (quicksort (Cons x xs))
                 %to pure (quicksort ys ++ Cons x Nil ++ quicksort zs)
        %by %reflexivity
    %==
      slowsort (Cons x xs)
        %by undefined
        %-- TODO: not sure how to progress...
  |]
  where
    ys = proj1 (partition x xs)
    zs = proj2 (partition x xs)
