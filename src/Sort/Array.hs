{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Sort.Array where

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
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (*), (+), (++), (>>), (>>=))

--
-- ## ipartl
--

{-@ reflect partl' @-}
partl' :: Int -> (List Int, List Int, List Int) -> M (List Int, List Int)
partl' p (ys, zs, Nil) = pure (ys, zs)
partl' p (ys, zs, Cons x xs) = dispatch x p (ys, zs, xs) >>= partl' p

{-@ reflect dispatch @-}
dispatch :: Int -> Int -> (List Int, List Int, List Int) -> M (List Int, List Int, List Int)
dispatch x p (ys, zs, xs) =
  if leq x p
    then permute zs >>= \zs' -> pure (ys ++ Cons x Nil, zs', xs)
    else permute (zs ++ Cons x Nil) >>= \zs' -> pure (ys, zs', xs)

-- final derivation of `ipartl`
{-@ reflect ipartl @-}
ipartl :: Int -> Natural -> (Natural, Natural, Natural) -> M (Natural, Natural)
ipartl p i (ny, nz, Z) = pure (ny, nz)
ipartl p i (ny, nz, S k) =
  read (i + ny + nz) >>= \x ->
    if leq x p
      then swap (i + ny) (i + ny + nz) >> ipartl p i (S ny, nz, k)
      else ipartl p i (ny, S nz, k)

--
-- ### ipartl spec lemmas
--

{-@ reflect ipartl_spec_lemma_aux1 @-}
ipartl_spec_lemma_aux1 :: Natural -> Int -> List Int -> M ()
ipartl_spec_lemma_aux1 i x zs =
  writeList i (zs ++ Cons x Nil) >> swap i (i + length zs)

{-@ reflect ipartl_spec_lemma_aux2 @-}
ipartl_spec_lemma_aux2 :: Natural -> Int -> List Int -> M ()
ipartl_spec_lemma_aux2 i x zs =
  permute zs >>= \zs' -> writeList i (Cons x Nil ++ zs')

-- [ref 11]
-- TODO: do they give a proof of this somewhere? try
{-@
ipartl_spec_lemma ::
  Equality (M Unit) =>
  i:Natural ->
  x:Int ->
  zs:List Int ->
  RefinesPlus (Unit)
    {ipartl_spec_lemma_aux1 i x zs}
    {ipartl_spec_lemma_aux2 i x zs}
@-}
ipartl_spec_lemma :: Equality (M ()) => Natural -> Int -> List Int -> EqualityProp (M ())
ipartl_spec_lemma i x zs =
  [eqpropchain|
      (writeList i (zs ++ Cons x Nil) >> swap i (i + length zs))
        <+> (permute zs >>= \zs' -> writeList i (Cons x Nil ++ zs'))
    %==
      permute zs >>= \zs' -> writeList i (Cons x Nil ++ zs')
        %by undefined -- TODO 
  |]

--
-- ### ipartl spec
--

{-@ reflect ipartl_spec_aux1 @-}
ipartl_spec_aux1 :: Int -> Natural -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_aux1 p i xs ys zs = writeList i (ys ++ zs ++ xs) >> ipartl p i (length ys, length zs, length xs)

{-@ reflect ipartl_spec_aux2 @-}
ipartl_spec_aux2 :: Int -> Natural -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_aux2 p i xs ys zs = partl' p (ys, zs, xs) >>= writeListToLength2 i

-- [ref 10]
{-@
ipartl_spec ::
  Equality (M (Natural, Natural)) =>
  p:Int ->
  i:Natural ->
  xs:List Int ->
  ys:List Int ->
  zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_aux1 p i xs ys zs}
    {ipartl_spec_aux2 p i xs ys zs}
@-}
ipartl_spec :: Equality (M (Natural, Natural)) => Int -> Natural -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec p i xs ys zs =
  [eqpropchain|
      (writeList i (ys ++ zs ++ xs) >> ipartl p i (length ys, length zs, length xs))
        <+> (partl' p (ys, zs, xs) >>= writeListToLength2 i)
    %==
      partl' p (ys, zs, xs) >>= writeListToLength2 i
        %by undefined -- TODO
  |]

--
-- ## iqsort
--

--
-- ### lemmas
--

{-@
permute_kleisli_permute_lemma ::
  Equality (M (List Int)) =>
  xs:List Int ->
  EqualProp (M (List Int)) {bind (permute xs) permute} {permute xs}
@-}
permute_kleisli_permute_lemma :: Equality (M (List Int)) => List Int -> EqualityProp (M (List Int))
permute_kleisli_permute_lemma Nil =
  [eqpropchain|
      bind (permute Nil) permute
    %==
      bind (pure Nil) permute
        %by %rewrite permute Nil 
                 %to pure Nil 
        %by %reflexivity
    %==
      permute Nil
        %by bind_identity_left_outfix Nil permute 
  |]
permute_kleisli_permute_lemma (Cons x xs) =
  [eqpropchain|
      bind (permute (Cons x xs)) permute 
    %==
      bind
        (split xs >>= \(ys, zs) -> liftM2 (\ys' zs' -> ys' ++ Cons x Nil ++ zs') (permute ys) (permute zs))
        permute 
        %by %rewrite permute (Cons x xs)
                 %to split xs >>= \(ys, zs) -> liftM2 (\ys' zs' -> ys' ++ Cons x Nil ++ zs') (permute ys) (permute zs)
        %by undefined
        %-- TODO: why not? by def of permute
    %==
      bind
        (split xs >>= \(ys, zs) -> permute ys >>= \ys' -> permute zs >>= \zs' -> pure (ys' ++ Cons x Nil ++ zs'))
        permute 
          %by undefined
          %{-
          -- TODO: doesn't work, even when by undefined
          ```
          %by %rewrite \(ys, zs) -> liftM2 (\ys' zs' -> ys' ++ Cons x Nil ++ zs') (permute ys) (permute zs)
                   %to \(ys, zs) -> permute ys >>= \ys' -> permute zs >>= \zs' -> pure (ys' ++ Cons x Nil ++ zs')
          %by %extend (ys, zs)
          %by undefined
          ```
          -- TODO: very strange error:
            ...
            The sort GHC.Types.Int is not numeric
              because
            Cannot unify int with GHC.Types.Int in expression: lq_anf$##7205759403794112138##d5x0K lam_arg##2
            ...
          -}%
    %==
      bind
        (split xs >>= \(ys, zs) -> permute ys >>= \ys' -> permute zs >>= \zs' -> pure (ys' ++ Cons x Nil ++ zs'))
        permute 
    %==
      permute (Cons x xs)
        %by undefined
        %-- TODO: not sure how to progress
  |]

{-@
permute_kleisli_permute ::
  (Equality (List Int -> M (List Int)), Equality (M (List Int))) =>
  xs:List Int ->
  EqualProp (M (List Int))
    {kleisli permute permute xs}
    {permute xs}
@-}
permute_kleisli_permute :: (Equality (List Int -> M (List Int)), Equality (M (List Int))) => List Int -> EqualityProp (M (List Int))
permute_kleisli_permute Nil =
  [eqpropchain|
      kleisli permute permute Nil
    %==
      permute Nil >>= permute
    %==
      pure Nil >>= permute
        %by %rewrite permute Nil %to pure Nil
        %by undefined
        %-- TODO: why not by reflexivity?
    %==
      permute Nil
        %by bind_identity_left Nil permute
  |]
permute_kleisli_permute (Cons x xs) =
  [eqpropchain|
      kleisli permute permute (Cons x xs)
    %==
      permute (Cons x xs) >>= permute
    %==
      (split xs >>= permute_aux1 x) >>= permute
        %by %rewrite permute (Cons x xs)
                 %to split xs >>= permute_aux1 x
        %by undefined
        %-- TODO: why not by def of permute?
    %==
      split xs >>= (permute_aux1 x >=> permute)
        %by bind_associativity (split xs) (permute_aux1 x) permute
    %==
      split xs >>= ((\(ys, zs) -> liftM2 (permute_aux2 x) (permute ys) (permute zs)) >=> permute)
        %by undefined
        %{-
        -- TODO: this error again: "The sort GHC.Types.Int is not numeric"
        %by %rewrite permute_aux1 x
                 %to \(ys, zs) -> liftM2 (permute_aux2 x) (permute ys) (permute zs)
        %by %extend (ys, zs)
        %by %reflexivity
        -}%
    %==
      split xs >>= ((\(ys, zs) -> permute ys >>= \ys' -> permute zs >>= \zs' -> pure (permute_aux2 x ys' zs')) >=> permute)
        %by undefined
        %{-
        -- TODO: not sure why; parsing error suggesting BlockArguments 
        %rewrite liftM2 (permute_aux2 x) (permute ys) (permute zs)
             %to \(ys, zs) -> permute ys >>= \ys' -> permute zs >>= \zs' -> pure (permute_aux2 x ys' zs')
        %by %extend (ys, zs)
        %reflexivity
        -}%
        %-- TODO: not sure how to progress
    %==
      permute (Cons x xs)
        %by undefined
  |]

{-@
permute_kleisli_slowsort ::
  (Equality (M (List Int)), Equality (List Int -> M (List Int))) =>
  xs:List Int ->
  EqualProp (M (List Int))
    {kleisli permute slowsort xs}
    {slowsort xs}
@-}
permute_kleisli_slowsort :: (Equality (M (List Int)), Equality (List Int -> M (List Int))) => List Int -> EqualityProp (M (List Int))
permute_kleisli_slowsort xs =
  [eqpropchain|
      kleisli permute slowsort xs
    %==
      kleisli permute (kleisli permute (guardBy sorted)) xs
        %by %rewrite slowsort
                 %to kleisli permute (guardBy sorted)
        %by %extend ys
        %by %reflexivity
    %==
      kleisli (kleisli permute permute) (guardBy sorted) xs
        %by undefined
        %-- TODO: prove kleisli_associativity in Placeholder.M
    %==
      kleisli permute (guardBy sorted) xs
        %by %rewrite kleisli permute permute
                 %to permute 
        %by %extend ys
        %by permute_kleisli_permute ys
    %==
      slowsort xs
  |]

--
-- #### lemma 1
--

{-@ reflect iqsort_spec_lemma1_aux1 @-}
iqsort_spec_lemma1_aux1 :: Natural -> Int -> List Int -> M ()
iqsort_spec_lemma1_aux1 i p xs =
  partl' p (Nil, Nil, xs) >>= iqsort_spec_lemma1_aux2 i p

{-@ reflect iqsort_spec_lemma1_aux2 @-}
iqsort_spec_lemma1_aux2 :: Natural -> Int -> (List Int, List Int) -> M ()
iqsort_spec_lemma1_aux2 i p (ys, zs) =
  permute ys >>= iqsort_spec_lemma1_aux3 i p ys zs

{-@ reflect iqsort_spec_lemma1_aux3 @-}
iqsort_spec_lemma1_aux3 :: Natural -> Int -> List Int -> List Int -> List Int -> M ()
iqsort_spec_lemma1_aux3 i p ys zs ys' =
  writeList i (ys' ++ Cons p Nil ++ zs)
    >> iqsort i (length ys)
    >> iqsort (S (i + length ys)) (length zs)

-- uses: [ref 9] and [ref 12]
-- desc: For this to work, we introduced two `perm` to permute both partitions
-- generated by partition. We can do so because `perm >=> perm = perm` and thus
-- `perm >=> slowsort = slowsort`. The term perm `zs` was combined with
-- `partition p`, yielding `partl' p`, while `perm ys` will be needed later. We
-- also needed [ref 9] to split `writeList i (ys' ++ [x] ++ zs')` into two
-- parts. Assuming that [ref 12] has been met for lists shorter than `xs`, two
-- subexpressions are folded back to `iqsort`.
{-@
iqsort_spec_lemma1 ::
  Equality (M ()) =>
  i:Natural -> p:Int -> xs:List Int ->
  EqualProp (M ())
    {iqsort_spec_aux2 i (Cons p xs)}
    {iqsort_spec_lemma1_aux1 i p xs}
@-}
iqsort_spec_lemma1 :: Equality (M ()) => Natural -> Int -> List Int -> EqualityProp (M ())
iqsort_spec_lemma1 = undefined -- TODO

--
-- #### lemma 2
--

{-@ reflect iqsort_spec_lemma2_aux1 @-}
iqsort_spec_lemma2_aux1 :: Natural -> Int -> List Int -> M ()
iqsort_spec_lemma2_aux1 i p ys = permute ys >>= iqsort_spec_lemma2_aux2 i p

{-@ reflect iqsort_spec_lemma2_aux2 @-}
iqsort_spec_lemma2_aux2 :: Natural -> Int -> List Int -> M ()
iqsort_spec_lemma2_aux2 i p ys' = writeList i (ys' ++ Cons p Nil)

-- [ref 13]
-- uses: iqsort_spec_lemma1 [ref 10], ipartl_spec_lemma [ref 11]
-- desc: Now that we have introduced `partl'`, the next goal is to embed
-- `ipartl`. The status of the array before the two calls to `iqsort` is given
-- by `writeList i (ys' ++ [p] ++ zs)`. That is, `ys' ++ [p] ++ zs` is stored in
-- the array from index `i`, where `ys'` is a permutation of `ys`. The
-- postcondition of `ipartl`, according to the specification [ref 10], ends up
-- with `ys` and `zs` stored consecutively. To connect the two conditions, we
-- use a lemma that is dual to [ref 11]:
{-@
iqsort_spec_lemma2 ::
  Equality (M Unit) =>
  i:Natural -> p:Int -> ys:List Int ->
  RefinesPlus (Unit)
    {seq (writeList i (append (Cons p Nil) ys)) (swap i (add i (length ys)))}
    {iqsort_spec_lemma2_aux1 i p ys}
@-}
iqsort_spec_lemma2 :: Equality (M Unit) => Natural -> Int -> List Int -> EqualityProp (M Unit)
iqsort_spec_lemma2 = undefined

--
-- #### lemma 3
--

{-@ reflect iqsort_spec_lemma3_aux1 @-}
iqsort_spec_lemma3_aux1 :: Natural -> Int -> List Int -> M ()
iqsort_spec_lemma3_aux1 i p xs =
  writeList i (Cons p xs)
    >> ipartl p (S i) (Z, Z, length xs)
      >>= iqsort_spec_lemma3_aux2 i

{-@ reflect iqsort_spec_lemma3_aux2 @-}
iqsort_spec_lemma3_aux2 :: Natural -> (Natural, Natural) -> M ()
iqsort_spec_lemma3_aux2 i (ny, nz) =
  swap i (i + ny)
    >> iqsort i ny
    >> iqsort (S (i + ny)) nz

-- uses: iqsort_spec_lemma1 [ref 10], iqsort_spec_lemma2 [ref 13]
-- desc. This is what the typical quicksort algorithm does: swapping the pivot
-- with the last element of `ys`, and [ref 13] says that it is valid because
-- that is one of the many permutations of `ys`. With [ref 13] and [ref 10], the
-- specification can be refined to:
{-@
iqsort_spec_lemma3 ::
  Equality (M ()) =>
  i:Natural -> p:Int -> xs:List Int ->
  RefinesPlus (Unit)
    {iqsort_spec_lemma3_aux1 i p xs}
    {iqsort_spec_lemma1_aux1 i p xs}
@-}
iqsort_spec_lemma3 :: Equality (M ()) => Natural -> Int -> List Int -> EqualityProp (M ())
iqsort_spec_lemma3 = undefined -- TODO

--
-- #### lemma 4
--

-- connects `iqsort_spec_lemma3` to `iqsort_spec` (`Cons` case)
{-@
iqsort_spec_lemma4 ::
  Equality (M ()) =>
  i:Natural -> p:Int -> xs:List Int ->
  RefinesPlus (Unit)
    {iqsort_spec_aux1 i (Cons p xs)}
    {iqsort_spec_lemma3_aux1 i p xs}
@-}
iqsort_spec_lemma4 :: Equality (M ()) => Natural -> Int -> List Int -> EqualityProp (M ())
iqsort_spec_lemma4 = undefined -- TODO

--
-- #### iqsort
--

-- `iqsort i n` sorts the `n` elements in the array starting from index `i`.
-- TODO: need to prove termination?
{-@ lazy iqsort @-}
{-@ reflect iqsort @-}
iqsort :: Natural -> Natural -> M ()
iqsort i Z = pure ()
iqsort i (S n) = read i >>= iqsort_aux1 i n

{-@ lazy iqsort_aux1 @-}
{-@ reflect iqsort_aux1 @-}
iqsort_aux1 :: Natural -> Natural -> Int -> M ()
iqsort_aux1 i n p = ipartl p (S i) (Z, Z, n) >>= iqsort_aux2 i n

{-@ lazy iqsort_aux2 @-}
{-@ reflect iqsort_aux2 @-}
iqsort_aux2 :: Natural -> Natural -> (Natural, Natural) -> M ()
iqsort_aux2 i n (ny, nz) = swap i (i + ny) >> iqsort i ny >> iqsort (S (i + ny)) nz

--
-- ### iqsort spec
--

-- from [ref 12]
{-@ reflect iqsort_spec_aux1 @-}
iqsort_spec_aux1 :: Natural -> List Int -> M ()
iqsort_spec_aux1 i xs = writeList i xs >> iqsort i (length xs)

-- from [ref 12]
{-@ reflect iqsort_spec_aux2 @-}
iqsort_spec_aux2 :: Natural -> List Int -> M ()
iqsort_spec_aux2 i xs = slowsort xs >>= writeList i

{-@
iqsort_spec_aux1_Nil ::
  (Equality (M Unit), Equality (M (List Int))) =>
  i:Natural ->
  EqualProp (M Unit) {iqsort_spec_aux1 i Nil} {pure it}
@-}
iqsort_spec_aux1_Nil :: (Equality (M ()), Equality (M (List Int))) => Natural -> EqualityProp (M ())
iqsort_spec_aux1_Nil i =
  [eqpropchain|
      iqsort_spec_aux1 i Nil
    %==
      writeList i Nil >> iqsort i (length Nil)
    %==
      writeList i Nil >> iqsort i Z
        %by %rewrite length Nil %to Z
        %by %reflexivity
    %==
      writeList i Nil >> pure ()
        %by %rewrite iqsort i Z %to pure ()
        %by %reflexivity
    %==
      pure it >> pure ()
        %by %rewrite writeList i Nil %to pure it
        %by %reflexivity
    %==
      pure ()
        %by seq_identity_left it (pure ())
    %==
      pure it
        %by %rewrite () %to it
        %by %reflexivity
  |]

{-@
iqsort_spec_aux2_Nil ::
  (Equality (M Unit), Equality (M (List Int))) =>
  i:Natural ->
  EqualProp (M Unit) {iqsort_spec_aux2 i Nil} {pure it}
@-}
iqsort_spec_aux2_Nil :: (Equality (M ()), Equality (M (List Int))) => Natural -> EqualityProp (M ())
iqsort_spec_aux2_Nil i =
  [eqpropchain|
      iqsort_spec_aux2 i Nil
    %==
      slowsort Nil >>= writeList i
    %==
      (permute Nil >>= guardBy sorted) >>= writeList i
        %by %rewrite slowsort Nil %to permute Nil >>= guardBy sorted
        %by %reflexivity
    %==
      (pure Nil >>= guardBy sorted) >>= writeList i
        %by %rewrite permute Nil %to pure Nil
        %by %reflexivity
    %==
      guardBy sorted Nil >>= writeList i
        %by %rewrite pure Nil >>= guardBy sorted %to guardBy sorted Nil
        %by bind_identity_left Nil (guardBy sorted)
    %==
      (guard (sorted Nil) >> pure Nil) >>= writeList i
        %by %rewrite guardBy sorted Nil %to guard (sorted Nil) >> pure Nil
        %by %reflexivity
    %==
      (guard True >> pure Nil) >>= writeList i
        %by %rewrite sorted Nil %to True
        %by %reflexivity
    %==
      (pure () >> pure Nil) >>= writeList i
        %by %rewrite guard True %to pure ()
        %by %reflexivity
    %==
      pure Nil >>= writeList i
        %by %rewrite pure () >> pure Nil %to pure Nil
        %by seq_identity_left () (pure Nil)
    %==
      writeList i Nil
        %by bind_identity_left Nil (writeList i)
    %==
      pure it
        %by undefined
  |]

{-@ reflect iqsort_spec_aux1_Cons_aux @-}
iqsort_spec_aux1_Cons_aux :: Natural -> Int -> List Int -> M ()
iqsort_spec_aux1_Cons_aux i p xs =
  (write i p >> writeList (S i) xs)
    >> (read i >>= iqsort_aux1 i n)
  where
    n = length xs

{-@
iqsort_spec_aux1_Cons ::
  (Equality (M Unit), Equality (M (List Int))) =>
  i:Natural -> p:Int -> xs:List Int ->
  EqualProp (M Unit)
    {iqsort_spec_aux1 i (Cons p xs)}
    {iqsort_spec_aux1_Cons_aux i p xs}
@-}
iqsort_spec_aux1_Cons :: (Equality (M ()), Equality (M (List Int))) => Natural -> Int -> List Int -> EqualityProp (M ())
iqsort_spec_aux1_Cons i p xs =
  [eqpropchain|
      iqsort_spec_aux1 i (Cons p xs)  
    %==
      writeList i (Cons p xs) >> iqsort i (length (Cons p xs))
    %==
      writeList i (Cons p xs) >> iqsort i (S (length xs))
        %by %rewrite length (Cons p xs) %to S (length xs)
        %by %reflexivity
    %==
      writeList i (Cons p xs) >> iqsort i (S n)
        %by %rewrite length xs %to n 
        %by %reflexivity
    %==
      writeList i (Cons p xs) >> (read i >>= iqsort_aux1 i n)
        %by %rewrite iqsort i (S n)
                 %to read i >>= iqsort_aux1 i n
        %by %reflexivity
    %==
      (write i p >> writeList (S i) xs) >> (read i >>= iqsort_aux1 i n)
        %by %rewrite writeList i (Cons p xs)
                 %to write i p >> writeList (S i) xs
        %by %reflexivity
    %==
      iqsort_spec_aux1_Cons_aux i p xs
        %by %symmetry
        %by %reflexivity
  |]
  where
    n = length xs

{-@ reflect iqsort_spec_aux2_Cons_aux @-}
iqsort_spec_aux2_Cons_aux :: Natural -> Int -> List Int -> M ()
iqsort_spec_aux2_Cons_aux i p xs =
  split xs
    >>= permute_aux1 p
    >>= guardBy sorted
    >>= writeList i

{-@
iqsort_spec_aux2_Cons ::
  (Equality (M Unit), Equality (M (List Int))) =>
  i:Natural -> p:Int -> xs:List Int ->
  EqualProp (M Unit)
    {iqsort_spec_aux2 i (Cons p xs)}
    {iqsort_spec_aux2_Cons_aux i p xs}
@-}
iqsort_spec_aux2_Cons :: (Equality (M ()), Equality (M (List Int))) => Natural -> Int -> List Int -> EqualityProp (M ())
iqsort_spec_aux2_Cons i p xs =
  [eqpropchain|
      iqsort_spec_aux2 i (Cons p xs)
    %==
      slowsort (Cons p xs) >>= writeList i
    %==
      (permute (Cons p xs) >>= guardBy sorted) >>= writeList i
        %by %rewrite slowsort (Cons p xs)
                 %to permute (Cons p xs) >>= guardBy sorted
        %by %reflexivity
    %==
      ((split xs >>= permute_aux1 p) >>= guardBy sorted) >>= writeList i
        %by %rewrite permute (Cons p xs)
                 %to split xs >>= permute_aux1 p
        %by %reflexivity
    %==
      iqsort_spec_aux2_Cons_aux i p xs
        %by %symmetry
        %by %reflexivity
  |]
