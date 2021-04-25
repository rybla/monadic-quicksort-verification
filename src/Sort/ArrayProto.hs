{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Sort.ArrayProto where

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
import Sort.Array
import Sort.List
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (*), (+), (++), (>>), (>>=))

{-@
permute_kleisli_permute_lemma ::
  Equality (M (List Int)) =>
  xs:List Int ->
  EqualProp (M (List Int))
    {bind (permute xs) permute}
    {permute xs}
@-}
permute_kleisli_permute_lemma :: Equality (M (List Int)) => List Int -> EqualityProp (M (List Int))
permute_kleisli_permute_lemma Nil =
  -- TODO: solver fail
  [eqpropchain|
      %-- permute Nil >>= permute
      permute Nil >>= permute
    %==
      permute Nil
        %by undefined
        %-- TODO: bind_identity_left Nil permute 
  |]
permute_kleisli_permute_lemma (Cons x xs) = undefined

{-- TODO: solver fail
[eqpropchain|
    permute (Cons x xs)
      >>= permute
  %==
    split xs
      >>= apply (\(ys, zs) -> liftM2 (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs')) (permute ys) (permute zs))
        >>= permute
  %==
    split xs
      >>= apply (\(ys, zs) -> permute ys >>= apply (\ys' -> permute zs >>= apply (\zs' -> pure (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs') ys' zs'))))
        >>= permute
      %by %rewrite apply (\(ys, zs) -> liftM2 (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs')) (permute ys) (permute zs))
               %to apply (\(ys, zs) -> permute ys >>= apply (\ys' -> permute zs >>= apply (\zs' -> pure (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs') ys' zs'))))
      %-- %by %extend (ys, zs) -- TODO: why does this break it? even with `%by undefined` after
      %by undefined
  %==
    permute (Cons x xs)
      %by undefined
|]
-}

{-@
permute_kleisli_permute ::
  (Equality (List Int -> M (List Int)), Equality (M (List Int))) =>
  EqualProp (List Int -> M (List Int))
    {kleisli permute permute}
    {permute}
@-}
permute_kleisli_permute :: (Equality (List Int -> M (List Int)), Equality (M (List Int))) => EqualityProp (List Int -> M (List Int))
permute_kleisli_permute = undefined

{-- TODO: solver fail
[eqpropchain|
    permute >=> permute
  %==
    apply (\xs -> permute xs >>= permute)
  %==
    apply (\xs -> permute xs)
      %-- TODO: why not?
      %-- %by %extend xs
      %-- permute_kleisli_permute_lemma xs
      %by undefined
  %==
    permute
      %by %extend xs
      %by undefined
|]
-}

{-@
permute_kleisli_slowsort ::
  Equality (M (List Int)) =>
  xs:List Int ->
  EqualProp (M (List Int))
    {kleisli permute (slowsort) xs}
    {slowsort xs}
@-}
permute_kleisli_slowsort :: Equality (M (List Int)) => List Int -> EqualityProp (M (List Int))
permute_kleisli_slowsort xs =
  [eqpropchain|
      (permute >=> slowsort) xs 
    %==
      (permute >=> (permute >=> guardBy sorted)) xs
    %==
      slowsort xs
        %by undefined
  |]

{-
## Theorem. `iqsort_spec`
-}

{-@ reflect iqsort_spec_aux1 @-}
iqsort_spec_aux1 :: Natural -> List Int -> M ()
iqsort_spec_aux1 i xs = writeList i xs >> iqsort i (length xs)

{-@ reflect iqsort_spec_aux2 @-}
iqsort_spec_aux2 :: Natural -> List Int -> M ()
iqsort_spec_aux2 i xs = slowsort xs >>= writeList i

-- main theorem
-- [ref] display 12
{-@
iqsort_spec ::
  Equality (M Unit) =>
  i:Natural ->
  xs:List Int ->
  RefinesPlus Unit {iqsort_spec_aux1 i xs} {iqsort_spec_aux2 i xs}
@-}
iqsort_spec :: Equality (M ()) => Natural -> List Int -> EqualityProp (M ())
iqsort_spec i Nil = undefined
iqsort_spec i (Cons p xs) =
  [eqpropchain|
      (writeList i (Cons p xs) >> iqsort i (length (Cons p xs)))
        <+> (slowsort (Cons p xs) >>= writeList i)

    %==

      partl' p (Nil, Nil, (Cons p xs))
        >>= apply
          ( \(ys, zs) ->
              permute ys
                >>= apply
                  ( \ys' ->
                      writeList i (ys' ++ Cons p Nil ++ zs)
                        >> iqsort i (length ys)
                        >> iqsort (S (i + length ys)) (length zs)
                  )
          )
        %by undefined -- TODO: prove

    %==

      slowsort (Cons p xs) >>= writeList i
        %by undefined
  |]
