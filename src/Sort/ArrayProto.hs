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

{-
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
-}

{-
## Theorem. `iqsort_spec`
-}

{-
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
  RefinesPlus (Unit)
    {iqsort_spec_aux1 i xs}
    {iqsort_spec_aux2 i xs}
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
-}
