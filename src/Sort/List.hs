{-@ LIQUID "--compile-spec" @-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

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
import Prelude hiding (Monad, all, concat, foldl, length, pure, read, readList, seq, (+), (++), (>>), (>>=))

{-@ reflect apply2 @-}
apply2 :: (a -> b -> c) -> (a -> b -> c)
apply2 f = f

--
-- ## Slowsort
--

--
-- ### Definitions
---

{-@ reflect slowsort @-}
slowsort :: List Int -> M (List Int)
slowsort xs = permute xs >>= guardBy sorted

{-@ reflect sorted @-}
sorted :: List Int -> Bool
sorted Nil = True
sorted (Cons x xs) = all (leq x) xs && sorted xs

{-@ reflect split @-}
split :: List Int -> M (List Int, List Int)
split Nil = pure (Nil, Nil)
split (Cons x xs) = split xs >>= split_aux x

{-@ reflect split_aux @-}
split_aux :: Int -> (List Int, List Int) -> M (List Int, List Int)
split_aux x (ys, zs) = pure (Cons x ys, zs) <+> pure (ys, Cons x zs)

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

{-@ reflect sandwich @-}
sandwich :: List Int -> Int -> List Int -> List Int
sandwich ys x zs = concat (concat ys (single x)) zs

--
-- ### Lemmas
--

{-@ assume
pure_refines_permute ::
  xs:List Int ->
  RefinesPlus (List Int)
    {pure xs}
    {permute xs}
@-}
pure_refines_permute :: List Int -> EqualityProp (M (List Int))
pure_refines_permute xs = assumedProp

-- [ref] display 5
-- TODO: how do I prove (<=>)?
-- TODO: where is this used?
{-@ assume
sorted_middle ::
  ys:List Int -> x:Int -> zs:List Int ->
  {sorted (sandwich ys x zs) <=>
   sorted ys && sorted zs && all (geq x) ys && all (leq x) zs}
@-}
sorted_middle :: List Int -> Int -> List Int -> Proof
sorted_middle Nil x zs = ()
sorted_middle (Cons y ys) x zs = ()

--
-- split_preserves_length
--

-- TODO: how to phrase this??? for permute_preserves_length

-- {-@ reflect split_preserves_length_aux @-}
-- split_preserves_length_aux :: ((Int, Int) -> M a) -> (List Int, List Int) -> M a
-- split_preserves_length_aux k (ys, zs) = k (length ys, length zs)

-- {-@
-- split_preserves_length ::
--   xs:List Int ->
--   EqualProp (M Int)
--     {split xs >>= split_preserves_length_aux}
--     {}
-- @-}
-- split_preserves_length :: List Int -> EqualityProp (M Int)
-- split_preserves_length = undefined

--
-- permute_preserves_length
--

-- {-@ assume
-- permute_preserves_length ::
--   (Equality Natural, Equality (M (List Int)), Equality (M Natural)) =>
--   xs:List Int ->
--   EqualProp (M Natural)
--     {liftM length (permute xs)}
--     {pure (length xs)}
-- @-}
-- permute_preserves_length :: (Equality Natural, Equality (M (List Int)), Equality (M Natural)) => List Int -> EqualityProp (M Natural)
-- permute_preserves_length _ = assumedProp

-- permute_preserves_length :: (Equality (M Natural), Equality Natural, Equality (M (List Int))) => List Int -> EqualityProp (M Natural)
-- permute_preserves_length Nil =
--   [eqp| liftM length (permute Nil)
--     %== permute Nil >>= liftM_aux length
--           %by %reflexivity

--     %== permute Nil >>= apply (\xs -> pure (length xs))
--           %by (subst_cont (pure Nil) (liftM_aux length) (apply (\xs -> pure (length xs))))
--               (\xs ->
--                 reflexivity (apply (\xs -> pure (length xs)) xs)
--                 ? liftM_aux length xs)

--     %== pure Nil >>= apply (\xs -> pure (length xs))
--           %by subst_curr (permute Nil) (pure Nil) (apply (\xs -> pure (length xs)))
--                 reflexivity (permute Nil)

--     %== apply (\xs -> pure (length xs)) Nil
--           %by pure_bind Nil (apply (\xs -> pure (length xs)))

--     %== pure (length Nil)
--   |]
-- -- x =
-- --   [eqp| pure (length Nil)
-- --     %== apply (\xs -> pure (length xs)) Nil
-- --     %== pure Nil >>= apply (\xs -> pure (length xs))
-- --           %by %symmetry
-- --           %by pure_bind Nil (apply (\xs -> pure (length xs)))
-- --     %== permute Nil >>= apply (\xs -> pure (length xs))
-- --           %by %rewrite pure Nil
-- --                    %to permute Nil
-- --           %by %symmetry
-- --           %by %reflexivity
-- --     %== permute Nil >>= liftM_aux length
-- --           %by subst_cont (permute Nil) (apply (\xs -> pure (length xs))) (liftM_aux length)
-- --                 (\xs -> reflexivity (apply (\xs -> pure (length xs)) xs)
-- --                      ? apply (\xs -> pure (length xs)) xs
-- --                      ? liftM_aux length xs)
-- --     %== liftM length (permute Nil)
-- --           %by %symmetry
-- --           %by %reflexivity
-- --   |]

-- permute_preserves_length (Cons x xs) =
--   [eqp| pure (length (Cons x xs))

--     %== pure (S (length xs))
--           %by undefined

--     %== bind (split xs) (permute_preserves_length_lemma2_aux1)
--           %by undefined

--     %== split xs >>= permute_preserves_length_lemma2_aux1
--           %by undefined

--     %== split xs >>= (permute_aux1 x >=> apply (\xs -> pure (length xs)))
--           %by undefined

--     %== split xs >>= permute_aux1 x >>= apply (\xs -> pure (length xs))
--           %by undefined

--     %== permute (Cons x xs) >>= apply (\xs -> pure (length xs))
--       %by %rewrite split xs >>= permute_aux1 x
--                %to permute (Cons x xs)
--       %by %symmetry
--       %by %reflexivity

--     %== permute (Cons x xs) >>= liftM_aux length
--           %by subst_cont (permute (Cons x xs)) (apply (\xs -> pure (length xs))) (liftM_aux length)
--                 (\xs -> reflexivity (apply (\xs -> pure (length xs)) xs)
--                       ? apply (\xs -> pure (length xs)) xs
--                       ? liftM_aux length xs)

--     %== liftM length (permute (Cons x xs))
--           %by %symmetry
--           %by %reflexivity
--   |]

-- --
-- -- permute_preserves_length_lemma1
-- --

-- -- TODO: prove
-- {-@ assume
-- permute_preserves_length_lemma1 ::
--   Equality (M Int) =>
--   x:Int -> ys:List Int -> zs:List Int ->
--   EqualProp (M Int)
--     {bind (liftM2 (permute_aux2 x) (permute ys) (permute zs)) (pureF length)}
--     {pure (S (add (length ys) (length zs)))}
-- @-}
-- permute_preserves_length_lemma1 :: Equality (M Int) => Int -> List Int -> List Int -> EqualityProp (M Int)
-- permute_preserves_length_lemma1 = undefined

-- --
-- -- permute_preserves_length_lemma2
-- --

-- permute_preserves_length_lemma2_aux1 x = permute_aux1 x >=> permute_preserves_length_lemma2_aux1_aux x

-- permute_preserves_length_lemma2_aux1_aux x xs = pure (length xs)

-- -- permute_preserves_length_lemma2

-- -- --
-- -- -- permute_preserves_length_lemmaTMP
-- -- --

-- -- {-@ reflect permute_preserves_length_lemmaTMP_aux1 @-}
-- -- permute_preserves_length_lemmaTMP_aux1 :: (List Int, List Int) -> M Natural
-- -- permute_preserves_length_lemmaTMP_aux1 (ys, zs) = pure (S (length ys + length zs))

-- -- permute_preserves_length_lemmaTMP_aux2 :: Int -> (List Int, List Int) -> M Natural
-- -- permute_preserves_length_lemmaTMP_aux2 x = permute_aux1 x >=> apply (\xs -> pure (length xs))

-- -- {-@
-- -- permute_preserves_length_lemmaTMP ::
-- --   Equality (M Natural) =>
-- --   xs:List Int ->
-- --   EqualProp (M Natural)
-- --     {bind (split xs) permute_preserves_length_lemmaTMP_aux1}
-- --     {pure (S (length xs))}
-- -- @-}
-- -- permute_preserves_length_lemmaTMP :: Equality (M Natural) => List Int -> EqualityProp (M Natural)
-- -- permute_preserves_length_lemmaTMP Nil =
-- --   [eqp| split Nil >>= permute_preserves_length_lemmaTMP_aux1
-- --     %== pure (Nil, Nil) >>= permute_preserves_length_lemmaTMP_aux1
-- --           %by undefined
-- --           %{-
-- --           -- TODO
-- --           **** LIQUID: ERROR :1:1-1:1: Error
-- --           crash: SMTLIB2 respSat = Error "line 36831 column 452552: unknown constant Placeholder.M.Pure  (Int) (Placeholder.M.M Int) declared: (declare-fun Placeholder.M.Pure             ((Data.Refined.List.List Int))             (Placeholder.M.M (Data.Refined.List.List Int))) declared: (declare-fun Placeholder.M.Pure             ((Placeholder.M.M Int))             (Placeholder.M.M (Placeholder.M.M Int))) declared: (declare-fun Placeholder.M.Pure             (Data.Refined.Natural.Natural)             (Placeholder.M.M Data.Refined.Natural.Natural)) "

-- --           %by subst_curr (split Nil) (pure (Nil, Nil)) permute_preserves_length_lemmaTMP_aux1
-- --                 ( reflexivity (split Nil)
-- --                 ? split Nil
-- --                 ? pure (Nil, Nil) )
-- --           -}%
-- --     %== permute_preserves_length_lemmaTMP_aux1 (Nil, Nil)
-- --           %by pure_bind (Nil, Nil) permute_preserves_length_lemmaTMP_aux1
-- --     %== pure (S (length Nil + length Nil))
-- --     %== pure (S Z)
-- --     %== pure (S (length Nil))
-- --   |]
-- -- permute_preserves_length_lemmaTMP (Cons x xs) = undefined

-- -- -- permute_preserves_length_lemmaTMP xs =
-- -- --   [eqp| split xs >>= permute_preserves_length_lemmaTMP_aux1
-- -- --     %== split xs >>= apply (\(ys, zs) -> permute_preserves_length_lemmaTMP_aux1)
-- -- --     %==
-- -- --   |]
