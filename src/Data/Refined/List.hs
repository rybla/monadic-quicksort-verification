{-@ LIQUID "--compile-spec" @-}
{-# OPTIONS_GHC "-Wno-missing-signatures" #-}

module Data.Refined.List where

import Data.Refined.Natural
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (all, concat, foldl, length, (+), (++))

{-
# List
-}

{-@
data List a where
    Nil :: List a
  | Cons :: a -> List a -> List a
@-}
data List a where
  Nil :: List a
  Cons :: a -> List a -> List a

{-
## Interface
-}

{-@ reflect length @-}
length :: List a -> Natural
length Nil = Z
length (Cons _ xs) = S (length xs)

{-@ reflect concat @-}
concat :: List a -> List a -> List a
concat Nil ys = ys
concat (Cons x xs) ys = Cons x (concat xs ys)

{-@ reflect snoc @-}
snoc :: List a -> a -> List a
snoc xs x = xs ++ Cons x Nil

{-@ reflect single @-}
single :: a -> List a
single x = Cons x Nil

{-@ infixr 5 ++ @-}
infixr 5 ++

{-@ reflect ++ @-}
(++) :: List a -> List a -> List a
(++) = concat

-- {-@ infixr 5 ++ @-}
-- {-@ reflect ++ @-}
-- (++) :: List a -> List a -> List a
-- xs ++ ys = concat xs ys

{-@ automatic-instances concat_identity @-}
{-@
concat_identity :: xs:List a -> {(concat xs Nil = xs) && (concat Nil xs = xs)}
@-}
concat_identity :: List a -> Proof
concat_identity Nil = trivial
concat_identity (Cons _ xs) = concat_identity xs

{-@
concat_associativity :: xs:List a -> ys:List a -> zs:List a -> {xs ++ ys ++ zs = (xs ++ ys) ++ zs}
@-}
concat_associativity :: List a -> List a -> List a -> Proof
concat_associativity xs ys zs = undefined -- TODO

{-@
length_snoc :: xs:List a -> x:a -> {length (xs ++ Cons x Nil) = S (length xs)}
@-}
length_snoc :: List a -> a -> Proof
length_snoc xs x = undefined -- TODO

{-@
length_concat :: xs:List a -> ys:List a -> {add (length xs) (length ys) = length (xs ++ ys)}
@-}
length_concat :: List a -> List a -> Proof
length_concat xs ys = undefined -- TODO

-- {-@
-- concat_concat_single ::
--   ys:List a -> zs:List a -> x:a ->
--   {concat (concat ys zs) (single x) = concat ys (snoc zs x)}
-- @-}
-- concat_concat_single :: List a -> List a -> a -> Proof
concat_concat_single ys zs x = undefined

-- |
-- == Utilities

{-@ reflect all @-}
all :: (a -> Bool) -> List a -> Bool
all p Nil = True
all p (Cons x xs) = p x && all p xs

-- |
-- == Instances

--
instance (EqSMT a, Equality a) => Equality (List a) where
  symmetry = undefined
  transitivity = undefined
