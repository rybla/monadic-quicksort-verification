module Data.Refined.List where

import Data.Refined.Natural
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, (+), (++))

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

{-@ reflect append @-}
append :: List a -> List a -> List a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

{-@ infixr 5 ++ @-}
{-@ reflect ++ @-}
(++) :: List a -> List a -> List a
xs ++ ys = append xs ys

{-@ automatic-instances append_identity @-}
{-@
append_identity :: xs:List a -> {(xs ++ Nil = xs) && (Nil ++ xs = xs)}
@-}
append_identity :: List a -> Proof
append_identity Nil = trivial
append_identity (Cons _ xs) = append_identity xs

-- TODO: old, using built-in list

-- {-@
-- length :: [a] -> Natural
-- @-}
-- length :: [a] -> Natural
-- length [] = Z
-- length (_ : xs) = S (length xs)

-- {-@ reflect append @-}
-- append :: [a] -> [a] -> [a]
-- append [] ys = ys
-- append (x : xs) ys = x : (xs ++ ys)

-- {-@ infixr 5 ++ @-}
-- {-@ reflect ++ @-}
-- (++) :: [a] -> [a] -> [a]
-- xs ++ ys = append xs ys

-- -- [] ++ ys = ys
-- -- (x : xs) ++ ys = x : (xs ++ ys)

-- {-@ automatic-instances append_identity @-}
-- {-@
-- append_identity :: xs:[a] -> {(xs ++ [] = xs) && ([] ++ xs = xs)}
-- @-}
-- append_identity :: [a] -> Proof
-- append_identity [] = trivial
-- append_identity (x : xs) = append_identity xs
