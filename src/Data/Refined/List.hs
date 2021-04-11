{-@ LIQUID "--compile-spec" @-}

module Data.Refined.List where

import Data.Refined.Natural
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (all, foldl, length)

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

{-@ reflect ++ @-}
(++) :: List a -> List a -> List a
(++) = append

-- {-@ infixr 5 ++ @-}
-- {-@ reflect ++ @-}
-- (++) :: List a -> List a -> List a
-- xs ++ ys = append xs ys

{-@ automatic-instances append_identity @-}
{-@
append_identity :: xs:List a -> {(append xs Nil = xs) && (append Nil xs = xs)}
@-}
append_identity :: List a -> Proof
append_identity Nil = trivial
append_identity (Cons _ xs) = append_identity xs

{-
## Utilities
-}

{-@ reflect all @-}
all :: (a -> Bool) -> List a -> Bool
all p Nil = True
all p (Cons x xs) = p x && all p xs
