module Data.Natural where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length)

{-
# Natural numbers
-}

{-
## Data
-}

{-@
data Natural = Z | S Natural
@-}
data Natural = Z | S Natural

{-
## Addition and Multiplication
-}

{-@ reflect add @-}
add :: Natural -> Natural -> Natural
Z `add` n = n
S m `add` n = S (add m n)

{-@ automatic-instances add_identity @-}
{-@
add_identity :: n:Natural -> {(add n Z = n) && (add Z n = n)}
@-}
add_identity :: Natural -> Proof
add_identity Z = trivial
add_identity (S n) = add_identity n

{-@ automatic-instances add_S_right @-}
{-@
add_S_right :: m:Natural -> n:Natural -> {add m (S n) = S (add m n)}
@-}
add_S_right :: Natural -> Natural -> Proof
add_S_right Z n = add_identity (S n) &&& add_identity n
add_S_right (S m) n = add_S_right m n

{-@ automatic-instances add_commutativity @-}
{-@
add_commutativity :: m:Natural -> n:Natural -> {add m n = add n m}
@-}
add_commutativity :: Natural -> Natural -> Proof
add_commutativity Z n = add_identity n
add_commutativity (S m) n = add_commutativity m n &&& add_S_right n m

{-@ automatic-instances add_associativity @-}
{-@
add_associativity :: l:Natural -> m:Natural -> n:Natural -> {add (add l m) n = add l (add m n)}
@-}
add_associativity :: Natural -> Natural -> Natural -> Proof
add_associativity Z m n = add_identity n &&& add_identity (add m n)
add_associativity (S l) m n = add_associativity l m n

-- 0 * n = 0
-- (1 + m) * n = n + (m * n)
{-@ reflect mul @-}
mul :: Natural -> Natural -> Natural
Z `mul` n = Z
S m `mul` n = n `add` (m `mul` n)

{-@ reflect one @-}
one :: Natural
one = S Z

-- n + 0 = 0 + n = n
{-@ automatic-instances mul_identity @-}
{-@
mul_identity :: n:Natural -> {(mul one n = n) && (mul n one = n)}
@-}
mul_identity :: Natural -> Proof
mul_identity Z = trivial
mul_identity (S n) = mul_identity n

-- n * 0 = 0 * n = 0
{-@ automatic-instances mul_annihilator @-}
{-@
mul_annihilator :: n:Natural -> {(mul n Z = Z) && (mul Z n = Z)}
@-}
mul_annihilator :: Natural -> Proof
mul_annihilator Z = trivial
mul_annihilator (S n) = mul_annihilator n

-- m * (1 + n) = m + (m * n)
{-@ automatic-instances mul_S_right @-}
{-@
mul_S_right :: m:Natural -> n:Natural -> {mul m (S n) = add m (mul m n)}
@-}
mul_S_right :: Natural -> Natural -> Proof
mul_S_right Z n = trivial
mul_S_right (S m) n =
  mul_S_right m n
    &&& add_associativity n m (m `mul` n)
    &&& add_commutativity n m
    &&& add_associativity m n (m `mul` n)

{-@ automatic-instances mul_commutativity @-}
{-@
mul_commutativity :: m:Natural -> n:Natural -> {mul m n = mul n m}
@-}
mul_commutativity :: Natural -> Natural -> Proof
mul_commutativity Z n = mul_annihilator n
mul_commutativity (S m) n = mul_commutativity m n &&& mul_S_right n m

-- TODO: prove
{-@ automatic-instances mul_distributivity @-}
{-@
mul_distributivity :: l:Natural -> m:Natural -> n:Natural -> {mul l (add m n) = add (mul l m) (mul l n)}
@-}
mul_distributivity :: Natural -> Natural -> Natural -> Proof
mul_distributivity Z m n = trivial
mul_distributivity (S l) m n = undefined

-- (1 + l) * (m + n)
-- (m + n) + (l * (m + n))
-- ...
-- m + (((l * m) + n) + (l * n))
-- m + (((l * m) + n) + (l * n))
-- m + ((l * m) + (n + (l * n)))
-- (m + (l * m)) + (n + (l * n)) ? add_associativity m (l * m) (n + (l * n))
-- ((1 + l) * m) + ((1 + l) * n)

{-
## Utilities
-}

-- TODO

{-
## List
-}

{-@ reflect length @-}
length :: [a] -> Natural
length [] = Z
length (_ : xs) = S (length xs)

{-@ reflect append @-}
append :: [a] -> [a] -> [a]
append [] ys = ys
append (x : xs) ys = x : (xs `append` ys)

{-@ automatic-instances append_identity @-}
{-@
append_identity :: xs:[a] -> {append xs [] = xs && append [] xs = xs}
@-}
append_identity :: [a] -> Proof
append_identity [] = trivial
append_identity (x : xs) = append_identity xs
