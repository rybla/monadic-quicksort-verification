{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-} 

module Reverse where 

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding ((++))
import PropositionalEquality
import PEqProperties

{-@ infix ++ @-}
{-@ infix :  @-}


------------------------------------------------------------
-- | Main Theorem   ----------------------------------------
------------------------------------------------------------
-- This is SAFE 
reverseFunEq :: AEq [a] => EqT ([a] -> [a])
{-@ reverseFunEq :: AEq [a] => EqRT ([a] -> [a]) {fastReverse} {slowReverse} @-}
reverseFunEq = EqFun fastReverse slowReverse reverseTEq

-- on arbitrary types, reuses existing infra
reverseFunSimple :: Reflexivity [a] => [a] -> EqT [a]
{-@ reverseFunSimple :: (Reflexivity [a], Transitivity [a]) => xs:[a] -> EqRT [a] {fastReverse xs} {slowReverse xs} @-}
reverseFunSimple xs = refl (fastReverse xs) ? lemma xs [] ? rightId (slowReverse xs)

-- on arbitrary types, uses explicit lemma
reverseFunProp :: (Reflexivity [a], Transitivity [a]) => [a] -> EqT [a]
{-@ reverseFunProp :: (Reflexivity [a], Transitivity [a]) => xs:[a] -> EqRT [a] {fastReverse xs} {slowReverse xs} @-}
reverseFunProp xs = trans (fastReverse xs) 
                          (slowReverse xs ++ []) 
                          (slowReverse xs) 
                          (reverseSameLemma [] xs) 
                          (rightIdP (slowReverse xs))

reverseSameLemma :: (Reflexivity [a], Transitivity [a]) => [a] -> [a] -> EqT [a]
{-@ reverseSameLemma :: (Reflexivity [a], Transitivity [a]) => rest:[a] -> xs:[a] -> EqRT [a] {fastReverse' rest xs} {slowReverse xs ++ rest} @-}
reverseSameLemma rest [] = refl rest
reverseSameLemma rest (x:xs) =
  trans (fastReverse' rest (x:xs))
        (slowReverse xs ++ (x:rest))
        (slowReverse (x:xs) ++ rest)
    (reverseSameLemma (x:rest) xs)
    (assocP (slowReverse xs) [x] rest)


{-@ rightIdP :: xs:[a] -> EqRT [a] {xs ++ []} {xs} @-}
rightIdP :: (Reflexivity [a], Transitivity [a]) => [a] -> EqT [a]
rightIdP []     = refl [] 
rightIdP (x:xs) = trans ((x:xs) ++ [])
                        (cons x (xs++[]))
                        (cons x xs)
                        (refl (x:(xs ++[])))
                        (eqRTCtx (xs ++ []) (xs) (rightIdP xs) (cons x)) 


{-@ assocP :: xs:[a] -> ys:[a] -> zs:[a]
          -> EqRT [a] {(xs ++ (ys ++ zs))} {((xs ++ ys) ++ zs)}  @-}
assocP :: (Reflexivity [a], Transitivity [a]) => [a] -> [a] -> [a] -> EqT [a]
assocP []     ys zs = refl ([] ++ (ys ++ zs)) 
assocP (x:xs) ys zs = trans ((x:xs) ++ (ys ++ zs)) 
                            (cons x (xs ++ (ys ++ zs)))
                            (cons x  ((xs ++ ys) ++ zs))
                            (refl ((x:xs) ++ (ys ++ zs)))
                            (eqRTCtx ((xs ++ (ys ++ zs))) ((xs ++ ys) ++ zs) (assocP xs ys zs) (cons x))
                            

{-@ reflect cons @-}
cons :: a -> [a] -> [a]
{-@ cons :: x:a -> y:[a] -> {v:[a] | v == x:y} @-}
cons x xs = x:xs

{-@ consP :: x:a -> xs:[a] -> {cons x xs == x:xs} @-}
consP :: a -> [a] -> ()
consP x xs = cons x xs *** QED 


reverseOneSwoopEq :: AEq [a] => EqT ([a] -> [a])
{-@ reverseOneSwoopEq :: AEq [a] => EqRT ([a] -> [a]) {fastReverse} {slowReverse} @-}
reverseOneSwoopEq = EqFun fastReverse slowReverse $ \xs ->
  EqSMT (fastReverse xs) (slowReverse xs) (reverseEq xs ? reflP (fastReverse xs))

{-@ reverseTEq :: AEq [a] => xs:[a] -> EqRT [a] {fastReverse xs} {slowReverse xs} @-}
reverseTEq :: AEq [a] => [a] -> EqT [a]
reverseTEq xs = EqSMT (fastReverse xs) (slowReverse xs) (reverseEq xs ? reflP (fastReverse xs))

{-@ reverseEq :: xs:[a] -> { fastReverse xs = slowReverse xs } @-}
reverseEq :: [a] -> ()
reverseEq xs 
  =     lemma xs [] 
      ? rightId (slowReverse xs)

{-@ reverseNoEq :: xs:[a] -> { fastReverse xs = slowReverse xs } @-}
reverseNoEq :: [a] -> ()
reverseNoEq xs 
  = fastReverse xs
  ? fastReverse' [] xs  
      ? lemma xs [] 
      ? rightId (slowReverse xs)
  ? slowReverse xs 
  *** QED


------------------------------------------------------------
-- | Bad proofs that should fail  --------------------------
------------------------------------------------------------


-- NIKI TO FIX: nothing gets checked with the below uncommented :(

{- 
reverseFunEqWrong :: Eq a => EqT ([a] -> [a])
{-@ fail reverseFunEqWrong @-}
{-@ reverseFunEqWrong :: Eq a => EqRT ([a] -> [a]) (fastReverse) (badReverse) @-}
reverseFunEqWrong = eqFun fastReverse slowReverse trivialTEq

-- this shouldn't be provable! we're sending the wrong goals to SMT :(
reverseFunEqDistressing :: Eq a => EqT ([a] -> [a])
{-@ fail reverseFunEqDistressing @-}
{-@ reverseFunEqDistressing :: Eq a => EqRT ([a] -> [a]) (fastReverse) (badReverse) @-}
reverseFunEqDistressing = eqFun fastReverse badReverse trivialTEq

-- this shouldn't be provable... so easily.
reverseFunEqTooGood :: Eq a => EqT ([a] -> [a])
{-@ fail reverseFunEqTooGood @-}
{-@ reverseFunEqTooGood :: Eq a => EqRT ([a] -> [a]) (fastReverse) (slowReverse) @-}
reverseFunEqTooGood = eqFun fastReverse slowReverse trivialTEq

{-@ trivialTEq :: Eq a => xs:[a] -> EqRT [a] (xs) (xs) @-}
trivialTEq :: Eq a => [a] -> EqT [a]
trivialTEq xs = eqSMT xs xs ()

{-@ reverseFunNoExt :: { fastReverse = slowReverse } @-}
{-@ fail reverseFunNoExt @-}
reverseFunNoExt :: ()
reverseFunNoExt = () ? reverseNoEq
-}
------------------------------------------------------------
-- | Helper Proofs  ----------------------------------------
------------------------------------------------------------

{-
Note: All the below are proved by SMT and without any `Eq [a]`
-}

{-@ lemma :: xs:[a] -> ys:[a] 
          -> { fastReverse' ys xs = slowReverse xs ++ ys } @-}
lemma :: [a] -> [a] -> ()
lemma [] _  = ()
lemma (x:xs) ys 
  = lemma xs (x:ys)  
  ? assoc (slowReverse xs) [x] ys 

{-@ rightId :: xs:[a] -> { xs ++ [] = xs } @-}
rightId :: [a] -> ()
rightId []     = ()
rightId (_:xs) = rightId xs 

{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a]
          -> { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc []     _  _  = ()
assoc (_:xs) ys zs = assoc xs ys zs 

------------------------------------------------------------
-- | Code --------------------------------------------------
------------------------------------------------------------

{-@ reflect fastReverse @-}
fastReverse :: [a] -> [a]
fastReverse xs = fastReverse' [] xs 

{-@ reflect fastReverse' @-}
fastReverse' :: [a] -> [a] -> [a]
fastReverse' acc [] = acc 
fastReverse' acc (x:xs) = fastReverse' (x:acc) xs 

{-@ reflect slowReverse @-}
slowReverse :: [a] -> [a]
slowReverse []     = [] 
slowReverse (x:xs) = slowReverse xs ++ [x]

{-@ reflect badReverse @-}
badReverse :: [a] -> [a] 
badReverse xs = xs 

{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x:(xs ++ ys)
         
