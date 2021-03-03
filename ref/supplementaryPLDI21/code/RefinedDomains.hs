{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-} 

module RefinedDomains where 

import PropositionalEquality 
-- import Language.Haskell.Liquid.ProofCombinators

--------------------------------------------------------------------------------
-- | Main theorem
--------------------------------------------------------------------------------

pf :: EqT (Integer -> Integer)
{-@ pf :: EqRT (x:{Integer | 0 <= x } -> Integer) add1Int add1Nat @-}
pf = EqFun add1Int add1Nat (\x -> eqSMT (add1Int x) (add1Nat x) (reflP (add1Int x)))

pf' :: EqT (Integer -> Integer)
{-@ pf' :: EqRT (x:{Integer | 0 <= x } -> {x:Integer | 0 <= x }) add1Int add1Nat @-}
pf' = EqFun add1Int add1Nat pf0' 

pf0' :: Integer -> EqT Integer
{-@ pf0' :: x:{Integer | 0 <= x } ->  EqRT {x:Integer | 0 <= x } (add1Int x) (add1Nat x) @-}
pf0' x = eqSMT (add1Int x)  (add1Nat x) (reflP (add1Int x)) 

pf'' :: EqT (Integer -> Integer)
{-@ pf'' :: EqRT (x:{Integer | 0 <= x } -> {v:Integer | v = x + 1 }) add1Int add1Nat @-}
pf'' = deqFun add1Int add1Nat pf0'' 

pf0'' :: Integer -> EqT Integer
{-@ pf0'' :: x:{Integer | 0 <= x } ->  EqRT {v:Integer | v = x + 1 } (add1Int x) (add1Nat x) @-}
pf0'' x = eqSMT (add1Int x)  (add1Nat x) (reflP (add1Int x)) 


--------------------------------------------------------------------------------
-- | Bad proofs that should fail
--------------------------------------------------------------------------------
{- 
pfBadRange :: () ->  EqT (Integer -> Integer)
{-@ fail pfBadRange @-}
{-@ pfBadRange :: () -> EqRT (x:{Integer | 0 <= x } -> {x:Integer | 0 > x }) add1Int add1Nat @-}
pfBadRange _ = eqFun add1Int add1Nat (\x -> eqSMT (add1Int x) (add1Nat x) ())

pf0BadRange :: Integer -> EqT Integer
{-@ fail pf0BadRange @-}
{-@ pf0BadRange :: x:{Integer | 0 <= x }-> EqRT {v:Integer | v < 0 } (add1Int x) (add1Nat x) @-}
pf0BadRange x = eqSMT (add1Int x) (add1Nat x) ()

pfBadDomain :: () -> EqT (Integer -> Integer)
{-@ fail pfBadDomain @-}
{-@ pfBadDomain :: () -> EqRT (x:Integer -> Integer) add1Int add1Nat @-}
pfBadDomain _ = eqFun add1Int add1Nat (\x -> eqSMT (add1Int x) (add1Nat x) ())

pf0BadDomain :: Integer -> EqT Integer
{-@ fail pf0BadDomain @-}
{-@ pf0BadDomain :: x:Integer-> EqRT Integer {add1Int x} (add1Nat x) @-}
pf0BadDomain x = eqSMT (add1Int x) (add1Nat x) () 
-}

--------------------------------------------------------------------------------
-- | Definitions for add1Int and g
--------------------------------------------------------------------------------

{-@ reflect add1Int @-}
add1Int :: Integer -> Integer 
add1Int x = x + 1 

{-@ reflect add1Nat @-}
add1Nat :: Integer -> Integer 
add1Nat x = if x >= 0 then x + 1 else 0
