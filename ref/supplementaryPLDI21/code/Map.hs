{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-} 

module Map where 

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (map)
import PropositionalEquality
import PEqProperties
import RefinedDomains

{-@ infix :  @-}


client :: [Integer] -> EqT [Integer] 
{-@ client :: xs:[{v:Integer | 0 <= v}] -> EqRT [Integer] {map add1Int xs} {map add1Nat xs}@-}
client = mapEq add1Int add1Nat pf 

client'' ::  EqT ([Integer] -> [Integer])
{-@ client'' ::  EqRT ([{v:Integer | 0 <= v}] -> [Integer]) {map add1Int} {map add1Nat}@-}
client'' = mapEq'' add1Int add1Nat pf 


mapEq     :: (a -> b) -> (a -> b) -> EqT (a -> b) -> [a] -> EqT [b]
{-@ mapEq :: f:(a -> b) -> g:(a -> b) ->
             EqRT (a -> b) {f} {g} ->
             xs:[a] -> EqRT [b] {map f xs} {map g xs} @-}
mapEq f g mpf xs =
  EqCtx f g mpf (flipMap xs)
  ? mapFlipMap f xs
  ? mapFlipMap g xs

mapFlipMap     :: (a -> b) -> [a] -> ()
{-@ mapFlipMap :: f:(a -> b) -> xs:[a] -> {map f xs = flipMap xs f} @-}
mapFlipMap _f _xs = ()

mapEq'     :: (Reflexivity [b], Transitivity [b]) => (a -> b) -> (a -> b) -> EqT (a -> b) -> [a] -> EqT [b]
{-@ mapEq' :: (Reflexivity [b], Transitivity [b]) => f:(a -> b) -> g:(a -> b) ->
                  EqRT (a -> b) {f} {g} ->
                  xs:[a] -> EqRT [b] {map f xs} {map g xs} @-}
mapEq' f g mpf xs =
  trans (map f xs)
        (flipMap xs f)
        (map g xs)
    (refl (map f xs))
    (trans (flipMap xs f)
           (flipMap xs g)
           (map g xs)
      (EqCtx f g mpf (flipMap xs))
      (refl (flipMap xs g)))

mapEq''     :: (a -> b) -> (a -> b) -> EqT (a -> b) -> EqT ([a] -> [b])
{-@ mapEq'' :: f:(a -> b) -> g:(a -> b) ->
               EqRT (a -> b) {f} {g} ->
               EqRT ([a] -> [b]) {map f} {map g} @-}
mapEq'' f g mpf = EqCtx f g mpf map   



------------------------------------------------------------
-- | Code --------------------------------------------------
------------------------------------------------------------

{-@ reflect flipMap @-}
flipMap :: [a] -> (a -> b) -> [b]
flipMap xs f = map f xs

{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map _f []     = []
map  f (x:xs) = f x : map f xs
