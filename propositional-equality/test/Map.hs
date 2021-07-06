{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-} 

module Map where 

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (map)
import Relation.Equality.Prop
import RefinedDomains
import Data.Refined.Unit

{-@ infix :  @-}


client :: [Integer] -> EqualityProp [Integer] 
{-@ client :: xs:[{v:Integer | 0 <= v}] -> EqualProp [Integer] {map add1Int xs} {map add1Nat xs}@-}
client = mapEq add1Int add1Nat pf 

client'' ::  EqualityProp ([Integer] -> [Integer])
{-@ client'' ::  EqualProp ([{v:Integer | 0 <= v}] -> [Integer]) {map add1Int} {map add1Nat}@-}
client'' = mapEq'' add1Int add1Nat pf 


mapEq     :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> [a] -> EqualityProp [b]
{-@ mapEq :: f:(a -> b) -> g:(a -> b) ->
             EqualProp (a -> b) {f} {g} ->
             xs:[a] -> EqualProp [b] {map f xs} {map g xs} @-}
mapEq f g mpf xs =
  substitutability (flipMap xs) f g mpf 
  ? mapFlipMap f xs
  ? mapFlipMap g xs

mapFlipMap     :: (a -> b) -> [a] -> ()
{-@ mapFlipMap :: f:(a -> b) -> xs:[a] -> {map f xs = flipMap xs f} @-}
mapFlipMap _f _xs = ()

mapEq'     :: (Reflexivity [b], Transitivity [b]) => (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> [a] -> EqualityProp [b]
{-@ mapEq' :: (Reflexivity [b], Transitivity [b]) => f:(a -> b) -> g:(a -> b) ->
                  EqualProp (a -> b) {f} {g} ->
                  xs:[a] -> EqualProp [b] {map f xs} {map g xs} @-}
mapEq' f g mpf xs =
  trans (map f xs)
        (flipMap xs f)
        (map g xs)
    (refl (map f xs))
    (trans (flipMap xs f)
           (flipMap xs g)
           (map g xs)
      (substitutability (flipMap xs) f g mpf )
      (refl (flipMap xs g)))

mapEq''     :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> EqualityProp ([a] -> [b])
{-@ mapEq'' :: f:(a -> b) -> g:(a -> b) ->
               EqualProp (a -> b) {f} {g} ->
               EqualProp ([a] -> [b]) {map f} {map g} @-}
mapEq'' f g mpf = substitutability map f g mpf    



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
