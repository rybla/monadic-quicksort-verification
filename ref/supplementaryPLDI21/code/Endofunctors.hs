{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

{-@ LIQUID "--reflection"  @-} 
{-@ LIQUID "--ple"         @-}
{- LIQUID "--fast"        @-}
{-@ LIQUID "--no-adt"      @-} 

module Endofunctors where

import Language.Haskell.Liquid.ProofCombinators
import PropositionalEquality
import Prelude hiding (id, mempty, mappend)

import PEqProperties

type Endo a = a -> a

{-@ reflect mempty @-}
mempty :: Endo a
mempty a = a

{-@ reflect mappend @-}
mappend :: Endo a -> Endo a -> Endo a
mappend f g a = f (g a)

{-
(x <> y) <> z = x <> (y <> z) -- associativity
mempty <> x = x               -- left identity
x <> mempty = x               -- right identity
-}

{-@ monoid_leftIdentity :: Reflexivity a => x:(Endo a) -> EqRT (Endo a) {mappend mempty x} {x} @-}
monoid_leftIdentity :: Reflexivity a => (Endo a) -> EqT (Endo a)
monoid_leftIdentity x =
  EqFun (mappend mempty x) x $ \a ->
    refl (mappend mempty x a) ?
         (    mappend mempty x a
          =~= mempty (x a)
          =~= x a
          *** QED)

{-@ monoid_rightIdentity :: Reflexivity a => x:(Endo a) -> EqRT (Endo a) {x} {mappend x mempty} @-}
monoid_rightIdentity :: Reflexivity a => Endo a -> EqT (Endo a)
monoid_rightIdentity x =
    EqFun x (mappend x mempty) $ \a ->
      refl (x a) ? -- (mappend x mempty a)
           (    x a
            =~= x (mempty a)
            =~= mappend x mempty a
            *** QED)

{-@ monoid_associativity :: Reflexivity a =>
      x:(Endo a) -> y:(Endo a) -> z:(Endo a) ->
      EqRT (Endo a) {mappend (mappend x y) z} {mappend x (mappend y z)} @-}
monoid_associativity :: Reflexivity a => Endo a -> Endo a -> Endo a -> EqT (Endo a)
monoid_associativity x y z =
  EqFun (mappend (mappend x y) z) (mappend x (mappend y z)) $ \a ->
    refl (mappend (mappend x y) z a) ?
         (    mappend (mappend x y) z a
          =~= (mappend x y) (z a)
          =~= x (y (z a))
          =~= x (mappend y z a)
          =~= mappend x (mappend y z) a
          *** QED)
