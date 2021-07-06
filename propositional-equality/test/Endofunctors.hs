{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

{-@ LIQUID "--ple"         @-}

module Endofunctors where

-- macros

import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Prelude hiding (id, mappend, mempty)

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

{-@ monoid_leftIdentity :: Reflexivity a => x:(Endo a) -> EqualProp (Endo a) {mappend mempty x} {x} @-}
monoid_leftIdentity :: Reflexivity a => (Endo a) -> EqualityProp (Endo a)
monoid_leftIdentity x =
  extensionality (mappend mempty x) x $ \a ->
    refl (mappend mempty x a)
      ? ( mappend mempty x a
            =~= mempty (x a)
            =~= x a
            *** QED
        )

{-@
monoid_leftIdentity_macros :: (Equality (Endo a), Equality a) => x:(Endo a) -> EqualProp (Endo a) {mappend mempty x} {x}
@-}
monoid_leftIdentity_macros :: (Equality (Endo a), Equality a) => Endo a -> EqualityProp (Endo a)
monoid_leftIdentity_macros x =
  [eqp| mappend mempty x
    %== apply $ \a -> mappend mempty x a  %by %extend a %by %reflexivity
    %== apply $ \a -> mempty (x a)        %by %extend a %by %reflexivity
    %== apply $ \a -> x a                 %by %extend a %by %reflexivity
    %== x                                 %by %extend a %by %reflexivity
  |]

{-@ monoid_rightIdentity :: Reflexivity a => x:(Endo a) -> EqualProp (Endo a) {x} {mappend x mempty} @-}
monoid_rightIdentity :: Reflexivity a => Endo a -> EqualityProp (Endo a)
monoid_rightIdentity x =
  extensionality x (mappend x mempty) $ \a ->
    refl (x a)
      ? ( x a -- (mappend x mempty a)
            =~= x (mempty a)
            =~= mappend x mempty a
            *** QED
        )

{-@ monoid_rightIdentity_macros :: (Equality a, Equality (Endo a)) => x:(Endo a) -> EqualProp (Endo a) {x} {mappend x mempty} @-}
monoid_rightIdentity_macros :: (Equality a, Equality (Endo a)) => Endo a -> EqualityProp (Endo a)
monoid_rightIdentity_macros x =
  [eqp| x
    %== apply $ \a -> x a                 %by %extend a %by %reflexivity
    %== apply $ \a -> x (mempty a)        %by %extend a %by %reflexivity
    %== apply $ \a -> mappend x mempty a  %by %extend a %by %reflexivity
    %== mappend x mempty                  %by %extend a %by %reflexivity
  |]

{-@ monoid_associativity :: Reflexivity a =>
      x:(Endo a) -> y:(Endo a) -> z:(Endo a) ->
      EqualProp (Endo a) {mappend (mappend x y) z} {mappend x (mappend y z)} @-}
monoid_associativity :: Reflexivity a => Endo a -> Endo a -> Endo a -> EqualityProp (Endo a)
monoid_associativity x y z =
  extensionality (mappend (mappend x y) z) (mappend x (mappend y z)) $ \a ->
    refl (mappend (mappend x y) z a)
      ? ( mappend (mappend x y) z a
            =~= (mappend x y) (z a)
            =~= x (y (z a))
            =~= x (mappend y z a)
            =~= mappend x (mappend y z) a
            *** QED
        )

{-@ monoid_associativity_macros :: (Equality a, Equality (Endo a)) =>
      x:(Endo a) -> y:(Endo a) -> z:(Endo a) ->
      EqualProp (Endo a) {mappend (mappend x y) z} {mappend x (mappend y z)} @-}
monoid_associativity_macros :: (Equality a, Equality (Endo a)) => Endo a -> Endo a -> Endo a -> EqualityProp (Endo a)
monoid_associativity_macros x y z =
  [eqp| mappend (mappend x y) z
    %== apply $ \a -> mappend (mappend x y) z a  %by %extend a %by %reflexivity
    %== apply $ \a -> (mappend x y) (z a)        %by %extend a %by %reflexivity
    %== apply $ \a -> x (y (z a))                %by %extend a %by %reflexivity
    %== apply $ \a -> x ((mappend y z) a)        %by %extend a %by %reflexivity
    %== apply $ \a -> mappend x (mappend y z) a  %by %extend a %by %reflexivity
    %== mappend x (mappend y z)                  %by %extend a %by %reflexivity
  |]
