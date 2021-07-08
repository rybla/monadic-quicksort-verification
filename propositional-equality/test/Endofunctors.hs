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
import Prelude hiding (id, mconcat, mempty)

type Endo a = a -> a

{-@ reflect mempty @-}
mempty :: Endo a
mempty a = a

{-@ reflect mconcat @-}
mconcat :: Endo a -> Endo a -> Endo a
mconcat f g a = f (g a)

{-
(x <> y) <> z = x <> (y <> z) -- associativity
mempty <> x = x               -- left identity
x <> mempty = x               -- right identity
-}

{-@ monoid_leftIdentity :: Reflexivity a => x:(Endo a) -> EqualProp (Endo a) {mconcat mempty x} {x} @-}
monoid_leftIdentity :: Reflexivity a => (Endo a) -> EqualityProp (Endo a)
monoid_leftIdentity x =
  extensionality (mconcat mempty x) x $ \a ->
    refl (mconcat mempty x a)
      ? ( mconcat mempty x a
            =~= mempty (x a)
            =~= x a
            *** QED
        )

{-@
monoid_leftIdentity_macros :: (Equality (Endo a), Equality a) => x:(Endo a) -> EqualProp (Endo a) {mconcat mempty x} {x}
@-}
monoid_leftIdentity_macros :: (Equality (Endo a), Equality a) => Endo a -> EqualityProp (Endo a)
monoid_leftIdentity_macros x =
  [eqp| mconcat mempty x
    %== apply $ \a -> mconcat mempty x a  %by %extend a %by %reflexivity
    %== apply $ \a -> mempty (x a)        %by %extend a %by %reflexivity
    %== apply $ \a -> x a                 %by %extend a %by %reflexivity
    %== x                                 %by %extend a %by %reflexivity
  |]

{-@ monoid_rightIdentity :: Reflexivity a => x:(Endo a) -> EqualProp (Endo a) {x} {mconcat x mempty} @-}
monoid_rightIdentity :: Reflexivity a => Endo a -> EqualityProp (Endo a)
monoid_rightIdentity x =
  extensionality x (mconcat x mempty) $ \a ->
    refl (x a)
      ? ( x a -- (mconcat x mempty a)
            =~= x (mempty a)
            =~= mconcat x mempty a
            *** QED
        )

{-@ monoid_rightIdentity_macros :: (Equality a, Equality (Endo a)) => x:(Endo a) -> EqualProp (Endo a) {x} {mconcat x mempty} @-}
monoid_rightIdentity_macros :: (Equality a, Equality (Endo a)) => Endo a -> EqualityProp (Endo a)
monoid_rightIdentity_macros x =
  [eqp| x
    %== apply $ \a -> x a                 %by %extend a %by %reflexivity
    %== apply $ \a -> x (mempty a)        %by %extend a %by %reflexivity
    %== apply $ \a -> mconcat x mempty a  %by %extend a %by %reflexivity
    %== mconcat x mempty                  %by %extend a %by %reflexivity
  |]

{-@ monoid_associativity :: Reflexivity a =>
      x:(Endo a) -> y:(Endo a) -> z:(Endo a) ->
      EqualProp (Endo a) {mconcat (mconcat x y) z} {mconcat x (mconcat y z)} @-}
monoid_associativity :: Reflexivity a => Endo a -> Endo a -> Endo a -> EqualityProp (Endo a)
monoid_associativity x y z =
  extensionality (mconcat (mconcat x y) z) (mconcat x (mconcat y z)) $ \a ->
    refl (mconcat (mconcat x y) z a)
      ? ( mconcat (mconcat x y) z a
            =~= (mconcat x y) (z a)
            =~= x (y (z a))
            =~= x (mconcat y z a)
            =~= mconcat x (mconcat y z) a
            *** QED
        )

{-@ monoid_associativity_macros :: (Equality a, Equality (Endo a)) =>
      x:(Endo a) -> y:(Endo a) -> z:(Endo a) ->
      EqualProp (Endo a) {mconcat (mconcat x y) z} {mconcat x (mconcat y z)} @-}
monoid_associativity_macros :: (Equality a, Equality (Endo a)) => Endo a -> Endo a -> Endo a -> EqualityProp (Endo a)
monoid_associativity_macros x y z =
  [eqp| mconcat (mconcat x y) z
    %== apply $ \a -> mconcat (mconcat x y) z a  %by %extend a %by %reflexivity
    %== apply $ \a -> (mconcat x y) (z a)        %by %extend a %by %reflexivity
    %== apply $ \a -> x (y (z a))                %by %extend a %by %reflexivity
    %== apply $ \a -> x ((mconcat y z) a)        %by %extend a %by %reflexivity
    %== apply $ \a -> mconcat x (mconcat y z) a  %by %extend a %by %reflexivity
    %== mconcat x (mconcat y z)                  %by %extend a %by %reflexivity
  |]
