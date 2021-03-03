{-# LANGUAGE FlexibleInstances #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt"     @-}
{-@ LIQUID "--ple"        @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}

module PropositionalEquality
  ( EqT (..),
    AEq (..),
    eqRTCtx,
    deqFun,
    eqSMT,
  )
where

{-@ measure eqT :: a -> a -> Bool @-}
{-@ type EqRT a E1 E2 = {v:EqT a | eqT E1 E2} @-}

{-@ eqRTCtx :: x:a -> y:a -> EqRT a {x} {y} -> ctx:(a -> b) -> EqRT b {ctx x} {ctx y}  @-}
eqRTCtx :: a -> a -> EqT a -> (a -> b) -> EqT b
eqRTCtx = EqCtx

{-@ ignore deqFun @-}
{-@ deqFun :: forall<p :: a -> b -> Bool>. f:(a -> b) -> g:(a -> b)
          -> (x:a -> EqRT b<p x> {f x} {g x}) -> EqRT (y:a -> b<p y>) {f} {g}  @-}
deqFun :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)
deqFun = EqFun

{-@ _eqFun :: f:(a -> b) -> g:(a -> b)
          -> (x:a -> EqRT b {f x} {g x}) -> EqRT (a -> b) {f} {g}  @-}
_eqFun :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)
_eqFun = EqFun

{-@ ignore eqSMT @-}
{-@ assume eqSMT :: forall <p :: a -> Bool>.
      AEq a => x:a<p> -> y:a<p> ->
      {v:() | bbEq x y} ->
      EqRT (a<p>) {x} {y}
@-}
eqSMT :: AEq a => a -> a -> () -> EqT a
eqSMT x y p = EqSMT x y p

data EqT :: * -> * where
  EqSMT :: AEq a => a -> a -> () -> EqT a
  EqFun :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)
  EqCtx :: a -> a -> EqT a -> (a -> b) -> EqT b

-- NV: the below parses with the compiler plugin but to parse with the lh executable you need to remove the |//.
{-@ data EqT  :: * -> *  where
        EqSMT  :: AEq a => x:a -> y:a -> {v:() | bbEq x y} -> EqRT a {x} {y}
      |  EqFun  :: ff:(a -> b) -> gg:(a -> b) -> (x:a -> EqRT b {ff x} {gg x}) -> EqRT (a -> b) {ff} {gg}
      |  EqCtx  :: x:a -> y:a -> EqRT a {x} {y} -> ctx:(a -> b) -> EqRT b {ctx x} {ctx y}
@-}

class AEq a where
  bEq :: a -> a -> Bool
  reflP :: a -> ()
  symmP :: a -> a -> ()
  transP :: a -> a -> a -> ()

{-@ measure bbEq :: a -> a -> Bool @-}
{-@ class AEq a where
     bEq    :: x:a -> y:a -> {v:Bool | v <=> bbEq x y }
     reflP  :: x:a -> {bbEq x x}
     symmP  :: x:a -> y:a -> { bbEq x y => bbEq y x }
     transP :: x:a -> y:a -> z:a -> { ( bbEq x y && bbEq y z) => bbEq x z }
@-}

instance AEq Integer where
  bEq = bEqInteger
  reflP x = const () (bEqInteger x x)
  symmP x y = () `const` (bEqInteger x y)
  transP x y _ = () `const` (bEqInteger x y)

instance AEq Bool where
  bEq = bEqBool
  reflP x = const () (bEqBool x x)
  symmP x y = () `const` (bEqBool x y)
  transP x y _ = () `const` (bEqBool x y)

{-@ assume bEqInteger :: x:Integer -> y:Integer -> {v:Bool | (v <=> bbEq x y) && (v <=> x = y)} @-}
bEqInteger :: Integer -> Integer -> Bool
bEqInteger x y = x == y

{-@ assume bEqBool :: x:Bool -> y:Bool -> {v:Bool | (v <=> bbEq x y) && (v <=> x = y)} @-}
bEqBool :: Bool -> Bool -> Bool
bEqBool x y = x == y
