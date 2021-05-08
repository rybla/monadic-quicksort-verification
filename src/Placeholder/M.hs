{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Placeholder.M where

-- import qualified Control.Refined.Monad as Monad
-- import qualified Control.Refined.Monad.Array as Array
-- import qualified Control.Refined.Monad.Plus as Plus

import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Prelude hiding (Monad, length, pure, read, readList, seq, (+), (++), (>>), (>>=))

{-
# Synonyms
-}

{-@ reflect leq @-}
leq :: Int -> Int -> Bool
leq x y = x <= y

{-@ reflect geq @-}
geq :: Int -> Int -> Bool
geq x y = y <= x

{-
# M
-}

-- instances: Monad M, Plus M, Array M Int
data M :: * -> * where
  Pure :: a -> M a
  Bind :: M a -> (a -> M b) -> M b
  Epsilon :: M a
  Plus :: M a -> M a -> M a
  Read :: Natural -> M Int
  Write :: Natural -> Int -> M ()

-- TODO
-- interpretM :: Monad m -> Plus m -> Array m a -> M a -> m a
-- interpretM _ pls ary _m = undefined

{-
## Monad interface
-}

-- monad methods

{-@ reflect pure @-}
pure :: a -> M a
pure a = Pure a

{-@ reflect bind @-}
bind :: M a -> (a -> M b) -> M b
bind m k = Bind m k

{-@ infixl 1 >>= @-}
infixl 1 >>=

{-@ reflect >>= @-}
(>>=) :: M a -> (a -> M b) -> M b
m >>= k = Bind m k

-- monad functions

{-@ reflect seq @-}
seq :: M a -> M b -> M b
seq ma mb = ma >>= constant mb

{-@ infixl 1 >> @-}
infixl 1 >>

{-@ reflect >> @-}
(>>) :: M a -> M b -> M b
(>>) = seq

{-@ reflect kleisli @-}
kleisli :: (a -> M b) -> (b -> M c) -> (a -> M c)
kleisli k1 k2 x = k1 x >>= k2

{-@ infixr 1 >=> @-}
infixr 1 >=>

{-@ reflect >=> @-}
(>=>) :: (a -> M b) -> (b -> M c) -> (a -> M c)
(>=>) = kleisli

{-@
kleisli_unfold :: k1:(a -> M b) -> k2:(b -> M c) -> x:a ->
  EqualProp (M c) {kleisli k1 k2 x} {k1 x >>= k2}
@-}
kleisli_unfold :: (a -> M b) -> (b -> M c) -> a -> EqualityProp (M c)
kleisli_unfold k1 k2 x = reflexivity (kleisli k1 k2 x)

{-@ reflect join @-}
join :: M (M a) -> M a
join mm = mm >>= identity

{-@ reflect liftM @-}
liftM :: (a -> b) -> (M a -> M b)
liftM f m = m >>= \x -> pure (f x)

{-@ reflect liftM2 @-}
liftM2 :: (a -> b -> c) -> (M a -> M b -> M c)
liftM2 f ma mb = ma >>= \x -> mb >>= \y -> pure (f x y)

{-@ reflect second @-}
second :: (b -> M c) -> (a, b) -> M (a, c)
second k (x, y) = k y >>= \y' -> pure (x, y')

-- monad laws

{-@
assume
bind_identity_left :: x:a -> k:(a -> M b) -> EqualProp (M b) {pure x >>= k} {k x}
@-}
bind_identity_left :: a -> (a -> M b) -> EqualityProp (M b)
bind_identity_left _ _ = assumedProp

{-- TODO
I hate that I seem to have to do this, because apparently I need to use the
outfixed  notation sometimes due to parsing bugs. And because of a parsing bug
I can't prove or make use of an extensional equality between `bind` and `(>>=)`.
But I'm hoping that I don't need to have toooo many `_outfix` proxy lemmas.
-}
{-@
assume
bind_identity_left_outfix :: x:a -> k:(a -> M b) -> EqualProp (M b) {bind (pure x) k} {k x}
@-}
bind_identity_left_outfix :: a -> (a -> M b) -> EqualityProp (M b)
bind_identity_left_outfix _ _ = assumedProp

{-@
assume
bind_identity_right :: m:M a -> EqualProp (M a) {m >>= pure} {m}
@-}
bind_identity_right :: M a -> EqualityProp (M a)
bind_identity_right _ = assumedProp

{-@
assume
bind_associativity :: m:M a -> k1:(a -> M b) -> k2:(b -> M c) -> EqualProp (M c) {(m >>= k1) >>= k2} {m >>= (k1 >=> k2)}
@-}
bind_associativity :: M a -> (a -> M b) -> (b -> M c) -> EqualityProp (M c)
bind_associativity _ _ _ = assumedProp

-- monad lemmas

{-@
seq_associativity ::
  Equality (M c) => ma:M a -> mb:M b -> mc:M c -> EqualProp (M c) {(ma >> mb) >> mc} {ma >> mb >> mc}
@-}
seq_associativity ::
  Equality (M c) => M a -> M b -> M c -> EqualityProp (M c)
seq_associativity ma mb mc =
  [eqpropchain|
      (ma >> mb) >> mc 
    %==
      (ma >>= constant mb) >> mc
    %==
      (ma >>= constant mb) >>= constant mc
        %by undefined %-- TODO: smt crash: invalid qualiied identifier, sort mismatch
    %==
      ma >>= (constant mb >=> constant mc)
        %by bind_associativity ma (constant mb) (constant mc)
    %==
      ma >>= (\x -> (constant mb x >>= constant mc))
    %==
      ma >>= (\x -> (mb >>= constant mc))
        %by %rewrite (\x -> (constant mb x >>= constant mc)) 
                 %to (\x -> (mb >>= constant mc))
        %by %extend x
        %by %reflexivity
    %==
      ma >>= constant (mb >>= constant mc)
        %by %rewrite \x -> (mb >>= constant mc)
                 %to constant (mb >>= constant mc)
        %by %extend x 
        %by %reflexivity
    %==
      ma >> (mb >>= constant mc)
    %==
      ma >> mb >> mc 
  |]

{-@
seq_identity_left :: Equality (M b) =>
  x:a -> m:M b ->
  EqualProp (M b) {pure x >> m} {m}
@-}
seq_identity_left :: Equality (M b) => a -> M b -> EqualityProp (M b)
seq_identity_left x m =
  [eqpropchain|
      pure x >> m
    %== 
      pure x >>= \_ -> m
    %==
      (\_ -> m) x
        %by bind_identity_left x (\_ -> m)
    %== 
      m
  |]

-- TODO: other monad lemmas

{-
## Plus interface
-}

-- plus methods

{-@ reflect epsilon @-}
epsilon :: M a
epsilon = Epsilon

{-@ reflect plus @-}
plus :: M a -> M a -> M a
plus = Plus

{-@ infixl 3 <+> @-}
infixl 3 <+>

{-@ reflect <+> @-}
(<+>) :: M a -> M a -> M a
(<+>) = plus

-- plus functions

{-@ reflect plusF @-}
plusF :: (a -> M b) -> (a -> M b) -> (a -> M b)
plusF k1 k2 x = k1 x <+> k2 x

{-@ reflect guard @-}
guard :: Bool -> M ()
guard b = if b then pure () else epsilon

{-@ reflect guardBy @-}
guardBy :: (a -> Bool) -> a -> M a
guardBy p x = guard (p x) >> pure x

-- plus laws

{-@
assume
plus_identity_left :: m:M a -> EqualProp (M a) {epsilon <+> m} {m}
@-}
plus_identity_left :: M a -> EqualityProp (M a)
plus_identity_left _ = assumedProp

{-@
assume
plus_distributivity_left :: m1:M a -> m2:M a -> k:(a -> M b) -> EqualProp (M b) {(m1 <+> m2) >>= k} {(m1 >>= k) <+> (m2 >>= k)}
@-}
plus_distributivity_left :: M a -> M a -> (a -> M b) -> EqualityProp (M b)
plus_distributivity_left _ _ _ = assumedProp

{-@ reflect plus_distributivity_right_aux @-}
plus_distributivity_right_aux :: (a -> M b) -> (a -> M b) -> a -> M b
plus_distributivity_right_aux k1 k2 x = k1 x <+> k2 x

{-@
assume
plus_distributivity_right :: m:M a -> k1:(a -> M b) -> k2:(a -> M b) -> EqualProp (M b) {m >>= plus_distributivity_right_aux k1 k2} {(m >>= k1) <+> (m >>= k2)}
@-}
plus_distributivity_right :: M a -> (a -> M b) -> (a -> M b) -> EqualityProp (M b)
plus_distributivity_right _ _ _ = assumedProp

{-@
assume
bind_zero_left :: k:(a -> M b) -> EqualProp (M b) {epsilon >>= k} {epsilon}
@-}
bind_zero_left :: (a -> M b) -> EqualityProp (M b)
bind_zero_left _ = assumedProp

{-@
assume
bind_zero_right :: m:M a -> EqualProp (M b) {m >> epsilon} {epsilon}
@-}
bind_zero_right :: M a -> EqualityProp (M b)
bind_zero_right _ = assumedProp

-- plus lemmas

{-@
type RefinesPlus a M1 M2 = EqualProp (M a) {plus M1 M2} {M2}
@-}

{-@
type RefinesPlusF a b K1 K2 = x:a -> EqualProp (M b) {plus (K1 x) (K2 x)} {K2 x}
@-}

{-@
refinesplus_equalprop :: Equality (M a) =>
  m1:M a -> m2:M a ->
  EqualProp (M a) {m1} {m2} ->
  RefinesPlus a {m1} {m2}
@-}
refinesplus_equalprop :: Equality (M a) => M a -> M a -> EqualityProp (M a) -> EqualityProp (M a)
refinesplus_equalprop = undefined -- TODO

{-@
refinesplus_reflexivity :: Equality (M a) =>
  m:M a -> RefinesPlus a {m} {m}
@-}
refinesplus_reflexivity :: Equality (M a) => M a -> EqualityProp (M a)
refinesplus_reflexivity m =
  [eqpropchain|
      m <+> m
    %==
      m 
        %by undefined 
        %-- TODO: not sure...
  |]

-- TODO: other lemmas about RefinesPlus

{-@
refinesplus_transitivity :: Equality (M a) =>
  m1:M a -> m2:M a -> m3:M a ->
  RefinesPlus a {m1} {m2} ->
  RefinesPlus a {m2} {m3} ->
  RefinesPlus a {m1} {m3}
@-}
refinesplus_transitivity :: Equality (M a) => M a -> M a -> M a -> EqualityProp (M a) -> EqualityProp (M a) -> EqualityProp (M a)
refinesplus_transitivity m1 m2 m3 h12 h23 = undefined -- TODO

{-
## Array interface
-}

-- array methods

{-@ reflect read @-}
read :: Natural -> M Int
read = Read

{-@ reflect write @-}
write :: Natural -> Int -> M ()
write = Write

-- array methods

-- TODO

{-@ reflect readList @-}
readList :: Natural -> Natural -> M (List Int)
readList i Z = pure Nil
readList i (S n) = liftM2 Cons (read i) (readList (S i) n)

{-@ reflect writeList @-}
writeList :: Natural -> List Int -> M ()
writeList i Nil = pure it
writeList i (Cons x xs) = write i x >> writeList (S i) xs

{-@ reflect writeListToLength @-}
writeListToLength :: Natural -> List Int -> M Natural
writeListToLength i xs = writeList i xs >> pure (length xs)

{-@ reflect writeListToLength2 @-}
writeListToLength2 :: Natural -> (List Int, List Int) -> M (Natural, Natural)
writeListToLength2 i (xs, ys) = writeList i (xs ++ ys) >> pure (length xs, length ys)

{-@ reflect writeListToLength3 @-}
writeListToLength3 :: Natural -> (List Int, List Int, List Int) -> M (Natural, Natural, Natural)
writeListToLength3 i (xs, ys, zs) = writeList i (xs ++ ys ++ zs) >> pure (length xs, length ys, length zs)

{-@ reflect swap @-}
swap :: Natural -> Natural -> M ()
swap i j = read i >>= \x -> read j >>= \y -> write i y >> write j x

-- array laws

{-@
assume
bind_read_write :: i:Natural -> EqualProp (m ()) {read i >>= write i} {pure it}
@-}
bind_read_write :: Natural -> EqualityProp (m ())
bind_read_write _ = assumedProp

{-@
assume
seq_write_read :: i:Natural -> x:Int -> EqualProp (m Int) {write i x >> read i} {write i x >> pure x}
@-}
seq_write_read :: Natural -> Int -> EqualityProp (m Int)
seq_write_read _ _ = assumedProp

{-@
assume
seq_write_write :: i:Natural -> x:Int -> y:Int -> EqualProp (m Unit) {write i x >> write i y} {write i y}
@-}
seq_write_write :: Natural -> Int -> Int -> EqualityProp (m Unit)
seq_write_write _ _ _ = assumedProp

{-@
assume
liftM_read :: i:Natural -> f:(Int -> Int -> Int) -> EqualProp (M Int) {liftM2 f (read i) (read i)} {liftM (diagonalize f) (read i)}
@-}
liftM_read :: Natural -> (Int -> Int -> Int) -> EqualityProp (M Int)
liftM_read _ _ = assumedProp

{-@
assume
seq_commutativity_write :: i:Natural -> j:{j:Natural | i /= j} -> x:Int -> y:Int -> EqualProp (M Unit) {write i x >> write j y} {write j y >> write i x}
@-}
seq_commutativity_write :: Natural -> Natural -> Int -> Int -> EqualityProp (M ())
seq_commutativity_write _ _ _ _ = assumedProp

{-@
assume
seq_associativity_write :: i:Natural -> j:{j:Natural | i /= j} -> x:Int -> y:Int -> EqualProp (m Unit) {(read i >> pure it) >> write j x} {write j x >> (read i >> pure it)}
@-}
seq_associativity_write :: Natural -> Natural -> Int -> Int -> EqualityProp (m Unit)
seq_associativity_write _ _ _ _ = assumedProp

-- array lemmas

{-@
writeList_append :: i:Natural -> xs:List Int -> ys:List Int -> EqualProp (M Unit) {writeList i (append xs ys)} {writeList i xs >> writeList (add i (length xs)) ys}
@-}
writeList_append :: Natural -> List Int -> List Int -> EqualityProp (M ())
writeList_append = undefined -- TODO: migrate proof from Control.Monad.Array