{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-@ LIQUID "--compile-spec" @-}
-- import qualified Control.Refined.Monad as Monad
-- import qualified Control.Refined.Monad.Array as Array
-- import qualified Control.Refined.Monad.Plus as Plus
{-
# Synonyms
-}
{-@ reflect leq @-}
{-@ reflect geq @-}
{-
# M
-}
-- instances: Monad M, Plus M, Array M Int
-- only performs monad and plus effects i.e. does not perform array effects
{-@ reflect onlyMonadPlus @-}
{-@ reflect onlyMonadPlusF @-}
-- TODO
-- TODO
-- interpretM :: Monad m -> Plus m -> Array m a -> M a -> m a
-- interpretM _ pls _m =
{-
## Monad interface
-}
-- monad methods
{-@ reflect pure @-}
{-@ reflect bind @-}
{-@ infixl 1 >>= @-}
{-@ reflect >>= @-}
-- monad functions
{-@ reflect seq @-}
{-@ infixl 1 >> @-}
{-@ reflect >> @-}
{-@ reflect kleisli @-}
{-@ infixr 1 >=> @-}
{-@ reflect >=> @-}
{-@
kleisli_unfold :: k1:(a -> M b) -> k2:(b -> M c) -> x:a ->
  EqualProp (M c) {kleisli k1 k2 x} {k1 x >>= k2}
@-}
{-@ reflect join @-}
{-@ reflect liftM @-}
{-@ reflect liftM_aux @-}
{-@ reflect liftM2 @-}
{-@ reflect liftM2_aux @-}
{-@ reflect liftM2_aux_aux @-}
{-@ reflect second @-}
{-@ reflect bind2 @-}
{-@ reflect bindFirst @-}
{-@ reflect pureF @-}
-- monad laws
{-@
subst_cont ::
  m:M a -> k1:(a -> M b) -> k2:(a -> M b) ->
  (x:a -> EqualProp (M b) {k1 x} {k2 x}) ->
  EqualProp (M b) {m >>= k1} {m >>= k2}
@-}
{-@ assume
subst_curr ::
  m1:M a -> m2:M a -> k:(a -> M b) ->
  (EqualProp (M a) {m1} {m2}) ->
  EqualProp (M b) {m1 >>= k} {m2 >>= k}
@-}
{-@
assume
pure_bind :: x:a -> k:(a -> M b) -> EqualProp (M b) {pure x >>= k} {k x}
@-}
{-@
assume
pure_bind_outfix :: x:a -> k:(a -> M b) -> EqualProp (M b) {bind (pure x) k} {k x}
@-}
{-@
assume
bind_identity_right :: m:M a -> EqualProp (M a) {m >>= pure} {m}
@-}
{-@
assume
bind_associativity ::
  Equality (M c) =>
  m:M a -> k1:(a -> M b) -> k2:(b -> M c) ->
  EqualProp (M c)
    {m >>= k1 >>= k2}
    {m >>= (k1 >=> k2)}
@-}
{-@
assume
bind_associativity_nofix ::
  Equality (M c) =>
  m:M a -> k1:(a -> M b) -> k2:(b -> M c) ->
  EqualProp (M c)
    {m >>= k1 >>= k2}
    {m >>= kleisli k1 k2}
@-}
-- monad lemmas
{-@
seq_associativity ::
  Equality (M c) => ma:M a -> mb:M b -> mc:M c ->
  EqualProp (M c)
    {(ma >> mb) >> mc}
    {ma >> mb >> mc}
@-}
{-@
seq_identity_left :: Equality (M b) =>
  x:a -> m:M b ->
  EqualProp (M b) {pure x >> m} {m}
@-}
-- implied by apply_if
{-@
bind_if ::
  Equality (M b) =>
  b:Bool -> m1:M a -> m2:M a -> k:(a -> M b) ->
  EqualProp (M b)
    {(if b then m1 else m2) >>= k}
    {if b then m1 >>= k else m2 >>= k}
@-}
{-@
seq_bind_associativity ::
  (Equality (M c), Equality (a -> M c)) =>
  m1:M a -> m2:M b -> k:(b -> M c) ->
  EqualProp (M c)
    {m1 >> m2 >>= k}
    {m1 >> (m2 >>= k)}
@-}
{-@
bind_associativity4 ::
  Equality (M d) =>
  m:M a -> k1:(a -> M b) -> k2:(b -> M c) -> k3:(c -> M d) ->
  EqualProp (M d)
    {m >>= k1 >>= k2 >>= k3}
    {m >>= (k1 >=> (k2 >=> k3))}
@-}
{-@
seq_associativity4 ::
  Equality (M d) =>
  ma:M a -> mb:M b -> mc:M c -> md:M d ->
  EqualProp (M d)
    {ma >> mb >> mc >> md}
    {ma >> (mb >> (mc >> md))}
@-}
{-@
seq_pure_bind ::
  (Equality (M c), Equality (a -> M c)) =>
  m:M a -> x:b -> k:(b -> M c) ->
  EqualProp (M c)
    {m >> pure x >>= k}
    {m >> (pure x >>= k)}
@-}
{-@
seq_if_bind ::
  (Equality (M c), Equality (a -> M c)) =>
  m:M a -> b:Bool -> m1:M b -> m2:M b -> k:(b -> M c) ->
  EqualProp (M c)
    {m >> (if b then m1 else m2) >>= k}
    {m >> if b then m1 >>= k else m2 >>= k}
@-}
{-@
pure_kleisli ::
  Equality (M c) =>
  f:(a -> b) -> k:(b -> M c) -> x:a ->
  EqualProp (M c)
    {kleisli (compose pure f) k x}
    {compose k f x}
@-}
{-@
seq_bind_seq_associativity ::
  (Equality (a -> M c), Equality (M d), Equality (M c)) =>
  m1:M a -> m2:M b -> k:(b -> M c) -> m3:M d ->
  EqualProp (M d)
    {m1 >> m2 >>= k >> m3}
    {m1 >> (m2 >>= k >> m3)}
@-}
{-@ reflect kseq @-}
{-@ reflect seqk @-}
{-@
bind_seq_associativity ::
  (Equality (M c), Equality (a -> M c)) =>
  m1:M a -> k:(a -> M b) -> m2:M c ->
  EqualProp (M c)
    {m1 >>= k >> m2}
    {m1 >>= kseq k m2}
@-}
{-@
assume
seq_pure_unit ::
  m:M Unit ->
  EqualProp (M Unit)
    {m}
    {m >> pure it}
@-}
{-@
kleisli_associativity ::
    (Equality (M d)) => k1:(a -> M b) -> k2:(b -> M c) -> k3:(c -> M d) -> x:a ->
    EqualProp (M d)
        {kleisli k1 (kleisli k2 k3) x}
        {kleisli (kleisli k1 k2) k3 x}
@-}
-- TODO: other monad lemmas
{-
## Plus interface
-}
-- plus methods
{-@ reflect epsilon @-}
{-@ reflect plus @-}
{-@ infixl 3 <+> @-}
{-@ reflect <+> @-}
-- plus functions
{-@ reflect plusF @-}
{-@ reflect guard @-}
{-@ reflect guardBy @-}
-- plus laws
{-@
assume
plus_identity_left :: m:M a -> EqualProp (M a) {epsilon <+> m} {m}
@-}
{-@
assume
plus_associativity ::
  (Equality (M a)) =>
  m1:M a -> m2:M a -> m3:M a ->
  EqualProp (M a)
    {m1 <+> m2 <+> m3}
    {m1 <+> (m2 <+> m3)}
@-}
{-@
assume
plus_idempotency :: m:M a -> EqualProp (M a) {m <+> m} {m}
@-}
{-@
assume
plus_commutativity :: m1:M a -> m2:M a -> EqualProp (M a) {m1 <+> m2} {m2 <+> m1}
@-}
{-@
assume
plus_distributivity_left :: m1:M a -> m2:M a -> k:(a -> M b) -> EqualProp (M b) {(m1 <+> m2) >>= k} {(m1 >>= k) <+> (m2 >>= k)}
@-}
{-@ reflect plus_distributivity_right_aux @-}
{-@
assume
plus_distributivity_right :: m:M a -> k1:(a -> M b) -> k2:(a -> M b) -> EqualProp (M b) {m >>= plus_distributivity_right_aux k1 k2} {(m >>= k1) <+> (m >>= k2)}
@-}
{-@
assume
bind_zero_left :: k:(a -> M b) -> EqualProp (M b) {epsilon >>= k} {epsilon}
@-}
{-@
assume
bind_zero_right :: m:M a -> EqualProp (M b) {m >> epsilon} {epsilon}
@-}
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
{-@
assume
refinesplus_reflexivity :: Equality (M a) =>
  m:M a -> RefinesPlus a {m} {m}
@-}
-- !ASSUMED
-- TODO: other lemmas about RefinesPlus
{-@
refinesplus_transitivity ::
  Equality (M a) =>
  m1:M a -> m2:M a -> m3:M a ->
  RefinesPlus a {m1} {m2} ->
  RefinesPlus a {m2} {m3} ->
  RefinesPlus a {m1} {m3}
@-}
{-@
type Morphism a b F = x:M a -> y:M a -> EqualProp (M b) {F x <+> F y} {F (x <+> y)}
@-}
-- {-@
-- refinesplus_substitutability ::
--   (Equality (M a), Equality (M b)) =>
--   f:(M a -> M b) -> x:M a -> y:M a ->
--   Morphism a b {f} ->
--   RefinesPlus (a) {x} {y} ->
--   RefinesPlus (b) {f x} {f y}
-- @-}
-- refinesplus_substitutability :: (Equality (M a), Equality (M b)) => (M a -> M b) -> M a -> M a -> Morphism a b -> EqualityProp (M a) -> EqualityProp (M b)
-- refinesplus_substitutability f x y f_morphism x_refines_y =
--   [eqpropchain|
--       f x <+> f y
--     %==
--       f (x <+> y)
--         %by f_morphism x y
--     %==
--       f y
--         %by %rewrite x <+> y %to y
--         %by x_refines_y
--   |]
{-@ assume
refinesplus_substitutability ::
  (Equality (M a), Equality (M b)) =>
  f:(M a -> M b) -> x:M a -> y:M a ->
  RefinesPlus (a) {x} {y} ->
  RefinesPlus (b) {f x} {f y}
@-}
{-@ reflect morphismF_aux @-}
{-@
type MorphismF a b c F = k1:(a -> M b) -> k2:(a -> M b) ->
  EqualProp (M c) {F k1 <+> F k2} {F (morphismF_aux k1 k2)}
@-}
{-@
assume
refinesplus_substitutabilityF ::
  (Equality (M a), Equality (M b), Equality (M c)) =>
  f:((a -> M b) -> M c) -> k1:(a -> M b) -> k2:(a -> M b) ->
  MorphismF a b c {f} ->
  RefinesPlusF (a) (b) {k1} {k2} ->
  RefinesPlus (c) {f k1} {f k2}
@-}
{-
## Array interface
-}
-- array methods
{-@ reflect read @-}
{-@ reflect write @-}
-- array methods
{-@ reflect readList @-}
{-@ reflect writeList @-}
{-@ reflect writeListToLength @-}
{-@ reflect writeListToLength2 @-}
{-@ reflect writeListToLength3 @-}
{-@ reflect swap @-}
-- array laws
{-@
assume
bind_read_write ::
  i:Natural -> EqualProp (m ())
    {read i >>= write i}
    {pure it}
@-}
{-@
assume
seq_write_read ::
  i:Natural -> x:Int ->
    EqualProp (m Int)
      {write i x >> read i}
      {write i x >> pure x}
@-}
{-@
assume
seq_write_write ::
  i:Natural -> x:Int -> y:Int ->
  EqualProp (m Unit)
    {write i x >> write i y}
    {write i y}
@-}
{-@
assume
seq_read_read ::
  i:Natural -> f:(Int -> Int -> M a) ->
  EqualProp (M Int)
      {seq_read_read_aux1 i f}
      {seq_read_read_aux2 i f}
@-}
{-@ reflect seq_read_read_aux1 @-}
{-@ reflect seq_read_read_aux2 @-}
{-@
assume
read_commutivity ::
  i:Natural -> j:Natural -> k:(Int -> Int -> M a) ->
  EqualProp (M a)
    {bind2 (read i) (read j) k}
    {bind2 (read j) (read i) (flip k)}
@-}
{-@
assume
write_commutativity ::
  i:Natural -> j:{j:Natural | i /= j} -> x:Int -> y:Int ->
  EqualProp (M Unit)
    {write i x >> write j y}
    {write j y >> write i x}
@-}
{-@
assume
read_write_commutivity ::
  i:Natural -> j:{j:Natural | j /= i} -> x:Int -> k:(Int -> M a) ->
  EqualProp (M a)
    {bindFirst (read i) (write j x) k}
    {write j x >> read i >>= k}
@-}
-- array lemmas
{-@
swap_id ::
  (Equality (M ()), Equality (M Unit)) =>
  i:Natural ->
  EqualProp (M Unit)
    {swap i i}
    {pure it}
@-}
-- [ref 9]
{-@
writeList_concat ::
  Equality (M Unit) =>
  i:Natural -> xs:List Int -> ys:List Int ->
  EqualProp (M Unit)
    {writeList i (concat xs ys)}
    {writeList i xs >> writeList (add i (length xs)) ys}
@-}
--
{-@
assume
write_redundancy ::
  Equality (M Unit) =>
  i:Natural -> x:Int ->
  EqualProp (M Unit)
    {write i x >> write i x}
    {write i x}
@-}
-- !ASSUMED
{-@
writeList_redundancy ::
  Equality (M Unit) =>
  i:Natural -> xs:List Int ->
  EqualProp (M Unit)
    {writeList i xs >> writeList i xs}
    {writeList i xs}
@-}
{-@
assume
write_writeList_commutativity ::
  Equality (M Unit) =>
  i:Natural -> x:Int -> xs:List Int ->
  EqualProp (M Unit)
    {write i x >> writeList (S i) xs}
    {writeList (S i) xs >> write i x}
@-}
-- !ASSUMED
{-@
write_writeList_commutativity' ::
  Equality (M Unit) =>
  i:Natural -> x:Int -> xs:List Int -> j:Natural ->
  EqualProp (M Unit)
    {write i x >> writeList (add (S i) j) xs}
    {writeList (add (S i) j) xs >> write i x}
@-}
{-@
writeList_commutativity ::
  Equality (M Unit) =>
  i:Natural -> xs:List Int -> ys:List Int ->
  EqualProp (M Unit)
    {seq (writeList i xs) (writeList (add i (length xs)) ys)}
    {seq (writeList (add i (length xs)) ys) (writeList i xs)}
@-}
-- TODO: explanations
{-@
writeList_read ::
  Equality (M Int) =>
  i:Natural -> x:Int -> xs:List Int ->
  EqualProp (M Int)
    {seq (writeList i (Cons x xs)) (read (add i (length xs)))}
    {seq (writeList i (Cons x xs)) (pure x)}
@-}
{-@
writeList_singleton ::
  Equality (M Unit) =>
  i:Natural -> x:Int ->
  EqualProp (M Unit)
    {writeList i (Cons x Nil)}
    {write i x}
@-}
{-# OPTIONS_GHC "-Wno-missing-signatures" #-}

module Placeholder.M where

import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Prelude hiding (Monad, concat, length, pure, read, readList, seq, (+), (++), (>>), (>>=))

leq :: Int -> Int -> Bool
leq x y = x <= y

geq :: Int -> Int -> Bool
geq x y = y <= x

data M :: * -> * where
  Pure :: a -> M a
  Bind :: M a -> (a -> M b) -> M b
  Epsilon :: M a
  Plus :: M a -> M a -> M a
  Read :: Natural -> M Int
  Write :: Natural -> Int -> M ()

onlyMonadPlus :: M a -> Bool
onlyMonadPlus (Pure _) = True
onlyMonadPlus (Bind m k) = onlyMonadPlus m && onlyMonadPlusF k
onlyMonadPlus Epsilon = True
onlyMonadPlus (Plus _ _) = True
onlyMonadPlus (Read _) = False
onlyMonadPlus (Write _ _) = False

onlyMonadPlusF :: (a -> M b) -> Bool
onlyMonadPlusF k = False

pure :: a -> M a
pure a = Pure a

bind :: M a -> (a -> M b) -> M b
bind m k = Bind m k

infixl 1 >>=

(>>=) :: M a -> (a -> M b) -> M b
m >>= k = Bind m k

seq :: M a -> M b -> M b
seq ma mb = ma >>= constant mb

infixl 1 >>

(>>) :: M a -> M b -> M b
(>>) = seq

kleisli :: (a -> M b) -> (b -> M c) -> (a -> M c)
kleisli k1 k2 x = k1 x >>= k2

infixr 1 >=>

(>=>) :: (a -> M b) -> (b -> M c) -> (a -> M c)
(>=>) = kleisli

kleisli_unfold :: (a -> M b) -> (b -> M c) -> a -> EqualityProp (M c)
kleisli_unfold k1 k2 x = reflexivity (kleisli k1 k2 x)

join :: M (M a) -> M a
join mm = mm >>= identity

liftM :: (a -> b) -> (M a -> M b)
liftM f m = m >>= liftM_aux f

liftM_aux :: (a -> b) -> a -> M b
liftM_aux f x = pure (f x)

liftM2 :: (a -> b -> c) -> (M a -> M b -> M c)
liftM2 f ma mb = ma >>= liftM2_aux f mb

liftM2_aux :: (a -> b -> c) -> M b -> a -> M c
liftM2_aux f mb x = mb >>= liftM2_aux_aux f x

liftM2_aux_aux :: (a -> b -> c) -> a -> b -> M c
liftM2_aux_aux f x y = pure (f x y)

second :: (b -> M c) -> (a, b) -> M (a, c)
second k (x, y) = k y >>= \y' -> pure (x, y')

bind2 :: M a -> M b -> (a -> b -> M c) -> M c
bind2 ma mb k = ma >>= \x -> mb >>= \y -> k x y

bindFirst :: M a -> M b -> (a -> M c) -> M c
bindFirst ma mb k = ma >>= \x -> mb >> k x

pureF :: (a -> b) -> (a -> M b)
pureF f x = pure (f x)

subst_cont :: M a -> (a -> M b) -> (a -> M b) -> (a -> EqualityProp (M b)) -> EqualityProp (M b)
subst_cont m k1 k2 pf = undefined

subst_curr :: M a -> M a -> (a -> M b) -> EqualityProp (M a) -> EqualityProp (M b)
subst_curr m1 m2 k pf = assumedProp

pure_bind :: a -> (a -> M b) -> EqualityProp (M b)
pure_bind _ _ = assumedProp

pure_bind_outfix :: a -> (a -> M b) -> EqualityProp (M b)
pure_bind_outfix _ _ = assumedProp

bind_identity_right :: M a -> EqualityProp (M a)
bind_identity_right _ = assumedProp

bind_associativity :: Equality (M c) => M a -> (a -> M b) -> (b -> M c) -> EqualityProp (M c)
bind_associativity _ _ _ = assumedProp

bind_associativity_nofix :: Equality (M c) => M a -> (a -> M b) -> (b -> M c) -> EqualityProp (M c)
bind_associativity_nofix _ _ _ = assumedProp

seq_associativity ::
  Equality (M c) => M a -> M b -> M c -> EqualityProp (M c)
seq_associativity ma mb mc =
  [eqpropchain|
      (ma >> mb) >> mc 
    %==
      (ma >>= constant mb) >> mc
    %==
      (ma >>= constant mb) >>= constant mc
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

seq_identity_left :: Equality (M b) => a -> M b -> EqualityProp (M b)
seq_identity_left x m =
  [eqpropchain|
      pure x >> m
    %== 
      pure x >>= \_ -> m
    %==
      (\_ -> m) x
        %by pure_bind x (\_ -> m)
    %== 
      m
  |]

bind_if :: Equality (M b) => Bool -> M a -> M a -> (a -> M b) -> EqualityProp (M b)
bind_if True m1 m2 k =
  [eqpropchain|
      (if True then m1 else m2) >>= k
    %==
      m1 >>= k
        %by %rewrite if True then m1 else m2 
                 %to m1
        %by %reflexivity
  |]
bind_if False m1 m2 k =
  [eqpropchain|
      (if False then m1 else m2) >>= k
    %==
      m2 >>= k
        %by %rewrite if False then m1 else m2
                 %to m2
        %by %reflexivity
  |]

seq_bind_associativity :: (Equality (M c), Equality (a -> M c)) => M a -> M b -> (b -> M c) -> EqualityProp (M c)
seq_bind_associativity m1 m2 k =
  [eqpropchain|
      m1 >> m2 >>= k
    %==
      m1 >>= (\_ -> m2) >>= k
        %by %rewrite m1 >> m2
                %to m1 >>= \_ -> m2
        %by %reflexivity
    %==
      m1 >>= ((\_ -> m2) >=> k)
        %by bind_associativity m1 (\_ -> m2) k
    %==
      m1 >>= \x -> ((\_ -> m2) >=> k) x
        %by %rewrite (\_ -> m2) >=> k
                %to \x -> ((\_ -> m2) >=> k) x
        %by %symmetry
        %by %reflexivity
    %==
      m1 >>= \x -> (\_ -> m2) x >>= k
        %by %rewrite \x -> ((\_ -> m2) >=> k) x
                %to \x -> (\_ -> m2) x >>= k
        %by %extend x
        %by %reflexivity
    %==
      m1 >>= \x -> m2 >>= k
        %by %rewrite \x -> (\_ -> m2) x >>= k
                 %to \x -> m2 >>= k
        %by %extend x
        %by %symmetry
        %by %reflexivity
    %==
      m1 >> (m2 >>= k)
        %by %symmetry
        %by %reflexivity
  |]

bind_associativity4 :: Equality (M d) => M a -> (a -> M b) -> (b -> M c) -> (c -> M d) -> EqualityProp (M d)
bind_associativity4 m k1 k2 k3 =
  [eqpropchain|
      m >>= k1 >>= k2 >>= k3
    %==
      m >>= k1 >>= (k2 >=> k3)
    %==
      m >>= k1 >>= (k2 >=> k3)
        %by bind_associativity (m >>= k1) k2 k3
    %==
      m >>= (k1 >=> (k2 >=> k3))
        %by bind_associativity m k1 (k2 >=> k3)
  |]

seq_associativity4 :: Equality (M d) => M a -> M b -> M c -> M d -> EqualityProp (M d)
seq_associativity4 ma mb mc md =
  [eqpropchain|
      ma >> mb >> mc >> md
    %==
      ma >> mb >> (mc >> md)
        %by seq_associativity (ma >> mb) mc md
    %==
      ma >> (mb >> (mc >> md))
        %by seq_associativity ma mb (mc >> md)
  |]

seq_pure_bind :: (Equality (M c), Equality (a -> M c)) => M a -> b -> (b -> M c) -> EqualityProp (M c)
seq_pure_bind m x k =
  [eqpropchain|
      m >> pure x >>= k 
    %==
      m >>= (\_ -> pure x) >>= k
        %by %rewrite m >> pure x
                 %to m >>= (\_ -> pure x)
        %by %reflexivity
    %==
      m >>= ((\_ -> pure x) >=> k)
        %by bind_associativity m (\_ -> pure x) k
    %==
      m >>= \y -> ((\_ -> pure x) >=> k) y
        %by %rewrite ((\_ -> pure x) >=> k)
                 %to \y -> ((\_ -> pure x) >=> k) y
        %by %symmetry
        %by %reflexivity
    %==
      m >>= \y -> (\_ -> pure x) y >>= k
        %by %rewrite \y -> ((\_ -> pure x) >=> k) y
                 %to \y -> (\_ -> pure x) y >>= k
        %by %extend y
        %by %reflexivity
    %==
      m >>= \y -> pure x >>= k
        %by %rewrite \y -> (\_ -> pure x) y >>= k
                 %to \y -> pure x >>= k
        %by %extend y
        %by %rewrite (\_ -> pure x) y
                 %to pure x
        %by %reflexivity
    %==
      m >> (pure x >>= k)
        %by %symmetry
        %by %reflexivity
  
  |]

seq_if_bind :: (Equality (M c), Equality (a -> M c)) => M a -> Bool -> M b -> M b -> (b -> M c) -> EqualityProp (M c)
seq_if_bind m True m1 m2 k =
  [eqpropchain|
      m >> (if True then m1 else m2) >>= k
    %==
      m >> m1 >>= k
        %by %rewrite if True then m1 else m2
                 %to m1
        %by %reflexivity
    %==
      m >> (m1 >>= k)
        %by seq_bind_associativity m m1 k
    %==
      m >> if True then m1 >>= k else m2 >>= k
        %by %rewrite m1 >>= k
                 %to if True then m1 >>= k else m2 >>= k
        %by %symmetry
        %by %reflexivity
  |]
seq_if_bind m b m1 m2 k =
  [eqpropchain|
      m >> (if True then m1 else m2) >>= k
    %==
      m >> m2 >>= k
        %by %rewrite if False then m1 else m2
                 %to m2
        %by %reflexivity
    %==
      m >> (m2 >>= k)
        %by seq_bind_associativity m m2 k
    %==
      m >> if False then m1 >>= k else m2 >>= k
        %by %rewrite m1 >>= k
                 %to if False then m1 >>= k else m2 >>= k
        %by %symmetry
        %by %reflexivity
  |]

pure_kleisli :: Equality (M c) => (a -> b) -> (b -> M c) -> a -> EqualityProp (M c)
pure_kleisli f k x =
  [eqpropchain|
      kleisli (compose pure f) k x
    %==
      (compose pure f) x >>= k
        %by %reflexivity
    %==
      pure (f x) >>= k
        %by %rewrite (compose pure f) x
                 %to pure (f x)
        %by %reflexivity
    %==
      k (f x)
        %by pure_bind (f x) k
    %==
      compose k f x
        %by %symmetry
        %by %reflexivity
  |]

seq_bind_seq_associativity :: (Equality (a -> M c), Equality (M d), Equality (M c)) => M a -> M b -> (b -> M c) -> M d -> EqualityProp (M d)
seq_bind_seq_associativity m1 m2 k m3 =
  [eqpropchain|
      m1 >> m2 >>= k >> m3
    %==
      m1 >> (m2 >>= k) >> m3
        %by %rewrite m1 >> m2 >>= k 
                 %to m1 >> (m2 >>= k)
        %by seq_bind_associativity m1 m2 k 
    %==
      m1 >> (m2 >>= k >> m3)
        %by seq_associativity m1 (m2 >>= k) m3
  |]

kseq :: (a -> M b) -> M c -> (a -> M c)
kseq k m x = k x >> m

seqk :: M a -> (b -> M c) -> (b -> M c)
seqk m k x = m >> k x

bind_seq_associativity :: (Equality (M c), Equality (a -> M c)) => M a -> (a -> M b) -> M c -> EqualityProp (M c)
bind_seq_associativity m1 k m2 =
  [eqpropchain|
      m1 >>= k >> m2 
    %==
      m1 >>= k >>= \_ -> m2
    %==
      m1 >>= (k >=> (\_ -> m2))
        %by bind_associativity m1 k (\_ -> m2)
    %==
      m1 >>= \x -> (k >=> (\_ -> m2)) x 
        %by %rewrite (k >=> (\_ -> m2))
                 %to \x -> (k >=> (\_ -> m2)) x 
        %by %symmetry
        %by %reflexivity
    %==
      m1 >>= \x -> (k x >>= (\_ -> m2))
        %by %rewrite \x -> (k >=> (\_ -> m2)) x 
                 %to \x -> (k x >>= (\_ -> m2))
        %by %extend x
        %by %reflexivity
    %==
      m1 >>= \x -> (k x >> m2)
        %by %rewrite \x -> (k x >>= (\_ -> m2))
                 %to \x -> (k x >> m2)
        %by %extend x 
        %by %symmetry
        %by %reflexivity
    %==
      m1 >>= kseq k m2
        %by %rewrite \x -> (k x >> m2)
                 %to kseq k m2
        %by %extend x 
        %by %symmetry
        %by %reflexivity
  |]

seq_pure_unit :: M Unit -> EqualityProp (M Unit)
seq_pure_unit m = assumedProp

kleisli_associativity :: Equality (M d) => (a -> M b) -> (b -> M c) -> (c -> M d) -> a -> EqualityProp (M d)
kleisli_associativity k1 k2 k3 x =
  [eqpropchain|
        kleisli k1 (kleisli k2 k3) x
    %==
        kleisli (kleisli k1 k2) k3 x
    |]

epsilon :: M a
epsilon = Epsilon

plus :: M a -> M a -> M a
plus = Plus

infixl 3 <+>

(<+>) :: M a -> M a -> M a
(<+>) = plus

plusF :: (a -> M b) -> (a -> M b) -> (a -> M b)
plusF k1 k2 x = k1 x <+> k2 x

guard :: Bool -> M ()
guard b = if b then pure () else epsilon

guardBy :: (a -> Bool) -> a -> M a
guardBy p x = guard (p x) >> pure x

plus_identity_left :: M a -> EqualityProp (M a)
plus_identity_left _ = assumedProp

plus_associativity :: (Equality (M a)) => M a -> M a -> M a -> EqualityProp (M a)
plus_associativity _ _ _ = assumedProp

plus_idempotency :: M a -> EqualityProp (M a)
plus_idempotency _ = assumedProp

plus_commutativity :: M a -> M a -> EqualityProp (M a)
plus_commutativity _ _ = assumedProp

plus_distributivity_left :: M a -> M a -> (a -> M b) -> EqualityProp (M b)
plus_distributivity_left _ _ _ = assumedProp

plus_distributivity_right_aux :: (a -> M b) -> (a -> M b) -> a -> M b
plus_distributivity_right_aux k1 k2 x = k1 x <+> k2 x

plus_distributivity_right :: M a -> (a -> M b) -> (a -> M b) -> EqualityProp (M b)
plus_distributivity_right _ _ _ = assumedProp

bind_zero_left :: (a -> M b) -> EqualityProp (M b)
bind_zero_left _ = assumedProp

bind_zero_right :: M a -> EqualityProp (M b)
bind_zero_right _ = assumedProp

refinesplus_equalprop :: Equality (M a) => M a -> M a -> EqualityProp (M a) -> EqualityProp (M a)
refinesplus_equalprop m1 m2 hyp =
  [eqpropchain|
      m1 <+> m2
    %==
      m2 <+> m2
        %by %rewrite m1 %to m2 %by hyp
    %==
      m2
        %by plus_idempotency m2
  |]

refinesplus_reflexivity :: Equality (M a) => M a -> EqualityProp (M a)
refinesplus_reflexivity m = assumedProp

refinesplus_transitivity :: Equality (M a) => M a -> M a -> M a -> EqualityProp (M a) -> EqualityProp (M a) -> EqualityProp (M a)
refinesplus_transitivity m1 m2 m3 h12 h23 =
  [eqpropchain|
      m1 <+> m3
    %==
      m1 <+> (m2 <+> m3)
    %==
      m1 <+> m2 <+> m3
        %by plus_associativity m1 m2 m3
    %==
      m2 <+> m3
        %by %rewrite m1 <+> m2 
                 %to m2
        %by h12
    %==
      m3 
        %by h23
  |]

type Morphism a b = M a -> M a -> EqualityProp (M b)

-- * uses morphism restriction

refinesplus_substitutability :: (Equality (M a), Equality (M b)) => (M a -> M b) -> M a -> M a -> EqualityProp (M a) -> EqualityProp (M b)
refinesplus_substitutability f x y x_refines_y = assumedProp

morphismF_aux :: (a -> M b) -> (a -> M b) -> (a -> M b)
morphismF_aux k1 k2 x = k1 x <+> k2 x

type MorphismF a b c = (a -> M b) -> (a -> M b) -> EqualityProp (M c)

refinesplus_substitutabilityF ::
  (Equality (M a), Equality (M b), Equality (M c)) =>
  ((a -> M b) -> M c) ->
  (a -> M b) ->
  (a -> M b) ->
  MorphismF a b c ->
  (a -> EqualityProp (M b)) ->
  EqualityProp (M c)
refinesplus_substitutabilityF f k1 k2 f_morphismF k1_refines_k2 =
  [eqpropchain|
      f k1 <+> f k2
    %==
      f (morphismF_aux k1 k2)
        %by f_morphismF k1 k2
    %==
      f (\x -> k1 x <+> k2 x)
        %by %rewrite morphismF_aux k1 k2 
                 %to \x -> k1 x <+> k2 x
        %by %extend x
        %by %reflexivity
    %==
      f (\x -> k2 x)
        %by %rewrite \x -> k1 x <+> k2 x
                 %to \x -> k2 x
        %by %extend x
        %by k1_refines_k2 x
    %==
      f k2
        %by %rewrite \x -> k2 x
                 %to k2
        %by %extend x 
        %by %reflexivity
  |]

read :: Natural -> M Int
read = Read

write :: Natural -> Int -> M ()
write = Write

readList :: Natural -> Natural -> M (List Int)
readList i Z = pure Nil
readList i (S n) = liftM2 Cons (read i) (readList (S i) n)

writeList :: Natural -> List Int -> M ()
writeList i Nil = pure it
writeList i (Cons x xs) = write i x >> writeList (S i) xs

writeListToLength :: Natural -> List Int -> M Natural
writeListToLength i xs = writeList i xs >> pure (length xs)

writeListToLength2 :: Natural -> (List Int, List Int) -> M (Natural, Natural)
writeListToLength2 i (xs, ys) = seq (writeList i (concat xs ys)) (pure (length xs, length ys))

writeListToLength3 :: Natural -> (List Int, List Int, List Int) -> M (Natural, Natural, Natural)
writeListToLength3 i (xs, ys, zs) = writeList i (xs ++ ys ++ zs) >> pure (length xs, length ys, length zs)

swap :: Natural -> Natural -> M ()
swap i j = read i >>= \x -> read j >>= \y -> write i y >> write j x

bind_read_write :: Natural -> EqualityProp (m ())
bind_read_write _ = assumedProp

seq_write_read :: Natural -> Int -> EqualityProp (m Int)
seq_write_read _ _ = assumedProp

seq_write_write :: Natural -> Int -> Int -> EqualityProp (m Unit)
seq_write_write _ _ _ = assumedProp

seq_read_read :: Natural -> (Int -> Int -> M a) -> EqualityProp (M Int)
seq_read_read _ _ = assumedProp

seq_read_read_aux1 :: Natural -> (Int -> Int -> M a) -> M a
seq_read_read_aux1 i f = read i >>= \x -> read i >>= \x' -> f x x'

seq_read_read_aux2 :: Natural -> (Int -> Int -> M a) -> M a
seq_read_read_aux2 i f = read i >>= \x -> read i >>= \_ -> f x x

read_commutivity :: Natural -> Natural -> (Int -> Int -> M a) -> EqualityProp (M a)
read_commutivity _ _ _ = assumedProp

write_commutativity :: Natural -> Natural -> Int -> Int -> EqualityProp (M ())
write_commutativity _ _ _ _ = assumedProp

read_write_commutivity :: Natural -> Natural -> Int -> (Int -> M a) -> EqualityProp (M a)
read_write_commutivity _ _ _ _ = assumedProp

swap_id :: (Equality (M ()), Equality (M Unit)) => Natural -> EqualityProp (M ())
swap_id i =
  [eqpropchain|
        swap i i
    %==
        read i >>= \x -> read i >>= \y -> write i y >> write i x
    %==
        read i >>= \x -> read i >>= \y -> (\x y -> write i y >> write i x) x y
    %==
        read i >>= \x -> read i >>= \y -> (\x y -> write i y >> write i x) x x
            %-- seq_read_read i (\x y -> write i y >> write i x)
    %==
        read i >>= \x -> read i >>= \y -> (\x y -> write i x) x x
    %==
        read i >>= \x -> read i >>= \y -> write i x
    %==
        read i >>= \x -> write i x
    %==
        pure it
            %by bind_read_write i
    |]

writeList_concat :: Equality (M Unit) => Natural -> List Int -> List Int -> EqualityProp (M ())
writeList_concat i Nil ys =
  [eqpropchain|
      writeList i (Nil ++ ys)
    %==
      writeList i ys
        %by %rewrite Nil ++ ys %to ys
        %by %smt
        %by concat_identity ys
    %==
      apply (\_ -> writeList i ys) it
        %by %smt
        %by etaEquivalency it (writeList i ys)
          ? apply (\_ -> writeList i ys) it
    %==
      pure it >>= apply (\_ -> writeList i ys)
        %by %symmetry
        %by pure_bind it (apply (\_ -> writeList i ys))
    %==
      pure it >> writeList i ys
        %by %smt
        %by pure it >>= apply (\_ -> writeList i ys)
    %==
      writeList i Nil >> writeList i ys
        %by %smt
        %by pure it >> writeList i ys
    %==
      writeList i Nil >> writeList (i + Z) ys
        %by %smt
        %by add_identity i
    %==
      writeList i Nil >> writeList (i + length Nil) ys
        %by %smt
        %by writeList i Nil >> writeList (i + Z) ys
  |]
writeList_concat i (Cons x xs) ys =
  [eqpropchain|
      writeList i (Cons x xs ++ ys)
    %==
      writeList i (Cons x (xs ++ ys))
        %by %rewrite Cons x xs ++ ys
                 %to Cons x (xs ++ ys)
        %by %smt
        %by Cons x (xs ++ ys)
    %==
      write i x >> writeList (S i) (xs ++ ys)
        %by %smt
        %by writeList i (Cons x (xs ++ ys))
    %==
      write i x >> (writeList (S i) xs >> writeList (S i + length xs) ys)
        %by %rewrite writeList (S i) (xs ++ ys)
                 %to writeList (S i) xs >> writeList (S i + length xs) ys
        %by writeList_concat (S i) xs ys
    %==
      write i x >> (writeList (S i) xs >> writeList (S (i + length xs)) ys)
        %by %rewrite S i + length xs
                 %to S (i + length xs)
        %by %smt
        %by S i + length xs
          ? S (i + length xs)
    %==
      (write i x >> writeList (S i) xs) >> writeList (S (i + length xs)) ys
        %by %symmetry
        %by seq_associativity
              (write i x)
              (writeList (S i) xs)
              (writeList (S (i + length xs)) ys)
    %==
      (write i x >> writeList (S i) xs) >> writeList (i + S (length xs)) ys
        %by %rewrite S (i + length xs)
                 %to i + S (length xs)
        %by %smt
        %by i + S (length xs)
          ? add_S_right i (length xs)
    %==
      (write i x >> writeList (S i) xs) >> writeList (i + length (Cons x xs)) ys
        %by %rewrite S (length xs)
                 %to length (Cons x xs)
        %by %smt
        %by S (length xs)
          ? length (Cons x xs)
    %==
      writeList i (Cons x xs) >> writeList (i + length (Cons x xs)) ys
        %by %rewrite write i x >> writeList (S i) xs
                 %to writeList i (Cons x xs)
        %by %smt
        %by write i x >> writeList (S i) xs
          ? writeList i (Cons x xs)
  |]

write_redundancy :: Equality (M Unit) => Natural -> Int -> EqualityProp (M Unit)
write_redundancy i x = assumedProp

writeList_redundancy :: Equality (M Unit) => Natural -> List Int -> EqualityProp (M ())
writeList_redundancy i Nil =
  [eqpropchain|
      writeList i Nil >> writeList i Nil
    %==
      pure it >> pure it
    %==
      pure it 
        %by seq_identity_left it (pure it)
    %==
      writeList i Nil
        %by %symmetry
        %by %reflexivity
  |]
writeList_redundancy i (Cons x xs) =
  [eqpropchain|
      writeList i (Cons x xs) >> writeList i (Cons x xs)
    %==
      write i x >> writeList (S i) xs >> (write i x >> writeList (S i) xs)
    %==
      write i x >> writeList (S i) xs >> (writeList (S i) xs >> write i x)
        %-- TODO
    %==
      write i x >> (writeList (S i) xs >> (writeList (S i) xs >> write i x))
        %by seq_associativity (write i x) (writeList (S i) xs) (writeList (S i) xs >> write i x)
    %==
      write i x >> (writeList (S i) xs >> writeList (S i) xs >> write i x)
        %by %rewrite (writeList (S i) xs >> (writeList (S i) xs >> write i x))
                 %to (writeList (S i) xs >> writeList (S i) xs >> write i x)
        %by %symmetry
        %by seq_associativity (writeList (S i) xs) (writeList (S i) xs) (write i x)
    %==
      write i x >> (writeList (S i) xs >> write i x)
        %by %rewrite writeList (S i) xs >> writeList (S i) xs >> write i x
                 %to writeList (S i) xs >> write i x
        %by writeList_redundancy (S i) xs
    %==
      write i x >> (write i x >> writeList (S i) xs)
        %-- TODO
    %== 
      write i x >> write i x >> writeList (S i) xs
        %by seq_associativity (write i x) (write i x) (writeList (S i) xs)
    %==
      write i x >> writeList (S i) xs
        %by %rewrite write i x >> write i x
                 %to write i x
        %by write_redundancy i x
    %==
      writeList i (Cons x xs)
        %-- TODO
  |]

write_writeList_commutativity :: Equality (M Unit) => Natural -> Int -> List Int -> EqualityProp (M Unit)
write_writeList_commutativity i x xs = assumedProp

write_writeList_commutativity' :: Equality (M Unit) => Natural -> Int -> List Int -> Natural -> EqualityProp (M Unit)
write_writeList_commutativity' i x xs Z =
  [eqpropchain|
      write i x >> writeList (add (S i) Z) xs

    %==
      write i x >> writeList (S i) xs

        %by %rewrite add (S i) Z
                 %to S i
        %by %smt
        %by add_identity (S i)

    %==
      writeList (S i) xs >> write i x

        %by write_writeList_commutativity i x xs

    %==
      writeList (add (S i) Z) xs >> write i x

        %by %rewrite S i 
                 %to add (S i) Z
        %by %smt
        %by add_identity (S i)
  |]
write_writeList_commutativity' i x Nil (S j) =
  [eqpropchain|
      write i x >> writeList (add (S i) (S j)) Nil

    %==
      write i x >> pure it
        %by %rewrite writeList (add (S i) (S j)) Nil
                 %to pure it 
        %by %reflexivity

    %==
      write i x
        %by %symmetry
        %by seq_pure_unit (write i x)

    %==
      pure it >> write i x
        %by %symmetry
        %by seq_identity_left it (write i x)

    %==
      writeList (add (S i) (S j)) Nil >> write i x
        %by %rewrite pure it 
                 %to writeList (add (S i) (S j)) Nil
        %by %symmetry
        %by %reflexivity
  |]
write_writeList_commutativity' i x (Cons y ys) (S j) =
  [eqpropchain|
      write i x >> writeList (add (S i) (S j)) (Cons y ys)

    %==
      write i x >> (write (add (S i) (S j)) y >> writeList (S (add (S i) (S j))) ys)
  
    %==
      write i x >> write (add (S i) (S j)) y >> writeList (S (add (S i) (S j))) ys
        %by %symmetry
        %by seq_associativity
              (write i x)
              (write (add (S i) (S j)) y)
              (writeList (S (add (S i) (S j))) ys)
    %==
      write (add (S i) (S j)) y >> write i x >> writeList (S (add (S i) (S j))) ys
        %by %rewrite write i x >> write (add (S i) (S j)) y
                 %to write (add (S i) (S j)) y >> write i x
        %by write_commutativity i (add (S i) (S j)) x y
          ? m_neq_S_add_Sm_Sn i j
    
    %==
      write (add (S i) (S j)) y >> write i x >> writeList (add (S i) (S (S j))) ys
        %by %rewrite (S (add (S i) (S j)))
                 %to (add (S i) (S (S j)))
        %by %reflexivity

    %==
      write (add (S i) (S j)) y >> (write i x >> writeList (add (S i) (S (S j))) ys)
        %by seq_associativity
              (write (add (S i) (S j)) y)
              (write i x)
              (writeList (add (S i) (S (S j))) ys)
    
    %==
      write (add (S i) (S j)) y >> (writeList (add (S i) (S (S j))) ys >> write i x)
        %by %rewrite write i x >> writeList (add (S i) (S (S j))) ys
                 %to writeList (add (S i) (S (S j))) ys >> write i x
        %by write_writeList_commutativity' i x ys (S (S j))
    
    %==
      write (add (S i) (S j)) y >> writeList (add (S i) (S (S j))) ys >> write i x
        %by %symmetry
        %by seq_associativity
              (write (add (S i) (S j)) y)
              (writeList (add (S i) (S (S j))) ys)
              (write i x)
    
    %==
      write (add (S i) (S j)) y >> writeList (add (S i) (S (S j))) ys >> write i x
        
    %==
      writeList (add (S i) (S j)) (Cons y ys) >> write i x 
        %by %rewrite write (add (S i) (S j)) y >> writeList (add (S i) (S (S j))) ys
                 %to writeList (add (S i) (S j)) (Cons y ys)
        %by %symmetry
        %by %reflexivity
  |]

writeList_commutativity :: Equality (M ()) => Natural -> List Int -> List Int -> EqualityProp (M ())
writeList_commutativity i Nil ys =
  [eqpropchain|
      writeList i Nil >> writeList (i + length Nil) ys

    %==
      pure it >> writeList (i + length Nil) ys
        %by %rewrite writeList i Nil 
                 %to pure it
        %by %reflexivity
    
    %==
      writeList (i + length Nil) ys
        %by seq_identity_left it (writeList (i + length Nil) ys)

    %==
      writeList (i + length Nil) ys >> pure it
        %by seq_pure_unit (writeList (i + length Nil) ys)

    %==
      writeList (i + length Nil) ys >> writeList i Nil
        %by %rewrite pure it 
                 %to writeList i Nil
        %by %symmetry
        %by %reflexivity
  |]
writeList_commutativity i (Cons x xs) ys =
  [eqpropchain|
      writeList i (Cons x xs) >> writeList (i + length (Cons x xs)) ys

    %==
      writeList i (Cons x xs) >> writeList (S (i + length xs)) ys
        %-- rewrite (i + length (Cons x xs))

    %==
      write i x >> writeList (S i) xs >> writeList (S (i + length xs)) ys
        %-- defn writeList

    %==
      write i x >> writeList (S (i + length xs)) ys >> writeList (S i) xs
        %-- by IH

    %==
      write i x >> writeList (S i + length xs) ys >> writeList (S i) xs
        %-- rewrite (S (i + length xs))

    %==
      writeList (S i + length xs) ys >> write i x >> writeList (S i) xs
        %-- by write_writeList_commutativity'

    %==
      writeList (S i + length xs) ys >> writeList i (Cons x xs)
        %-- defn writeList

    %==
      writeList (S (i + length xs)) ys >> writeList i (Cons x xs)
        %-- rewrite (S i + length xs)

    %==
      writeList (i + length (Cons x xs)) ys >> writeList i (Cons x xs)
        %-- defn writeList
  |]

writeList_read :: Equality (M Int) => Natural -> Int -> List Int -> EqualityProp (M Int)
writeList_read i x xs =
  [eqpropchain|
      seq (writeList i (Cons x xs)) (read (add i (length xs)))
    %==
      seq (writeList i (Cons x xs)) (pure x)
  |]

writeList_singleton :: Equality (M Unit) => Natural -> Int -> EqualityProp (M ())
writeList_singleton i x =
  [eqpropchain|
      writeList i (Cons x Nil)
    %==
      write i x
  |]

-- {-@
-- permute_commutativitiy_v1 ::
--   m:M () -> xs:List Int -> k:(List Int -> M a) ->
--   EqualProp (M a)
--     {bind (seq m (permute xs)) k}
--     {bind (permute xs) (\xs':List a -> seq m (k xs'))}
-- @-}
-- permute_commutativitiy_v1 :: M () -> List Int -> (List Int -> M a) -> EqualityProp (M a)
permute_commutativitiy_v1 m xs k = undefined

-- {-@
-- distribute_if ::
--   c:Bool -> m1:M a -> m2:M a -> k:(a -> M b)
--   EqualProp (M b)
--     {bind (if c then m1 else m2) k}
--     {if c then bind m1 k else bind m2 k}
-- @-}
-- distribute_if :: Bool -> M a -> M a -> (a -> M b) -> EqualityProp (M b)
distribute_if c m1 m2 k = undefined

-- {-@
-- permute_preserves_length ::
--   xs:List Int ->
--   EqualProp (M Natural)
--     {bind (permute xs) (pureF length)}
--     {pure (length xs)}
-- @-}
-- permute_preserves_length :: List Int -> EqualityProp (M Natural)
permute_preserves_length xs = undefined

-- {-@ assume
-- subst_curr' ::
--   m1:M a -> m2:M a -> k:(a -> M b) ->
--   (EqualProp (M a) {m1} {m2}) ->
--   EqualProp (M b) {m1 >>= k} {m2 >>= k}
-- @-}
-- subst_curr' :: M a -> M a -> (a -> M b) -> EqualityProp (M a) -> EqualityProp (M b)
subst_curr' = undefined

-- {-@
-- bind_associativity' ::
--   Equality (M c) =>
--   m:M a -> k1:(a -> M b) -> k2:(b -> M c) ->
--   EqualProp (M c)
--     {m >>= k1 >>= k2}
--     {m >>= (k1 >=> k2)}
-- @-}
-- bind_associativity' :: Equality (M c) => M a -> (a -> M b) -> (b -> M c) -> EqualityProp (M c)
bind_associativity' m k1 k2 = undefined

writeListToLength2_helper = undefined
