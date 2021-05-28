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
-- interpretM _ pls _m = undefined

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
pure_bind :: x:a -> k:(a -> M b) -> EqualProp (M b) {pure x >>= k} {k x}
@-}
pure_bind :: a -> (a -> M b) -> EqualityProp (M b)
pure_bind _ _ = assumedProp

{-@
assume
pure_bind_outfix :: x:a -> k:(a -> M b) -> EqualProp (M b) {bind (pure x) k} {k x}
@-}
pure_bind_outfix :: a -> (a -> M b) -> EqualityProp (M b)
pure_bind_outfix _ _ = assumedProp

{-@
assume
bind_identity_right :: m:M a -> EqualProp (M a) {m >>= pure} {m}
@-}
bind_identity_right :: M a -> EqualityProp (M a)
bind_identity_right _ = assumedProp

{-@
assume
bind_associativity ::
  Equality (M c) =>
  m:M a -> k1:(a -> M b) -> k2:(b -> M c) ->
  EqualProp (M c)
    {m >>= k1 >>= k2}
    {m >>= (k1 >=> k2)}
@-}
bind_associativity :: Equality (M c) => M a -> (a -> M b) -> (b -> M c) -> EqualityProp (M c)
bind_associativity _ _ _ = assumedProp

{-@
assume
bind_associativity_nofix ::
  Equality (M c) =>
  m:M a -> k1:(a -> M b) -> k2:(b -> M c) ->
  EqualProp (M c)
    {m >>= k1 >>= k2}
    {m >>= kleisli k1 k2}
@-}
bind_associativity_nofix :: Equality (M c) => M a -> (a -> M b) -> (b -> M c) -> EqualityProp (M c)
bind_associativity_nofix _ _ _ = assumedProp

-- monad lemmas

{-@
seq_associativity ::
  Equality (M c) => ma:M a -> mb:M b -> mc:M c ->
  EqualProp (M c)
    {(ma >> mb) >> mc}
    {ma >> mb >> mc}
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
        %by undefined %-- !LH reject: SMT crash: invalid qualiied identifier, sort mismatch
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
        %by pure_bind x (\_ -> m)
    %== 
      m
  |]

-- implied by apply_if
{-@
bind_if ::
  Equality (M b) =>
  b:Bool -> m1:M a -> m2:M a -> k:(a -> M b) ->
  EqualProp (M b)
    {(if b then m1 else m2) >>= k}
    {if b then m1 >>= k else m2 >>= k}
@-}
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

{-@
seq_bind_associativity ::
  (Equality (M c), Equality (a -> M c)) =>
  m1:M a -> m2:M b -> k:(b -> M c) ->
  EqualProp (M c)
    {m1 >> m2 >>= k}
    {m1 >> (m2 >>= k)}
@-}
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

{-@
bind_associativity4 ::
  Equality (M d) =>
  m:M a -> k1:(a -> M b) -> k2:(b -> M c) -> k3:(c -> M d) ->
  EqualProp (M d)
    {m >>= k1 >>= k2 >>= k3}
    {m >>= (k1 >=> (k2 >=> k3))}
@-}
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

{-@
seq_associativity4 ::
  Equality (M d) =>
  ma:M a -> mb:M b -> mc:M c -> md:M d ->
  EqualProp (M d)
    {ma >> mb >> mc >> md}
    {ma >> (mb >> (mc >> md))}
@-}
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

{-@
seq_pure_bind ::
  (Equality (M c), Equality (a -> M c)) =>
  m:M a -> x:b -> k:(b -> M c) ->
  EqualProp (M c)
    {m >> pure x >>= k}
    {m >> (pure x >>= k)}
@-}
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

{-@
seq_if_bind ::
  (Equality (M c), Equality (a -> M c)) =>
  m:M a -> b:Bool -> m1:M b -> m2:M b -> k:(b -> M c) ->
  EqualProp (M c)
    {m >> (if b then m1 else m2) >>= k}
    {m >> if b then m1 >>= k else m2 >>= k}
@-}
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

{-@
pure_kleisli ::
  Equality (M c) =>
  f:(a -> b) -> k:(b -> M c) -> x:a ->
  EqualProp (M c)
    {kleisli (compose pure f) k x}
    {compose k f x}
@-}
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

{-@
seq_bind_seq_associativity ::
  (Equality (a -> M c), Equality (M d), Equality (M c)) =>
  m1:M a -> m2:M b -> k:(b -> M c) -> m3:M d ->
  EqualProp (M d)
    {m1 >> m2 >>= k >> m3}
    {m1 >> (m2 >>= k >> m3)}
@-}
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

{-@ reflect kseq @-}
kseq :: (a -> M b) -> M c -> (a -> M c)
kseq k m x = k x >> m

{-@ reflect seqk @-}
seqk :: M a -> (b -> M c) -> (b -> M c)
seqk m k x = m >> k x

{-@
bind_seq_associativity ::
  (Equality (M c), Equality (a -> M c)) =>
  m1:M a -> k:(a -> M b) -> m2:M c ->
  EqualProp (M c)
    {m1 >>= k >> m2}
    {m1 >>= kseq k m2}
@-}
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
plus_associativity ::
  (Equality (M a)) =>
  m1:M a -> m2:M a -> m3:M a ->
  EqualProp (M a)
    {m1 <+> m2 <+> m3}
    {m1 <+> (m2 <+> m3)}
@-}
plus_associativity :: (Equality (M a)) => M a -> M a -> M a -> EqualityProp (M a)
plus_associativity _ _ _ = assumedProp

{-@
assume
plus_idempotency :: m:M a -> EqualProp (M a) {m <+> m} {m}
@-}
plus_idempotency :: M a -> EqualityProp (M a)
plus_idempotency _ = assumedProp

{-@
assume
plus_commutativity :: m1:M a -> m2:M a -> EqualProp (M a) {m1 <+> m2} {m2 <+> m1}
@-}
plus_commutativity :: M a -> M a -> EqualityProp (M a)
plus_commutativity _ _ = assumedProp

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
assume
refinesplus_reflexivity :: Equality (M a) =>
  m:M a -> RefinesPlus a {m} {m}
@-}
refinesplus_reflexivity :: Equality (M a) => M a -> EqualityProp (M a)
refinesplus_reflexivity m = assumedProp -- !ASSUMED

-- TODO: other lemmas about RefinesPlus

{-@
refinesplus_transitivity ::
  Equality (M a) =>
  m1:M a -> m2:M a -> m3:M a ->
  RefinesPlus a {m1} {m2} ->
  RefinesPlus a {m2} {m3} ->
  RefinesPlus a {m1} {m3}
@-}
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

-- TODO: does this need to be assumed? i have no idea how you would prove it...
{-@
assume
refinesplus_substitutability ::
  (Equality (M a), Equality (M b)) =>
  f:(M a -> M b) -> x:M a -> y:M a ->
  RefinesPlus (a) {x} {y} ->
  RefinesPlus (b) {f x} {f y}
@-}
refinesplus_substitutability :: (Equality (M a), Equality (M b)) => (M a -> M b) -> M a -> M a -> EqualityProp (M a) -> EqualityProp (M b)
refinesplus_substitutability f x y h = assumedProp -- !ASSUMED

-- TODO: same for this one as with `refinesplus_substitutability`...
{-@
assume
refinesplus_substitutabilityF ::
  (Equality (M a), Equality (M b)) =>
  f:((c -> M a) -> M b) -> k1:(c -> M a) -> k2:(c -> M a) ->
  RefinesPlusF (c) (a) {k1} {k2} ->
  RefinesPlus (b) {f k1} {f k2}
@-}
refinesplus_substitutabilityF :: (Equality (M a), Equality (M b)) => ((c -> M a) -> M b) -> (c -> M a) -> (c -> M a) -> (c -> EqualityProp (M a)) -> EqualityProp (M b)
refinesplus_substitutabilityF f k1 k2 h = undefined -- !ASSUMED

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
bind_read_write ::
  i:Natural -> EqualProp (m ())
    {read i >>= write i}
    {pure it}
@-}
bind_read_write :: Natural -> EqualityProp (m ())
bind_read_write _ = assumedProp

{-@
assume
seq_write_read ::
  i:Natural -> x:Int ->
    EqualProp (m Int)
      {write i x >> read i}
      {write i x >> pure x}
@-}
seq_write_read :: Natural -> Int -> EqualityProp (m Int)
seq_write_read _ _ = assumedProp

{-@
assume
seq_write_write ::
  i:Natural -> x:Int -> y:Int ->
  EqualProp (m Unit)
    {write i x >> write i y}
    {write i y}
@-}
seq_write_write :: Natural -> Int -> Int -> EqualityProp (m Unit)
seq_write_write _ _ _ = assumedProp

{-@
assume
seq_read_read ::
  i:Natural -> f:(Int -> Int -> M a) ->
  EqualProp (M Int)
      {seq_read_read_aux1 i f}
      {seq_read_read_aux2 i f}
@-}
seq_read_read :: Natural -> (Int -> Int -> M a) -> EqualityProp (M Int)
seq_read_read _ _ = assumedProp

{-@ reflect seq_read_read_aux1 @-}
seq_read_read_aux1 :: Natural -> (Int -> Int -> M a) -> M a
seq_read_read_aux1 i f = read i >>= \x -> read i >>= \x' -> f x x'

{-@ reflect seq_read_read_aux2 @-}
seq_read_read_aux2 :: Natural -> (Int -> Int -> M a) -> M a
seq_read_read_aux2 i f = read i >>= \x -> read i >>= \_ -> f x x

{-@
assume
liftM_read ::
  i:Natural -> f:(Int -> Int -> Int) ->
  EqualProp (M Int)
    {liftM2 f (read i) (read i)}
    {liftM (diagonalize f) (read i)}
@-}
liftM_read :: Natural -> (Int -> Int -> Int) -> EqualityProp (M Int)
liftM_read _ _ = assumedProp

{-@
assume
seq_commutativity_write ::
  i:Natural -> j:{j:Natural | i /= j} -> x:Int -> y:Int ->
  EqualProp (M Unit)
    {write i x >> write j y}
    {write j y >> write i x}
@-}
seq_commutativity_write :: Natural -> Natural -> Int -> Int -> EqualityProp (M ())
seq_commutativity_write _ _ _ _ = assumedProp

{-@
assume
seq_associativity_write ::
  i:Natural -> j:{j:Natural | i /= j} -> x:Int -> y:Int ->
  EqualProp (m Unit)
    {(read i >> pure it) >> write j x}
    {write j x >> (read i >> pure it)}
@-}
seq_associativity_write :: Natural -> Natural -> Int -> Int -> EqualityProp (m Unit)
seq_associativity_write _ _ _ _ = assumedProp

-- array lemmas

{-@
swap_id ::
  Equality (M Unit) =>
  i:Natural ->
  EqualProp (M Unit)
    {swap i i}
    {pure it}
@-}
swap_id :: Natural -> EqualityProp (M ())
swap_id = undefined

-- [ref 9]
{-@
writeList_append ::
  Equality (M Unit) =>
  i:Natural -> xs:List Int -> ys:List Int ->
  EqualProp (M Unit)
    {writeList i (append xs ys)}
    {writeList i xs >> writeList (add i (length xs)) ys}
@-}
writeList_append :: Equality (M Unit) => Natural -> List Int -> List Int -> EqualityProp (M ())
writeList_append i Nil ys =
  [eqpropchain|
      writeList i (Nil ++ ys)
    %==
      writeList i ys
        %by %rewrite Nil ++ ys %to ys
        %by %smt
        %by append_identity ys
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
--
writeList_append i (Cons x xs) ys =
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
        %by writeList_append (S i) xs ys
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

{-@
assume
write_redundancy ::
  Equality (M Unit) =>
  i:Natural -> x:Int ->
  EqualProp (M Unit)
    {write i x >> write i x}
    {write i x}
@-}
write_redundancy :: Equality (M Unit) => Natural -> Int -> EqualityProp (M Unit)
write_redundancy i x = assumedProp -- !ASSUMED

{-@
writeList_redundancy ::
  Equality (M Unit) =>
  i:Natural -> xs:List Int ->
  EqualProp (M Unit)
    {writeList i xs >> writeList i xs}
    {writeList i xs}
@-}
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

{-@
writeList_commutativity ::
  Equality (M Unit) =>
  i:Natural -> xs:List Int -> ys:List Int ->
  EqualProp (M Unit)
    {seq (writeList i xs) (writeList (add i (length xs)) ys)}
    {seq (writeList (add i (length xs)) ys) (writeList i xs)}
@-}
writeList_commutativity :: Equality (M ()) => Natural -> List Int -> List Int -> EqualityProp (M ())
writeList_commutativity = undefined -- TODO

{-@
writeList_read ::
  Equality (M Int) =>
  i:Natural -> x:Int -> xs:List Int ->
  EqualProp (M Int)
    {seq (writeList i (Cons x xs)) (read (add i (length xs)))}
    {seq (writeList i (Cons x xs)) (pure x)}
@-}
writeList_read :: Equality (M Int) => Natural -> Int -> List Int -> EqualityProp (M Int)
writeList_read i x xs = undefined

{-@
writeList_singleton ::
  Equality (M Unit) =>
  i:Natural -> x:Int ->
  EqualProp (M Unit)
    {writeList i (Cons x Nil)}
    {write i x}
@-}
writeList_singleton :: Equality (M Unit) => Natural -> Int -> EqualityProp (M ())
writeList_singleton i x = undefined
