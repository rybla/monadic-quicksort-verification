{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Refined.Monad.Plus where

import Control.Refined.Monad
import Data.Refined.Unit
import Data.Void
import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Prelude hiding (Monad, pure, seq)

{-
# Plus monad
-}

{-
## Data
-}

{-@
data Plus m = Plus
  { monad :: Monad m,
    epsilon :: forall a. m a,
    plus :: forall a. m a -> m a -> m a,
    plus_identityLeft ::
      forall a.
      m:m a ->
      EqualProp (m a)
        {plus epsilon m}
        {m},
    plus_associativity ::
      forall a.
      m1:m a ->
      m2:m a ->
      m3:m a ->
      EqualProp (m a)
        {plus (plus m1 m2) m3}
        {plus m1 (plus m2 m3)},
    plus_distributivity_left ::
      forall a b.
      m1:m a ->
      m2:m a ->
      k:(a -> m b) ->
      EqualProp (m b)
        {bind monad (plus m1 m2) k}
        {plus (bind monad m1 k) (bind monad m2 k)},
    plus_distributivity_right ::
      forall a b.
      m:m a ->
      k1:(a -> m b) ->
      k2:(a -> m b) ->
      EqualProp (m b)
        {bind monad m (\x:a -> plus (k1 x) (k2 x))}
        {plus (bind monad m k1) (bind monad m k2)},
    bind_zero_left ::
      forall a b.
      k:(a -> m b) ->
      EqualProp (m b)
        {bind monad epsilon k}
        {epsilon},
    bind_zero_right ::
      forall a b.
      m:m a ->
      EqualProp (m b)
        {seq monad m epsilon}
        {epsilon}
  }
@-}
data Plus m = Plus
  { monad :: Monad m,
    epsilon :: forall a. m a,
    plus :: forall a. m a -> m a -> m a,
    plus_identityLeft ::
      forall a.
      m a ->
      EqualityProp (m a),
    plus_associativity ::
      forall a.
      m a ->
      m a ->
      m a ->
      EqualityProp (m a),
    plus_distributivity_left ::
      forall a b.
      m a ->
      m a ->
      (a -> m b) ->
      EqualityProp (m b),
    plus_distributivity_right ::
      forall a b.
      m a ->
      (a -> m b) ->
      (a -> m b) ->
      EqualityProp (m b),
    bind_zero_left ::
      forall a b.
      (a -> m b) ->
      EqualityProp (m b),
    bind_zero_right ::
      forall a b.
      m a ->
      EqualityProp (m b)
  }

{-
## Utilities
-}

{-@ reflect plusF @-}
plusF :: Plus m -> (a -> m b) -> (a -> m b) -> (a -> m b)
plusF pls k1 k2 x = plus pls (k1 x) (k2 x)

{-@ reflect guard @-}
guard :: Plus m -> Bool -> m Unit
guard pls b =
  if b
    then pure mnd ()
    else epsilon pls
  where
    mnd = monad pls

guardBy :: Plus m -> (a -> Bool) -> a -> m a
guardBy pls p x = seq mnd (guard pls (p x)) (pure mnd x)
  where
    mnd = monad pls

{-
## Refinement
-}

{-
monad plus refinement: every result of M1 is a possible result of M2. aka
  • M1 refines M2
  • M2 can be refined to M1
  • M2 subsumes M1
where
  • Pls :: Plus m
  • M1 :: m a
  • M2 :: m a
-}
{-@
type RefinesPlus m a Pls M1 M2 =
      EqualProp (m a)
        {plus Pls M1 M2}
        {M2}
@-}

{-
monad plus refinement of functions. aka
  F1
where
  • Pls :: Plus m
  • K1 :: Plus m -> a -> m b
  • K2 :: Plus m -> a -> m b
-}
-- TODO: more convenient as ext eq or fun to eq?
{-@
type RefinesPlusF m a b Pls K1 K2 =
      x:a ->
      EqualProp (m b)
        {plus Pls (K1 Pls x) (K2 Pls x)}
        {K2 Pls x}
@-}

{-
### Properties
-}

{-@
refinesplus_reflexivity ::
  Equality (m a) =>
  pls:Plus m ->
  m:m a ->
  RefinesPlus m a {pls} {m} {m}
@-}
refinesplus_reflexivity :: Equality (m a) => Plus m -> m a -> EqualityProp (m a)
refinesplus_reflexivity pls m =
  [eqpropchain|
      m <+> m
    %eqprop 
      undefined -- TODO
    %eqprop 
      m
  |]
  where
    (<+>) = plus pls

{-@
refinesplus_antisymmetry ::
  Equality (m a) =>
  pls:Plus m ->
  m1:m a -> m2: m a ->
  RefinesPlus m a {pls} {m1} {m2} ->
  RefinesPlus m a {pls} {m2} {m1} -> Void
@-}
refinesplus_antisymmetry ::
  Equality (m a) =>
  Plus m ->
  m a ->
  m a ->
  EqualityProp (m a) ->
  EqualityProp (m a) ->
  Void
-- TODO: how to prove Void from something false?
refinesplus_antisymmetry pls m1 m2 rp12 rp21 = undefined

--   absurd
--     [eqpropchain|
--         m1 <+> m2
--       %eqprop
--         m2 <+> m1
--     |]
-- where
--   (<+>) = plus pls

{-@
refinesplus_transitivity ::
  Equality (m a) =>
  pls:Plus m ->
  m1:m a -> m2:m a -> m3:m a ->
  RefinesPlus m a {pls} {m1} {m2} ->
  RefinesPlus m a {pls} {m2} {m3} ->
  RefinesPlus m a {pls} {m1} {m3}
@-}
refinesplus_transitivity ::
  Equality (m a) =>
  Plus m ->
  m a ->
  m a ->
  m a ->
  EqualityProp (m a) ->
  EqualityProp (m a) ->
  EqualityProp (m a)
-- ? very stylish format
refinesplus_transitivity pls m1 m2 m3 rp12 rp23 =
  [eqpropchain|
              m1 <+> m3
    %eqprop 
              m1 <+> (m2 <+> m3)  
                                  %by %rewrite m3 %to m2 <+> m3
                                  %by %symmetry
                                  %by rp23
    %eqprop   
              (m1 <+> m2) <+> m3  
                                  %by %symmetry 
                                  %by plus_associativity pls m1 m2 m3
    %eqprop   
              m2 <+> m3           
                                  %by %rewrite m1 <+> m2 %to m2
                                  %by rp12 
    %eqprop   
              m3                  
                                  %by rp23 
  |]
  where
    (<+>) = plus pls

{-
  [eqpropchain|
      m1 <+> m3
    %eqprop
      m1 <+> (m2 <+> m3)
        %by %rewrite m3
                 %to m2 <+> m3
        %by %symmetry
        %by rp23
    %eqprop
      (m1 <+> m2) <+> m3
        %by %symmetry
        %by plus_associativity pls m1 m2 m3
    %eqprop
      m2 <+> m3
        %by %rewrite m1 <+> m2
                 %to m2
        %by rp12
    %eqprop
      m3
        %by rp23
  |]
-}

-- [ref] Lemma 1
{-
TODO
shouldn't need `mnd:Monad m` param, but it forgets what `bind` is  if i remove
it.... even though `mnd` isn't being used anywhere!!!
-}
{-@
bind_monotonic_refinesplus ::
  (Equality (m a), Equality (m b)) =>
  Monad m ->
  pls:Plus m ->
  m1:m a -> m2:m a -> k:(a -> m b) ->
  RefinesPlus m a {pls} {m1} {m2} ->
  RefinesPlus m b {pls} {bind (monad pls) m1 k} {bind (monad pls) m2 k}
@-}
bind_monotonic_refinesplus ::
  (Equality (m a), Equality (m b)) =>
  Monad m ->
  Plus m ->
  m a ->
  m a ->
  (a -> m b) ->
  EqualityProp (m a) ->
  EqualityProp (m b)
bind_monotonic_refinesplus _ pls m1 m2 k rp_m1_m2 =
  [eqpropchain|
      plus pls (bind mnd m1 k) (bind mnd m2 k)
    %eqprop 
      bind mnd (plus pls m1 m2) k
        %by %symmetry 
        %by plus_distributivity_left pls m1 m2 k 
    %eqprop 
      bind mnd m2 k 
        %by %rewrite plus pls m1 m2
                 %to m2
        %by rp_m1_m2 
  |]
  where
    mnd = monad pls

{-@
bind_monotonic_refinesplusF ::
  (Equality (m a), Equality (m b)) =>
  Monad m ->
  pls:Plus m ->
  m:m a -> k1:(Plus m -> a -> m b) -> k2:(Plus m -> a -> m b) ->
  RefinesPlusF m a b {pls} {k1} {k2} ->
  EqualityProp (m b)
@-}
-- RefinesPlus m b {pls} {bind (monad pls) m k1} {bind (monad pls) m k2}
bind_monotonic_refinesplusF ::
  (Equality (m a), Equality (m b)) =>
  Monad m ->
  Plus m ->
  m a ->
  (Plus m -> a -> m b) ->
  (Plus m -> a -> m b) ->
  (a -> EqualityProp (m b)) ->
  EqualityProp (m b)
bind_monotonic_refinesplusF _ pls m _k1 _k2 e_k1_k2 =
  [eqpropchain|
      plus pls (bind mnd m k1) (bind mnd m k2)
    %eqprop 
      bind mnd m (\x -> plus pls (k1 x) (k2 x))
        %by %symmetry
        %by plus_distributivity_right pls m k1 k2
    %eqprop 
      bind mnd m (\x -> k2 x)
        %by %rewrite (\x -> plus pls (k1 x) (k2 x))
                 %to (\x -> k2 x)
        %by undefined -- TODO: why not `e_k1_k2 x`?
    %eqprop 
      (bind mnd m k2)
        %by %rewrite (\x -> k2 x)
                 %to k2
        %by %extend x 
        %by %smt
        %by apply (\x -> k2 x) 
          ? apply k2 x 
  |]
  where
    mnd = monad pls
    (k1, k2) = (_k1 pls, _k2 pls)

{-
[ref] "If can be proved that `guard p` commutes with all `m` if non-determinism
is the only effect in `m` -- a property we will need many times.
-}
{-@
guard_commutes ::
  Equality (m c) =>
  Monad m ->
  pls:Plus m ->
  b:Bool ->
  m:m b ->
  k:(Monad m -> Tuple -> b -> m c) ->
  EqualProp (m c)
    {bind (monad pls) (guard pls b) (apply (\x:Tuple -> bind (monad pls) m (apply (\y:b -> k (monad pls) it y))))}
    {bind (monad pls) m (apply (\y:b -> bind (monad pls) (guard pls b) (apply (\x:Tuple -> k (monad pls) it y))))}
@-}
guard_commutes ::
  Equality (m c) =>
  Monad m ->
  Plus m ->
  Bool ->
  m b ->
  (Monad m -> Unit -> b -> m c) ->
  EqualityProp (m c)
guard_commutes _ pls b m k =
  [eqpropchain|
      bind mnd (guard pls b) (apply (\() -> bind mnd m (apply (\x -> k mnd () x))))
    %eqprop 
      undefined -- TODO 
    %eqprop 
      bind mnd m (apply (\x -> bind mnd (guard pls b) (apply (\() -> k mnd () x))))
  |]
  where
    mnd = monad pls

{-@ reflect andBool @-}
andBool :: Bool -> Bool -> Bool
andBool = (&&)

{-@
guard_and ::
  Equality (m Tuple) =>
  Monad m ->
  pls:Plus m ->
  p:Bool -> q:Bool ->
  EqualProp (m Tuple)
    {guard pls (andBool p q)}
    {seq (monad pls) (guard pls p) (guard pls q)}
@-}
guard_and ::
  Equality (m ()) =>
  Monad m ->
  Plus m ->
  Bool ->
  Bool ->
  EqualityProp (m ())
guard_and _ pls True q =
  [eqpropchain|
      guard pls (andBool True q)
    %eqprop
      guard pls q
    %eqprop
      seq mnd (pure mnd ()) (guard pls q)
        %by seq_identity_left mnd () (guard pls q)
          ? undefined -- TODO: what else??
    %eqprop 
      seq mnd (guard pls True) (guard pls q)
        %by %smt
        %by guard pls True
  |]
  where
    mnd = monad pls
guard_and _ pls False q =
  [eqpropchain|
      guard pls (andBool False q)
    %eqprop
      guard pls False
    %eqprop
      epsilon pls
        %by %smt 
        %by guard pls False 
    %eqprop
      bind mnd (epsilon pls) (apply (\_ -> guard pls q))
        %by %symmetry
        %by bind_zero_left pls (apply (\_ -> guard pls q))
    %eqprop
      bind mnd (guard pls False) (apply (\_ -> guard pls q))
        %by %smt
        %by guard pls False
    %eqprop
      seq mnd (guard pls False) (guard pls q)
        %by %smt
        %by seq mnd (guard pls False) (guard pls q)
  |]
  where
    mnd = monad pls
