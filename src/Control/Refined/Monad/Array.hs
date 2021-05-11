{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Control.Refined.Monad.Array where

import Control.Refined.Monad
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Prelude hiding (Monad, length, pure, read, readList, seq, (>>), (>>=))

{-

-- |
-- = Array Monad
--

-- |
-- == Data
--

type Index = Natural

{-@
data Array m a = Array
  { arrayMonad :: Monad m,
    read :: Index -> m a,
    write :: Index -> a -> m Unit,
    bind_read_write ::
      i:Index ->
      {_:EqualityProp (m Unit) | eqprop (bind arrayMonad (read i) (write i)) (pure arrayMonad it)},
    seq_write_read ::
      i:Index ->
      x:a ->
      {_:EqualityProp (m a) | eqprop (seq arrayMonad (write i x) (read i)) (seq arrayMonad (write i x) (pure arrayMonad x))},
    seq_write_write ::
      i:Index ->
      x:a ->
      y:a ->
      {_:EqualityProp (m Unit) | eqprop (seq arrayMonad (write i x) (write i y)) (write i y)},
    liftM_read ::
      i:Index ->
      f:(a -> a -> a) ->
      {_:EqualityProp (m a) | eqprop (liftM2 arrayMonad f (read i) (read i)) (liftM arrayMonad (diagonalize f) (read i))},
    seq_commutativity_read ::
      i:Index ->
      j:Index ->
      {_:EqualityProp (m a) | eqprop (seq arrayMonad (read i) (read j)) (seq arrayMonad (read j) (read i))},
    seq_commutativity_write ::
      i:Index ->
      j:{j:Index | i /= j} ->
      x:a ->
      y:a ->
      {_:EqualityProp (m Unit) | eqprop (seq arrayMonad (write i x) (write j y)) (seq arrayMonad (write j y) (write i x))},
    seq_associativity_write ::
      i:Index ->
      j:{j:Index | i /= j} ->
      x:a ->
      y:a ->
      {_:EqualityProp (m Unit) | eqprop (seq arrayMonad (seq arrayMonad (read i) (pure arrayMonad it)) (write j x)) (seq arrayMonad (write j x) (seq arrayMonad (read i) (pure arrayMonad it)))}
  }
@-}
data Array m a = Array
  { arrayMonad :: Monad m,
    read :: Index -> m a,
    write :: Index -> a -> m Unit,
    bind_read_write ::
      Index ->
      EqualityProp (m Unit),
    seq_write_read ::
      Index ->
      a ->
      EqualityProp (m a),
    seq_write_write ::
      Index ->
      a ->
      a ->
      EqualityProp (m Unit),
    liftM_read ::
      Index ->
      (a -> a -> a) ->
      EqualityProp (m a),
    seq_commutativity_read ::
      Index ->
      Index ->
      EqualityProp (m a),
    seq_commutativity_write ::
      Index ->
      Index ->
      a ->
      a ->
      EqualityProp (m Unit),
    seq_associativity_write ::
      Index ->
      Index ->
      a ->
      a ->
      EqualityProp (m Unit)
  }

-- |
-- == Utilities
--

{-@ reflect readList @-}
readList :: Array m a -> Index -> Natural -> m (List a)
readList ary i Z = pure mnd Nil
  where
    mnd = arrayMonad ary
readList ary i (S n) = liftM2 mnd Cons (read ary i) (readList ary (S i) n)
  where
    mnd = arrayMonad ary

{-@ reflect writeList @-}
writeList :: Array m a -> Index -> List a -> m Unit
writeList ary i Nil = pure mnd it
  where
    mnd = arrayMonad ary
writeList ary i (Cons x xs) = write ary i x >> writeList ary (S i) xs
  where
    (>>) = seq mnd
    mnd = arrayMonad ary

{-@ reflect writeListToLength @-}
writeListToLength :: Array m a -> Index -> List a -> m Natural
writeListToLength ary i xs = seq mnd (writeList ary i xs) (pure mnd (length xs))
  where
    (>>) = seq mnd
    mnd = arrayMonad ary

{-@ reflect writeListToLength2 @-}
writeListToLength2 ::
  Array m a -> Index -> (List a, List a) -> m (Natural, Natural)
writeListToLength2 ary i (xs, ys) =
  writeList ary i (xs `append` ys)
    >> pure mnd (length xs, length ys)
  where
    (>>) = seq mnd
    mnd = arrayMonad ary

{-@ reflect writeListToLength3 @-}
writeListToLength3 ::
  Array m a -> Index -> (List a, List a, List a) -> m (Natural, Natural, Natural)
writeListToLength3 ary i (xs, ys, zs) =
  writeList ary i (xs `append` (ys `append` ys))
    >> pure mnd (length xs, length ys, length zs)
  where
    (>>) = seq mnd
    mnd = arrayMonad ary

{-@ reflect swap @-}
swap :: Array m a -> Index -> Index -> m ()
swap ary i j = read ary i >>= \x -> read ary j >>= \y -> write ary i y >> write ary j x
  where
    (>>=) = bind mnd
    (>>) = seq mnd
    mnd = arrayMonad ary

-- |
-- == Lemmas
--

-- [ref] display 9
-- ? this proof takes 11m to check...
{-@
writeList_append ::
  forall m a.
  (Equality (m a), Equality (m Unit)) =>
  ary:Array m a ->
  i:Index ->
  xs:List a ->
  ys:List a ->
  EqualProp (m Unit)
    {writeList ary i (append xs ys)}
    {seq (arrayMonad ary) (writeList ary i xs) (writeList ary (add i (length xs)) ys)}
@-}
writeList_append ::
  forall m a.
  (Equality (m a), Equality (m Unit)) =>
  Array m a ->
  Index ->
  List a ->
  List a ->
  EqualityProp (m Unit)
--
writeList_append ary i Nil ys =
  [eqpropchain|
      writeList ary i (Nil `append` ys)
    %==
      writeList ary i ys
        %by %rewrite Nil `append` ys %to ys
        %by %smt
        %by append_identity ys
    %==
      apply (\_ -> writeList ary i ys) it
        %by %smt
        %by etaEquivalency it (writeList ary i ys)
          ? apply (\_ -> writeList ary i ys) it
    %==
      pure mnd it >>= apply (\_ -> writeList ary i ys)
        %by %symmetry
        %by pure_bind mnd it (apply (\_ -> writeList ary i ys))
    %==
      pure mnd it >> writeList ary i ys
        %by %smt
        %by pure mnd it >>= apply (\_ -> writeList ary i ys)
    %==
      writeList ary i Nil >> writeList ary i ys
        %by %smt
        %by pure mnd it >> writeList ary i ys
    %==
      writeList ary i Nil >> writeList ary (i `add` Z) ys
        %by %smt
        %by add_identity i
    %==
      writeList ary i Nil >> writeList ary (i `add` length Nil) ys
        %by %smt
        %by writeList ary i Nil >> writeList ary (i `add` Z) ys
  |]
  where
    (>>) = seq mnd
    (>>=) = bind mnd
    mnd = arrayMonad ary
--
writeList_append ary i (Cons x xs) ys =
  [eqpropchain|
      writeList ary i (Cons x xs `append` ys)
    %==
      writeList ary i (Cons x (xs `append` ys))
        %by %rewrite Cons x xs `append` ys
                 %to Cons x (xs `append` ys)
        %by %smt
        %by Cons x (xs `append` ys)
    %==
      write ary i x >> writeList ary (S i) (xs `append` ys)
        %by %smt
        %by writeList ary i (Cons x (xs `append` ys))
    %==
      write ary i x >> (writeList ary (S i) xs >> writeList ary (S i `add` length xs) ys)
        %by %rewrite writeList ary (S i) (xs `append` ys)
                 %to writeList ary (S i) xs >> writeList ary (S i `add` length xs) ys
        %by writeList_append ary (S i) xs ys
    %==
      write ary i x >> (writeList ary (S i) xs >> writeList ary (S (i `add` length xs)) ys)
        %by %rewrite S i `add` length xs
                 %to S (i `add` length xs)
        %by %smt
        %by S i `add` length xs
          ? S (i `add` length xs)
    %==
      (write ary i x >> writeList ary (S i) xs) >> writeList ary (S (i `add` length xs)) ys
        %by %symmetry
        %by (seq_associativity mnd)
              (write ary i x)
              (writeList ary (S i) xs)
              (writeList ary (S (i `add` length xs)) ys)
    %==
      (write ary i x >> writeList ary (S i) xs) >> writeList ary (i `add` S (length xs)) ys
        %by %rewrite S (i `add` length xs)
                 %to i `add` S (length xs)
        %by %smt
        %by i `add` S (length xs)
          ? add_S_right i (length xs)
    %==
      (write ary i x >> writeList ary (S i) xs) >> writeList ary (i `add` length (Cons x xs)) ys
        %by %rewrite S (length xs)
                 %to length (Cons x xs)
        %by %smt
        %by S (length xs)
          ? length (Cons x xs)
    %==
      writeList ary i (Cons x xs) >> writeList ary (i `add` length (Cons x xs)) ys
        %by %rewrite write ary i x >> writeList ary (S i) xs
                 %to writeList ary i (Cons x xs)
        %by %smt
        %by write ary i x >> writeList ary (S i) xs
          ? writeList ary i (Cons x xs)
  |]
  where
    (>>) = seq mnd
    (>>=) = bind mnd
    mnd = arrayMonad ary

-}
