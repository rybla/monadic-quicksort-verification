module Control.Refined.Monad.Array where

import Control.Refined.Monad
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (Monad, length, pure, read, readList, seq, (+), (++), (>>), (>>=))

{-
# Array monad
-}

{-
## Data
-}

{-@
type Index = Natural
@-}
type Index = Natural

{-@
data Array m a = Array
  { monad :: Monad m,
    read :: Index -> m a,
    write :: Index -> a -> m Unit,
    bind_read_write ::
      i:Index ->
      EqualProp (m Unit)
        {bind monad (read i) (write i)}
        {pure monad it},
    seq_write_read ::
      i:Index ->
      x:a ->
      EqualProp (m a)
        {seq monad (write i x) (read i)}
        {seq monad (write i x) (pure monad x)},
    seq_write_write ::
      i:Index ->
      x:a ->
      y:a ->
      EqualProp (m Unit)
        {seq monad (write i x) (write i y)}
        {write i y},
    map_read ::
      i:Index ->
      f:(a -> a -> a) ->
      EqualProp (m a)
        {map2 monad f (read i) (read i)}
        {map monad (diagonalize f) (read i)},
    seq_commutativity_read ::
      i:Index ->
      j:Index ->
      EqualProp (m a)
        {seq monad (read i) (read j)}
        {seq monad (read j) (read i)},
    seq_commutativity_write ::
      i:Index ->
      j:Index ->
      {_:Proof | i /= j} ->
      x:a ->
      y:a ->
      EqualProp (m Unit)
        {seq monad (write i x) (write j y)}
        {seq monad (write j y) (write i x)},
    seq_associativity_write ::
      i:Index ->
      j:Index ->
      {_:Proof | i /= j} ->
      x:a ->
      y:a ->
      EqualProp (m Unit)
        {seq monad (seq monad (read i) (pure monad it)) (write j x)}
        {seq monad (write j x) (seq monad (read i) (pure monad it))}
  }
@-}
data Array m a = Array
  { monad :: Monad m,
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
    map_read ::
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
      Proof ->
      a ->
      a ->
      EqualityProp (m Unit),
    seq_associativity_write ::
      Index ->
      Index ->
      Proof ->
      a ->
      a ->
      EqualityProp (m Unit)
  }

{-
## Utilities
-}

{-@ reflect readList @-}
readList :: Array m a -> Index -> Natural -> m (List a)
readList ary i Z = pure mnd Nil
  where
    mnd = monad ary
readList ary i (S n) = map2 mnd Cons (read ary i) (readList ary (S i) n)
  where
    mnd = monad ary

{-@ reflect writeList @-}
writeList :: Array m a -> Index -> List a -> m Unit
writeList ary i Nil = pure mnd it
  where
    mnd = monad ary
writeList ary i (Cons x xs) = write ary i x >> writeList ary (S i) xs
  where
    (>>) = seq mnd
    mnd = monad ary

{-@ reflect writeListToLength @-}
writeListToLength :: Array m a -> Index -> List a -> m Natural
writeListToLength ary i xs = seq mnd (writeList ary i xs) (pure mnd (length xs))
  where
    (>>) = seq mnd
    mnd = monad ary

{-@ reflect writeListToLength2 @-}
writeListToLength2 ::
  Array m a -> Index -> (List a, List a) -> m (Natural, Natural)
writeListToLength2 ary i (xs, ys) =
  (seq mnd)
    (writeList ary i (xs ++ ys))
    (pure mnd (length xs, length ys))
  where
    mnd = monad ary

{-@ reflect writeListToLength3 @-}
writeListToLength3 ::
  Array m a -> Index -> (List a, List a, List a) -> m (Natural, Natural, Natural)
writeListToLength3 ary i (xs, ys, zs) =
  (seq mnd)
    (writeList ary i (xs ++ (ys ++ ys)))
    (pure mnd (length xs, length ys, length zs))
  where
    mnd = monad ary

{-
# Lemmas
-}

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
    {seq (monad ary) (writeList ary i xs) (writeList ary (add i (length xs)) ys)}
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
  let --
      -- steps
      --
      t1 = writeList ary i (Nil ++ ys)
      -- append_identity
      t2 = writeList ary i ys
      -- betaEquivalencyTrivial
      t3 = (\_ -> writeList ary i ys) it
      -- bind_identity_left
      t4 = pure mnd it >>= (\_ -> writeList ary i ys)
      -- >>
      t5 = pure mnd it >> writeList ary i ys
      -- writeList
      t6 = writeList ary i Nil >> writeList ary i ys
      -- add_identity i
      t7 = writeList ary i Nil >> writeList ary (i `add` Z) ys
      -- length
      t8 = writeList ary i Nil >> writeList ary (i `add` length Nil) ys
      --
      -- proofs
      --
      ep_t1_t2 =
        (substitutability (writeList ary i) (Nil ++ ys) ys) -- writeList_ i (...)
          ( (fromSMT (Nil ++ ys) ys)
              (append_identity ys) -- Nil ++ ys = ys
          )
          ? writeList ary i (Nil ++ ys)
          ? writeList ary i ys
      ep_t2_t3 =
        betaEquivalencyTrivial it (writeList ary i ys)
          ? (\_ -> writeList ary i ys) it
      ep_t3_t4 =
        -- symmetry t4 t3 $
        --   bind_identity_left mnd it (\_ -> writeList_ i ys)
        undefined -- TODO
      ep_t4_t5 =
        fromSMT t4 t5 trivial
      ep_t5_t6 =
        fromSMT t5 t6 trivial
      ep_t6_t7 =
        fromSMT t6 t7 $ add_identity i
      ep_t7_t8 =
        fromSMT t7 t8 trivial
   in --
      -- structure
      --
      transitivity t1 t2 t8 ep_t1_t2 $
        transitivity t2 t3 t8 ep_t2_t3 $
          transitivity t3 t4 t8 ep_t3_t4 $
            transitivity t4 t5 t8 ep_t4_t5 $
              transitivity t5 t6 t8 ep_t5_t6 $
                transitivity t6 t7 t8 ep_t6_t7 ep_t7_t8
  where
    (>>) = seq mnd
    (>>=) = bind mnd
    mnd = monad ary
--
writeList_append ary i (Cons x xs) ys =
  let --
      -- steps
      --
      t1 = writeList ary i (Cons x xs ++ ys)
      -- Cons x xs ++ ys
      t2 = writeList ary i (Cons x (xs ++ ys))
      -- writeList ...
      t3 = write ary i x >> writeList ary (S i) (xs ++ ys)
      -- writeList_append ary (S i) xs ys
      t4 = write ary i x >> (writeList ary (S i) xs >> writeList ary (S i `add` length xs) ys)
      -- S i `add` length xs
      t5 = write ary i x >> (writeList ary (S i) xs >> writeList ary (S (i `add` length xs)) ys)
      -- symmetry $ seq_associativity (write ary i x) (writeList ary (S i) xs) (writeList ary (S (i `add` length xs)) ys)
      t6 = (write ary i x >> writeList ary (S i) xs) >> writeList ary (S (i `add` length xs)) ys
      -- symmetry $ add_S_right i (lenght xs)
      t7 = (write ary i x >> writeList ary (S i) xs) >> writeList ary (i `add` S (length xs)) ys
      -- symmetry $ length (Cons x xs)
      t8 = (write ary i x >> writeList ary (S i) xs) >> writeList ary (i `add` length (Cons x xs)) ys
      -- symmetry $ writeList ary i (Cons x xs)
      t9 = writeList ary i (Cons x xs) >> writeList ary (i `add` length (Cons x xs)) ys
      --
      -- proofs
      --
      ep_t1_t2 =
        -- substitutability (writeList ary i) (Cons x xs ++ ys) (Cons x (xs ++ ys)) $
        --   fromSMT (Cons x xs ++ ys) (Cons x (xs ++ ys)) trivial
        --     ? writeList ary i (Cons x xs ++ ys)
        --     ? writeList ary i (Cons x (xs ++ ys))
        --     ? xs ++ ys
        undefined -- TODO
      ep_t2_t3 = undefined
      ep_t3_t4 = undefined
      ep_t4_t5 = undefined
      ep_t5_t6 = undefined
      ep_t6_t7 = undefined
      ep_t7_t8 = undefined
      ep_t8_t9 = undefined
   in --
      -- structure
      --
      transitivity t1 t2 t9 ep_t1_t2 $
        transitivity t2 t3 t9 ep_t2_t3 $
          transitivity t3 t4 t9 ep_t3_t4 $
            transitivity t4 t5 t9 ep_t4_t5 $
              transitivity t5 t6 t9 ep_t5_t6 $
                transitivity t6 t7 t9 ep_t6_t7 $
                  transitivity t7 t8 t9 ep_t7_t8 ep_t8_t9
  where
    (>>) = seq mnd
    (>>=) = bind mnd
    mnd = monad ary
