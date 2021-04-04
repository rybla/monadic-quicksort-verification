{-# LANGUAGE TemplateHaskell #-}

module Control.Refined.Monad.Array where

import Control.Refined.Monad
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Relation.Equality.Prop.Reasoning
import Prelude hiding (Monad, length, pure, read, readList, seq, (>>), (>>=))

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
    (writeList ary i (xs `append` ys))
    (pure mnd (length xs, length ys))
  where
    mnd = monad ary

{-@ reflect writeListToLength3 @-}
writeListToLength3 ::
  Array m a -> Index -> (List a, List a, List a) -> m (Natural, Natural, Natural)
writeListToLength3 ary i (xs, ys, zs) =
  (seq mnd)
    (writeList ary i (xs `append` (ys `append` ys)))
    (pure mnd (length xs, length ys, length zs))
  where
    mnd = monad ary

{-
# Lemmas
-}

-- ? this proof takes 11m to check...
{-@ assume
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
  $( transitivity_chain
       [ [|
           ( writeList ary i (Nil `append` ys),
             (substitutability (writeList ary i) (Nil `append` ys) ys)
               (reflexivity ys ? append_identity ys)
               ? writeList ary i (Nil `append` ys)
               ? writeList ary i ys
           )
           |],
         [|
           ( writeList ary i ys,
             etaEquivalency it (writeList ary i ys)
               ? apply (\_ -> writeList ary i ys) it
           )
           |],
         [|
           ( apply (\_ -> writeList ary i ys) it,
             symmetry
               (pure mnd it >>= apply (\_ -> writeList ary i ys))
               (apply (\_ -> writeList ary i ys) it)
               $ bind_identity_left mnd it (apply (\_ -> writeList ary i ys))
           )
           |],
         [|
           ( pure mnd it >>= apply (\_ -> writeList ary i ys),
             reflexivity $ pure mnd it >>= apply (\_ -> writeList ary i ys)
           )
           |],
         [|
           ( pure mnd it >> writeList ary i ys,
             reflexivity $ pure mnd it >> writeList ary i ys
           )
           |],
         [|
           ( writeList ary i Nil >> writeList ary i ys,
             reflexivity (writeList ary i Nil >> writeList ary i ys)
               ? add_identity i
           )
           |],
         [|
           ( writeList ary i Nil >> writeList ary (i `add` Z) ys,
             reflexivity $ writeList ary i Nil >> writeList ary (i `add` Z) ys
           )
           |]
       ]
       [|writeList ary i Nil >> writeList ary (i `add` length Nil) ys|]
   )
  where
    (>>) = seq mnd
    (>>=) = bind mnd
    mnd = monad ary
--
writeList_append ary i (Cons x xs) ys =
  $( transitivity_chain
       [ [|
           ( writeList ary i (Cons x xs `append` ys),
             substitutability
               (writeList ary i)
               (Cons x xs `append` ys)
               (Cons x (xs `append` ys))
               $ reflexivity $
                 Cons x (xs `append` ys)
                   ? Cons x (xs `append` ys)
           )
           |],
         [|
           ( writeList ary i (Cons x (xs `append` ys)),
             reflexivity $
               write ary i x >> writeList ary (S i) (xs `append` ys)
                 ? writeList ary i (Cons x (xs `append` ys))
           )
           |],
         [|
           ( write ary i x >> writeList ary (S i) (xs `append` ys),
             substitutability
               (seq mnd (write ary i x))
               (writeList ary (S i) (xs `append` ys))
               (writeList ary (S i) xs >> writeList ary (S i `add` length xs) ys)
               $ writeList_append ary (S i) xs ys
           )
           |],
         [|
           ( write ary i x >> (writeList ary (S i) xs >> writeList ary (S i `add` length xs) ys),
             substitutability
               (apply (\j -> write ary i x >> (writeList ary (S i) xs >> writeList ary j ys)))
               (S i `add` length xs)
               (S (i `add` length xs))
               ( reflexivity $
                   S i `add` length xs
                     ? S (i `add` length xs)
               )
               ? apply (\j -> write ary i x >> (writeList ary (S i) xs >> writeList ary j ys)) (S i `add` length xs)
               ? apply (\j -> write ary i x >> (writeList ary (S i) xs >> writeList ary j ys)) (S (i `add` length xs))
           )
           |],
         [|
           ( write ary i x >> (writeList ary (S i) xs >> writeList ary (S (i `add` length xs)) ys),
             symmetry
               ((write ary i x >> writeList ary (S i) xs) >> writeList ary (S (i `add` length xs)) ys)
               (write ary i x >> (writeList ary (S i) xs >> writeList ary (S (i `add` length xs)) ys))
               $ (seq_associativity mnd)
                 (write ary i x)
                 (writeList ary (S i) xs)
                 (writeList ary (S (i `add` length xs)) ys)
           )
           |],
         [|
           ( (write ary i x >> writeList ary (S i) xs) >> writeList ary (S (i `add` length xs)) ys,
             substitutability
               (apply (\j -> (write ary i x >> writeList ary (S i) xs) >> writeList ary j ys))
               (S (i `add` length xs))
               (i `add` S (length xs))
               ( reflexivity $
                   i `add` S (length xs)
                     ? add_S_right i (length xs)
               )
               ? apply (\j -> (write ary i x >> writeList ary (S i) xs) >> writeList ary j ys) (S (i `add` length xs))
               ? apply (\j -> (write ary i x >> writeList ary (S i) xs) >> writeList ary j ys) (i `add` S (length xs))
           )
           |],
         [|
           ( (write ary i x >> writeList ary (S i) xs) >> writeList ary (i `add` S (length xs)) ys,
             substitutability
               (apply (\j -> (write ary i x >> writeList ary (S i) xs) >> writeList ary (i `add` j) ys))
               (S (length xs))
               (length (Cons x xs))
               ( reflexivity $
                   S (length xs)
                     ? length (Cons x xs)
               )
               ? apply (\j -> (write ary i x >> writeList ary (S i) xs) >> writeList ary (i `add` j) ys) (S (length xs))
               ? apply (\j -> (write ary i x >> writeList ary (S i) xs) >> writeList ary (i `add` j) ys) (length (Cons x xs))
           )
           |],
         [|
           ( (write ary i x >> writeList ary (S i) xs) >> writeList ary (i `add` length (Cons x xs)) ys,
             substitutability
               (apply (\m -> m >> writeList ary (i `add` length (Cons x xs)) ys))
               (write ary i x >> writeList ary (S i) xs)
               (writeList ary i (Cons x xs))
               ( reflexivity $
                   write ary i x >> writeList ary (S i) xs
                     ? writeList ary i (Cons x xs)
               )
               ? apply (\m -> m >> writeList ary (i `add` length (Cons x xs)) ys) (write ary i x >> writeList ary (S i) xs)
               ? apply (\m -> m >> writeList ary (i `add` length (Cons x xs)) ys) (writeList ary i (Cons x xs))
           )
           |]
       ]
       [|writeList ary i (Cons x xs) >> writeList ary (i `add` length (Cons x xs)) ys|]
   )
  where
    (>>) = seq mnd
    (>>=) = bind mnd
    mnd = monad ary
