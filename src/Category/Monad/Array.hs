module Category.Monad.Array where

import Category.Monad
import Data.Natural
import Data.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (Monad, length, pure, read, readList, seq)

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
    read_write ::
      i:Index ->
      EqualProp (m Unit)
        {bind monad (read i) (write i)}
        {pure monad it},
    write_read ::
      i:Index ->
      x:a ->
      EqualProp (m a)
        {seq monad (write i x) (read i)}
        {seq monad (write i x) (pure monad x)},
    write_write ::
      i:Index ->
      x:a ->
      y:a ->
      EqualProp (m Unit)
        {seq monad (write i x) (write i y)}
        {write i y},
    read_read ::
      i:Index ->
      f:(a -> a -> a) ->
      EqualProp (m a)
        {map2 monad f (read i) (read i)}
        {map monad (diagonalize f) (read i)},
    read_commutativity ::
      i:Index ->
      j:Index ->
      EqualProp (m a)
        {seq monad (read i) (read j)}
        {seq monad (read j) (read i)},
    write_commutativity ::
      i:Index ->
      j:Index ->
      {_:Proof | i /= j} ->
      x:a ->
      y:a ->
      EqualProp (m Unit)
        {seq monad (write i x) (write j y)}
        {seq monad (write j y) (write i x)},
    read_write_commutativity ::
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
    read_write ::
      Index ->
      EqualityProp (m Unit),
    write_read ::
      Index ->
      a ->
      EqualityProp (m a),
    write_write ::
      Index ->
      a ->
      a ->
      EqualityProp (m Unit),
    read_read ::
      Index ->
      (a -> a -> a) ->
      EqualityProp (m a),
    read_commutativity ::
      Index ->
      Index ->
      EqualityProp (m a),
    write_commutativity ::
      Index ->
      Index ->
      Proof ->
      a ->
      a ->
      EqualityProp (m Unit),
    read_write_commutativity ::
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
readList :: Array m a -> Index -> Natural -> m [a]
readList ary i Z = pure mnd []
  where
    mnd = monad ary
readList ary i (S n) = map2 mnd (:) (read ary i) (readList ary (S i) n)
  where
    mnd = monad ary

{-@ reflect writeList @-}
writeList :: Array m a -> Index -> [a] -> m Unit
writeList ary i [] = pure mnd it
  where
    mnd = monad ary
writeList ary i (x : xs) = seq mnd (write ary i x) (writeList ary (S i) xs)
  where
    mnd = monad ary

{-@ reflect writeListToLength @-}
writeListToLength :: Array m a -> Index -> [a] -> m Natural
writeListToLength ary i xs = seq mnd (writeList ary i xs) (pure mnd (length xs))
  where
    mnd = monad ary

{-@ reflect writeListToLength2 @-}
writeListToLength2 ::
  Array m a -> Index -> ([a], [a]) -> m (Natural, Natural)
writeListToLength2 ary i (xs, ys) =
  (seq mnd)
    (writeList ary i (xs `append` ys))
    (pure mnd (length xs, length ys))
  where
    mnd = monad ary

{-@ reflect writeListToLength3 @-}
writeListToLength3 ::
  Array m a -> Index -> ([a], [a], [a]) -> m (Natural, Natural, Natural)
writeListToLength3 ary i (xs, ys, zs) =
  (seq mnd)
    (writeList ary i (xs `append` (ys `append` ys)))
    (pure mnd (length xs, length ys, length zs))
  where
    mnd = monad ary

{-
# Lemmas
-}

{-@
writeList_append ::
  ary:Array m a ->
  i:Index ->
  xs:[a] ->
  ys:[a] ->
  EqualProp (m Unit)
    {writeList ary i (append xs ys)}
    {seq (monad ary) (writeList ary i xs) (writeList ary (add i (length xs)) ys)}
@-}
writeList_append ::
  Array m a ->
  Index ->
  [a] ->
  [a] ->
  EqualityProp (m Unit)
writeList_append ary i xs ys = undefined
