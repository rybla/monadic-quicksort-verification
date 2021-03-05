module Category.Monad.Array where

import Category.Monad
import Data.Natural
import Data.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
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
  (Equality (m a), Equality (m Unit)) =>
  ary:Array m a ->
  i:Index ->
  xs:[a] ->
  ys:[a] ->
  EqualProp (m Unit)
    {writeList ary i (append xs ys)}
    {seq (monad ary) (writeList ary i xs) (writeList ary (add i (length xs)) ys)}
@-}
writeList_append ::
  (Equality (m a), Equality (m Unit)) =>
  Array m a ->
  Index ->
  [a] ->
  [a] ->
  EqualityProp (m Unit)
--
writeList_append ary i [] ys =
  let t1 = writeList_ i ([] `append` ys)
      t2 = writeList_ i ys -- append_identity
      t3 = (\_ -> writeList_ i ys) it -- betaEquivalencyTrivial
      t4 = pure_ it >>= (\_ -> writeList_ i ys) -- bind_identity_left
      t5 = pure_ it >> writeList_ i ys -- def >>
      t6 = writeList_ i [] >> writeList_ i ys -- def writeList
      t7 = writeList_ i [] >> writeList_ (i `add` Z) ys -- add_identity i
      t8 = writeList_ i [] >> writeList_ (i `add` length []) ys -- def length
   in (transitivity t1 t4 t8)
        ( (transitivity t1 t2 t4)
            -- t1 = t2
            ( (substitutability (writeList_ i) ([] `append` ys) ys) -- writeList_ i (...)
                ( (fromSMT ([] `append` ys) ys)
                    (append_identity ys) -- [] `append` ys = ys
                )
                ? writeList_ i ([] `append` ys)
                ? writeList_ i ys
            )
            ( (transitivity t2 t3 t4)
                -- t2 = t3
                ( betaEquivalencyTrivial it (writeList_ i ys)
                    ? (\_ -> writeList_ i ys) it
                )
                -- t3 = t4
                ( (symmetry (pure_ it >>= (\_ -> writeList_ i ys)) ((\_ -> writeList_ i ys) it))
                    ( bind_identity_left mnd it (\_ -> writeList_ i ys)
                        ? (pure_ it >>= (\_ -> writeList_ i ys))
                    )
                )
            )
        )
        ( (transitivity t4 t6 t8)
            ( (transitivity t4 t5 t6)
                -- t4 = t5
                undefined
                -- t5 = t6
                undefined
            )
            ( (transitivity t6 t7 t8)
                -- t6 = t7
                undefined
                -- t7 = t7
                undefined
            )
        )
  where
    writeList_ = writeList ary
    (>>) = seq mnd
    (>>=) = bind mnd
    pure_ = pure mnd
    mnd = monad ary
--
writeList_append ary i (x : xs) ys = undefined

{-@
test ::
  ary:Array m a ->
  i:Index ->
  xs:[a] ->
  EqualProp (m Unit)
    {writeList ary i (append [] xs)}
    {writeList ary i xs}
@-}
test :: Array m a -> Index -> [a] -> EqualityProp (m Unit)
test ary i xs =
  let t1 = writeList_ i ([] `append` xs)
      t2 = writeList_ i xs -- append_identity
   in (substitutability (writeList_ i) ([] `append` xs) xs) -- writeList_ i (...)
        (fromSMT ([] `append` xs) xs (append_identity xs)) -- [] `append` xs = xs
        ? writeList_ i ([] `append` xs)
        ? writeList_ i xs
  where
    writeList_ = writeList ary
    (>>) = seq mnd
    (>>=) = bind mnd
    pure_ = pure mnd
    mnd = monad ary
