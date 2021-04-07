-- {-# LANGUAGE QuasiQuotes #-}
-- {-# LANGUAGE TemplateHaskell #-}

module Control.Refined.SlowsortList where

import Control.Refined.Monad
import Control.Refined.Monad.Plus
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.Equational
import Relation.Equality.Prop
-- import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (>>), (>>=))

{-@
type Elem = Int
@-}
type Elem = Int

{-@ reflect leq @-}
leq :: Elem -> Elem -> Bool
leq x y = x <= y

{-@ reflect geq @-}
geq :: Elem -> Elem -> Bool
geq x y = y <= x

--
slowsort :: Plus m -> List Elem -> m (List Elem)
slowsort pls = permute pls >=> guardBy pls sorted
  where
    (>=>) = kleisli mnd
    mnd = monad pls

--
{-@ reflect sorted @-}
sorted :: List Elem -> Bool
sorted Nil = True
sorted (Cons x xs) = all (leq x) xs && sorted xs

-- [ref] equation 5
{-@ automatic-instances sorted_middle @-}
{-@
sorted_middle ::
  ys:List Elem ->
  x:Elem ->
  zs:List Elem ->
  {sorted (append ys (append (Cons x Nil) zs)) <=>
   sorted ys && sorted zs && all (geq x) ys && all (leq x) zs}
@-}
--  sorted ys && sorted zs && all (geq x) ys && all (leq x) zs}
sorted_middle :: List Elem -> Elem -> List Elem -> Proof
sorted_middle Nil x zs = ()
sorted_middle (Cons y ys) x zs = undefined

-- TODO: got frustrated with proof
-- sorted (append (Cons y ys) (append (Cons x (Cons y ys)) zs))
--   ==. sorted (append (Cons y ys) (Cons x (append (Cons y ys) zs)))
--   ==. sorted (Cons y (append ys (Cons x (append (Cons y ys) zs))))
--   ==. ( all (leq y) (append ys (Cons x (append (Cons y ys) zs)))
--           && sorted (append ys (Cons x (append (Cons y ys) zs)))
--       )
--   ==. ( all (leq y) (append ys (Cons x (append (Cons y ys) zs)))
--           && sorted ys
--           && sorted (append (Cons y ys) zs)
--           && all (geq x) ys
--           && all (leq x) (append (Cons y ys) zs)
--       )
--   ==. (sorted (Cons y ys) && sorted zs && all (geq x) (Cons y ys) && all (leq x) zs)
--   *** QED

-- Using this permute function yields insertionsort.
-- However, we can derive quicksort with the next permute function.
permute_insertionsort :: Plus m -> List Elem -> m (List Elem)
permute_insertionsort pls Nil = pure mnd Nil
  where
    mnd = monad pls
permute_insertionsort pls (Cons x xs) = permute pls xs >>= insert pls x
  where
    (>>=) = bind mnd
    mnd = monad pls

-- The insert function for insertionsort.
insert :: Plus m -> Elem -> List Elem -> m (List Elem)
insert pls x xs = undefined

-- TODO: prove termination
{-@ lazy permute @-}
permute :: Plus m -> List a -> m (List a)
permute pls Nil = pure mnd Nil
  where
    mnd = monad pls
permute pls (Cons x xs) =
  split pls xs >>= \(ys, zs) ->
    (liftM2 mnd)
      (\ys zs -> ys `append` Cons x Nil `append` zs)
      (permute pls ys)
      (permute pls zs)
  where
    (>>=) = bind mnd
    mnd = monad pls

split :: Plus m -> List a -> m (List a, List a)
split pls Nil = pure mnd (Nil, Nil)
  where
    mnd = monad pls
split pls (Cons x xs) = split pls xs >>= \(ys, zs) -> pure mnd (Cons x ys, zs) <+> pure mnd (ys, Cons x zs)
  where
    (<+>) = plus pls
    (>>=) = bind mnd
    mnd = monad pls
