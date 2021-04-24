{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Sort.Array where

import Control.Refined.Monad
import Control.Refined.Monad.Array
import Control.Refined.Monad.Plus
import Data.Refined.Bool
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Tuple
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Sort.List
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (*), (+), (++), (>>), (>>=))

{-
## Functions. `ipartl` and relatives

-}

{-@ reflect partl' @-}
partl' :: Array m Elem -> Plus m -> Elem -> (List Elem, List Elem, List Elem) -> m (List Elem, List Elem)
partl' ary pls p (ys, zs, Nil) = pure mnd (ys, zs)
  where
    mnd = arrayMonad ary
partl' ary pls p (ys, zs, Cons x xs) = dispatch ary pls x p (ys, zs, xs) >>= partl' ary pls p
  where
    (>>=) = bind mnd
    mnd = arrayMonad ary

{-@ reflect dispatch @-}
dispatch :: Array m Elem -> Plus m -> Elem -> Elem -> (List Elem, List Elem, List Elem) -> m (List Elem, List Elem, List Elem)
dispatch ary pls x p (ys, zs, xs) =
  if leq x p
    then permute pls zs >>= apply (\zs' -> pure mnd (ys ++ Cons x Nil, zs', xs))
    else permute pls (zs ++ Cons x Nil) >>= apply (\zs' -> pure mnd (ys, zs', xs))
  where
    (>>=) = bind mnd
    mnd = arrayMonad ary

-- final derivation of `ipartl`
{-@ reflect ipartl @-}
ipartl :: forall m. Array m Elem -> Plus m -> Elem -> Index -> (Natural, Natural, Natural) -> m (Natural, Natural)
ipartl ary pls p i (ny, nz, Z) = pure mnd (ny, nz)
  where
    mnd = arrayMonad ary
ipartl ary pls p i (ny, nz, S k) =
  read ary (i + ny + nz)
    >>= apply
      ( \x ->
          if leq x p
            then swap ary (i + ny) (i + ny + nz) >> ipartl ary pls p i (S ny, nz, k)
            else ipartl ary pls p i (ny, S nz, k)
      )
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = arrayMonad ary

{-
## Theorem. `ipartl_spec`

-}

{-@ reflect ipartl_spec_aux1 @-}
ipartl_spec_aux1 :: Array m Elem -> Plus m -> Elem -> Index -> List Elem -> List Elem -> List Elem -> m (Natural, Natural)
ipartl_spec_aux1 ary pls p i xs ys zs = writeList ary i (ys ++ zs ++ xs) >> ipartl ary pls p i (length ys, length zs, length xs)
  where
    (>>) = seq mnd
    mnd = arrayMonad ary

{-@ reflect ipartl_spec_aux2 @-}
ipartl_spec_aux2 :: Array m Elem -> Plus m -> Elem -> Index -> List Elem -> List Elem -> List Elem -> m (Natural, Natural)
ipartl_spec_aux2 ary pls p i xs ys zs = partl' ary pls p (ys, zs, xs) >>= writeListToLength2 ary i
  where
    (>>=) = bind mnd
    mnd = arrayMonad ary

-- [ref] display 10
{-@
ipartl_spec ::
  forall m.
  Equality (m (Natural, Natural)) =>
  Monad m ->
  ary:Array m Elem ->
  pls:Plus m ->
  p:Elem ->
  i:Index ->
  xs:List Elem ->
  ys:List Elem ->
  zs:List Elem ->
  RefinesPlus m (Natural, Natural) {pls}
    {ipartl_spec_aux1 ary pls p i xs ys zs}
    {ipartl_spec_aux2 ary pls p i xs ys zs}
@-}
ipartl_spec :: forall m. Equality (m (Natural, Natural)) => Monad m -> Array m Elem -> Plus m -> Elem -> Index -> List Elem -> List Elem -> List Elem -> EqualityProp (m (Natural, Natural))
ipartl_spec mnd ary pls p i xs ys zs =
  [eqpropchain|
      (writeList ary i (ys ++ zs ++ xs) >> ipartl ary pls p i (length ys, length zs, length xs))
        <+> (partl' ary pls p (ys, zs, xs) >>= writeListToLength2 ary i)
    %==
      partl' ary pls p (ys, zs, xs) >>= writeListToLength2 ary i
        %by undefined 
  |]
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    mnd = arrayMonad ary

{-@ reflect ipartl_spec_lemma_aux1 @-}
ipartl_spec_lemma_aux1 :: Array m Elem -> Plus m -> Index -> Elem -> List Elem -> m ()
ipartl_spec_lemma_aux1 ary pls i x zs =
  writeList ary i (zs ++ Cons x Nil) >> swap ary i (i + length zs)
  where
    (>>) = seq mnd
    mnd = arrayMonad ary

{-@ reflect ipartl_spec_lemma_aux2 @-}
ipartl_spec_lemma_aux2 :: Array m Elem -> Plus m -> Index -> Elem -> List Elem -> m ()
ipartl_spec_lemma_aux2 ary pls i x zs =
  permute pls zs >>= apply (\zs' -> writeList ary i (Cons x Nil ++ zs'))
  where
    (>>=) = bind mnd
    mnd = arrayMonad ary

-- [ref] display 11
-- TODO: do they give a proof of this somewhere?
{-@
ipartl_spec_lemma ::
  forall m.
  Equality (m ()) =>
  Monad m ->
  ary:Array m Elem ->
  pls:Plus m ->
  i:Index ->
  x:Elem ->
  zs:List Elem ->
  RefinesPlus m () {pls}
    {ipartl_spec_lemma_aux1 ary pls i x zs}
    {ipartl_spec_lemma_aux2 ary pls i x zs}
@-}
ipartl_spec_lemma :: forall m. Equality (m ()) => Monad m -> Array m Elem -> Plus m -> Index -> Elem -> List Elem -> EqualityProp (m ())
ipartl_spec_lemma _ ary pls i x zs =
  [eqpropchain|
      (writeList ary i (zs ++ Cons x Nil) >> swap ary i (i + length zs))
        <+> (permute pls zs >>= apply (\zs' -> writeList ary i (Cons x Nil ++ zs')))
    %==
      permute pls zs >>= apply (\zs' -> writeList ary i (Cons x Nil ++ zs'))
        %by undefined -- TODO 
  |]
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    mnd = arrayMonad ary

{-
## Functions. `iqsort` and relatives

-}

-- `iqsort i n` sorts the `n` elements in the array starting from index `i`.
-- TODO: need to prove termination?
{-@ lazy iqsort @-}
{-@ reflect iqsort @-}
iqsort :: forall m. Array m Elem -> Plus m -> Index -> Natural -> m ()
iqsort ary pls i Z = pure mnd ()
  where
    mnd = arrayMonad ary
iqsort ary pls i (S n) =
  read ary i
    >>= apply
      ( \p ->
          ipartl ary pls p (S i) (Z, Z, n)
            >>= apply
              ( \(ny, nz) ->
                  swap ary i (i + ny)
                    >> iqsort ary pls i ny
                    >> iqsort ary pls (S (i + ny)) nz
              )
      )
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = arrayMonad ary
