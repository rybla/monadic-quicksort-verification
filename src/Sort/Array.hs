{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Sort.Array where

import Control.Refined.Monad
import Control.Refined.Monad.Array hiding (monad)
import Control.Refined.Monad.ArrayPlus
import Control.Refined.Monad.Plus hiding (monad)
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
partl' :: ArrayPlus m Elem -> Elem -> (List Elem, List Elem, List Elem) -> m (List Elem, List Elem)
partl' arp p (ys, zs, Nil) = pure mnd (ys, zs)
  where
    mnd = monad arp
partl' arp p (ys, zs, Cons x xs) = dispatch arp x p (ys, zs, xs) >>= partl' arp p
  where
    (>>=) = bind mnd
    mnd = monad arp

{-@ reflect dispatch @-}
dispatch :: ArrayPlus m Elem -> Elem -> Elem -> (List Elem, List Elem, List Elem) -> m (List Elem, List Elem, List Elem)
dispatch arp x p (ys, zs, xs) =
  if leq x p
    then permute pls zs >>= apply (\zs' -> pure mnd (ys ++ Cons x Nil, zs', xs))
    else permute pls (zs ++ Cons x Nil) >>= apply (\zs' -> pure mnd (ys, zs', xs))
  where
    (>>=) = bind mnd
    arr = array arp
    pls = plusm arp
    mnd = monad arp

-- final derivation of `ipartl`
{-@ reflect ipartl @-}
ipartl :: forall m. ArrayPlus m Elem -> Elem -> Index -> (Natural, Natural, Natural) -> m (Natural, Natural)
ipartl arp p i (ny, nz, Z) = pure mnd (ny, nz)
  where
    mnd = monad arp
ipartl arp p i (ny, nz, S k) =
  read arr (i + ny + nz)
    >>= apply
      ( \x ->
          if leq x p
            then swap arr (i + ny) (i + ny + nz) >> ipartl arp p i (S ny, nz, k)
            else ipartl arp p i (ny, S nz, k)
      )
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    arr = array arp
    pls = plusm arp
    mnd = monad arp

{-
## Theorem. `ipartl_spec`

-}

{-@ reflect ipartl_spec_aux1 @-}
ipartl_spec_aux1 :: ArrayPlus m Elem -> Elem -> Index -> List Elem -> List Elem -> List Elem -> m (Natural, Natural)
ipartl_spec_aux1 arp p i xs ys zs = writeList arr i (ys ++ zs ++ xs) >> ipartl arp p i (length ys, length zs, length xs)
  where
    (>>) = seq mnd
    arr = array arp
    mnd = monad arp

{-@ reflect ipartl_spec_aux2 @-}
ipartl_spec_aux2 :: ArrayPlus m Elem -> Elem -> Index -> List Elem -> List Elem -> List Elem -> m (Natural, Natural)
ipartl_spec_aux2 arp p i xs ys zs = partl' arp p (ys, zs, xs) >>= writeListToLength2 arr i
  where
    (>>=) = bind mnd
    arr = array arp
    pls = plusm arp
    mnd = monad arp

-- [ref] display 10
{-@
ipartl_spec ::
  forall m.
  Equality (m (Natural, Natural)) =>
  Monad m ->
  Array m Elem ->
  Plus m ->
  arp:ArrayPlus m Elem ->
  p:Elem ->
  i:Index ->
  xs:List Elem ->
  ys:List Elem ->
  zs:List Elem ->
  RefinesPlus m (Natural, Natural) {plusm arp}
    {ipartl_spec_aux1 arp p i xs ys zs}
    {ipartl_spec_aux2 arp p i xs ys zs}
@-}
ipartl_spec :: forall m. Equality (m (Natural, Natural)) => Monad m -> Array m Elem -> Plus m -> ArrayPlus m Elem -> Elem -> Index -> List Elem -> List Elem -> List Elem -> EqualityProp (m (Natural, Natural))
ipartl_spec mnd ary pls arp p i xs ys zs =
  [eqpropchain|
      (writeList ary i (ys ++ zs ++ xs) >> ipartl arp p i (length ys, length zs, length xs))
        <+> (partl' arp p (ys, zs, xs) >>= writeListToLength2 ary i)
    %==
      partl' arp p (ys, zs, xs) >>= writeListToLength2 ary i
        %by undefined 
  |]
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    ary = array arp
    pls = plusm arp
    mnd = monad arp

{-@ reflect ipartl_spec_lemma_aux1 @-}
ipartl_spec_lemma_aux1 :: ArrayPlus m Elem -> Index -> Elem -> List Elem -> m ()
ipartl_spec_lemma_aux1 arp i x zs =
  writeList ary i (zs ++ Cons x Nil) >> swap ary i (i + length zs)
  where
    (>>) = seq mnd
    ary = array arp
    mnd = monad arp

{-@ reflect ipartl_spec_lemma_aux2 @-}
ipartl_spec_lemma_aux2 :: ArrayPlus m Elem -> Index -> Elem -> List Elem -> m ()
ipartl_spec_lemma_aux2 arp i x zs =
  permute pls zs >>= apply (\zs' -> writeList ary i (Cons x Nil ++ zs'))
  where
    (>>=) = bind mnd
    ary = array arp
    pls = plusm arp
    mnd = monad arp

-- [ref] display 11
-- TODO: do they give a proof of this somewhere?
{-@
ipartl_spec_lemma ::
  forall m.
  Equality (m ()) =>
  Monad m ->
  Array m Elem ->
  Plus m ->
  arp:ArrayPlus m Elem ->
  i:Index ->
  x:Elem ->
  zs:List Elem ->
  RefinesPlus m () {plusm arp}
    {ipartl_spec_lemma_aux1 arp i x zs}
    {ipartl_spec_lemma_aux2 arp i x zs}
@-}
ipartl_spec_lemma :: forall m. Equality (m ()) => Monad m -> Array m Elem -> Plus m -> ArrayPlus m Elem -> Index -> Elem -> List Elem -> EqualityProp (m ())
ipartl_spec_lemma _ _ _ arp i x zs =
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
    ary = array arp
    pls = plusm arp
    mnd = monad arp

{-
## Functions. `iqsort` and relatives

-}

-- `iqsort i n` sorts the `n` elements in the array starting from index `i`.
-- TODO: need to prove termination?
{-@ lazy iqsort @-}
{-@ reflect iqsort @-}
iqsort :: forall m. ArrayPlus m Elem -> Index -> Natural -> m ()
iqsort arp i Z = pure mnd ()
  where
    mnd = monad arp
iqsort arp i (S n) =
  read ary i
    >>= apply
      ( \p ->
          ipartl arp p (S i) (Z, Z, n)
            >>= apply
              ( \(ny, nz) ->
                  swap ary i (i + ny)
                    >> iqsort arp i ny
                    >> iqsort arp (S (i + ny)) nz
              )
      )
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    ary = array arp
    pls = plusm arp
    mnd = monad arp

{-
## Theorem. `iqsort_spec`
-}

{-@ reflect iqsort_spec_aux1 @-}
iqsort_spec_aux1 :: ArrayPlus m Elem -> Index -> List Elem -> m ()
iqsort_spec_aux1 arp i xs = writeList ary i xs >> iqsort arp i (length xs)
  where
    (>>) = seq mnd
    ary = array arp
    mnd = monad arp

{-@ reflect iqsort_spec_aux2 @-}
iqsort_spec_aux2 :: ArrayPlus m Elem -> Index -> List Elem -> m ()
iqsort_spec_aux2 arp i xs = slowsort pls xs >>= writeList ary i
  where
    (>>=) = bind mnd
    pls = plusm arp
    ary = array arp
    mnd = monad arp
