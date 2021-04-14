{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Sort.ArrayProto where

import Control.Refined.Monad
import Control.Refined.Monad.Array hiding (monad)
import qualified Control.Refined.Monad.Array as Array (monad)
import Control.Refined.Monad.ArrayPlus
import Control.Refined.Monad.Plus hiding (monad)
import qualified Control.Refined.Monad.Plus as Plus (monad)
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
import Sort.Array
import Sort.List
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (*), (+), (++), (>>), (>>=))

{-@
permute_kleisli_permute_lemma ::
  forall m.
  Equality (m (List Elem)) =>
  Monad m ->
  pls:Plus m ->
  xs:List Elem ->
  EqualProp (m (List Elem))
    {bind (Plus.monad pls) (permute pls xs) (permute pls)}
    {permute pls xs}
@-}
permute_kleisli_permute_lemma :: forall m. Equality (m (List Elem)) => Monad m -> Plus m -> List Elem -> EqualityProp (m (List Elem))
permute_kleisli_permute_lemma _ pls Nil =
  [eqpropchain|
      permute pls Nil >>= permute pls
    %==
      pure mnd Nil >>= permute pls
    %==
      permute pls Nil
        %-- TODO: bind_identity_left mnd Nil (permute pls) 
        %by undefined
  |]
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>=>) :: forall a b c. (a -> m b) -> (b -> m c) -> (a -> m c)
    (>=>) = kleisli mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    mnd = Plus.monad pls
permute_kleisli_permute_lemma _ pls (Cons x xs) =
  [eqpropchain|
      permute pls (Cons x xs) >>= permute pls
    %==
      split pls xs
        >>= (apply (\(ys, zs) -> (liftM2 mnd) (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs')) (permute pls ys) (permute pls zs)))
          >>= permute pls
    %==
      split pls xs
        >>= (apply (\(ys, zs) -> (permute pls ys) >>= (apply (\ys' -> (permute pls zs) >>= (apply (\zs' -> pure mnd (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs') ys' zs')))))))
          >>= permute pls
        %by %rewrite apply (\(ys, zs) -> (liftM2 mnd) (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs')) (permute pls ys) (permute pls zs))
                 %to apply (\(ys, zs) -> (permute pls ys) >>= (apply (\ys' -> (permute pls zs) >>= (apply (\zs' -> pure mnd (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs') ys' zs'))))))
        %-- %by %extend (ys, zs) -- TODO: why does this break it? even with `%by undefined` after
        %by undefined 
    %==
      permute pls (Cons x xs)
        %by undefined
  |]
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>=>) :: forall a b c. (a -> m b) -> (b -> m c) -> (a -> m c)
    (>=>) = kleisli mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    mnd = Plus.monad pls

{-@
permute_kleisli_permute ::
  forall m.
  Equality (List Elem -> m (List Elem)) =>
  Monad m ->
  pls:Plus m ->
  EqualProp (List Elem -> m (List Elem))
    {kleisli (Plus.monad pls) (permute pls) (permute pls)}
    {permute pls}
@-}
permute_kleisli_permute :: forall m. Equality (List Elem -> m (List Elem)) => Monad m -> Plus m -> EqualityProp (List Elem -> m (List Elem))
permute_kleisli_permute _ pls =
  [eqpropchain|

      permute pls >=> permute pls

    %==

      apply (\xs -> permute pls xs >>= permute pls)

    %==

      permute pls 
        %by undefined
  
  |]
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>=>) :: forall a b c. (a -> m b) -> (b -> m c) -> (a -> m c)
    (>=>) = kleisli mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    mnd = Plus.monad pls

-- {-@
-- permute_kleisli_slowsort ::
--   EqualProp (m (List Elem))
--     {kleisli mnd (permute pls) (slowsort pls)}
--     {slowsort}
-- @-}

-- [ref] display 12
{-@
iqsort_spec ::
  forall m.
  Equality (m ()) =>
  Monad m ->
  Array m Elem ->
  Plus m ->
  arp:ArrayPlus m Elem ->
  i:Index ->
  xs:List Elem ->
  RefinesPlus m () {plusm arp}
    {iqsort_spec_aux1 arp i xs}
    {iqsort_spec_aux2 arp i xs}
@-}
iqsort_spec :: forall m. Equality (m ()) => Monad m -> Array m Elem -> Plus m -> ArrayPlus m Elem -> Index -> List Elem -> EqualityProp (m ())
iqsort_spec _ _ _ arp i Nil = undefined
iqsort_spec _ _ _ arp i (Cons p xs) =
  [eqpropchain|
      (writeList ary i (Cons p xs) >> iqsort arp i (length (Cons p xs)))
        <+> (slowsort pls (Cons p xs) >>= writeList ary i)

    %==

      partl' arp p (Nil, Nil, (Cons p xs))
        >>= apply
          ( \(ys, zs) ->
              permute pls ys
                >>= apply
                  ( \ys' ->
                      writeList ary i (ys' ++ Cons p Nil ++ zs)
                        >> iqsort arp i (length ys)
                        >> iqsort arp (S (i + length ys)) (length zs)
                  )
          )
        %by undefined

    %==

      slowsort pls (Cons p xs) >>= writeList ary i
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
