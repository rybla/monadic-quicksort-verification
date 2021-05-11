{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Sort.ArrayProto where

import Data.Refined.Bool
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Tuple
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.TH.Syntax
import Placeholder.M
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Sort.List
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (*), (+), (++), (>>), (>>=))
import Sort.Array 

{-@
permute_kleisli_permute_lemma ::
  forall m.
  Equality (m (List Elem)) =>
  Monad m ->
  pls:Plus m ->
  xs:List Elem ->
  EqualProp (m (List Elem))
    {bind (plusMonad pls) (permute pls xs) (permute pls)}
    {permute pls xs}
@-}
permute_kleisli_permute_lemma :: forall m. Equality (m (List Elem)) => Monad m -> Plus m -> List Elem -> EqualityProp (m (List Elem))
permute_kleisli_permute_lemma _ pls Nil = 
  -- TODO: solver fail
  [eqpropchain|
      %-- permute pls Nil >>= permute pls
      bind (plusMonad pls) (permute pls Nil) (permute pls)
    %==
      %-- permute pls Nil
      permute pls Nil
        %by undefined
        %-- TODO: pure_bind mnd Nil (permute pls) 
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
    mnd = plusMonad pls
permute_kleisli_permute_lemma _ pls (Cons x xs) = undefined
  -- TODO: solver fail
  -- [eqpropchain|
  --     permute pls (Cons x xs)
  --       >>= permute pls
  --   %==
  --     split pls xs
  --       >>= apply (\(ys, zs) -> liftM2 mnd (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs')) (permute pls ys) (permute pls zs))
  --         >>= permute pls
  --   %==
  --     split pls xs
  --       >>= apply (\(ys, zs) -> permute pls ys >>= apply (\ys' -> permute pls zs >>= apply (\zs' -> pure mnd (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs') ys' zs'))))
  --         >>= permute pls
  --       %by %rewrite apply (\(ys, zs) -> liftM2 mnd (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs')) (permute pls ys) (permute pls zs))
  --                %to apply (\(ys, zs) -> permute pls ys >>= apply (\ys' -> permute pls zs >>= apply (\zs' -> pure mnd (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs') ys' zs'))))
  --       %-- %by %extend (ys, zs) -- TODO: why does this break it? even with `%by undefined` after
  --       %by undefined 
  --   %==
  --     permute pls (Cons x xs)
  --       %by undefined
  -- |]
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>=>) :: forall a b c. (a -> m b) -> (b -> m c) -> (a -> m c)
    (>=>) = kleisli mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    mnd = plusMonad pls

{-@
permute_kleisli_permute ::
  forall m.
  (Equality (List Elem -> m (List Elem)), Equality (m (List Elem))) =>
  Monad m ->
  pls:Plus m ->
  EqualProp (List Elem -> m (List Elem))
    {kleisli (plusMonad pls) (permute pls) (permute pls)}
    {permute pls}
@-}
permute_kleisli_permute :: forall m. (Equality (List Elem -> m (List Elem)), Equality (m (List Elem))) => Monad m -> Plus m -> EqualityProp (List Elem -> m (List Elem))
permute_kleisli_permute _ pls = undefined
  -- TODO: solver fail
  -- [eqpropchain|
  --     permute pls >=> permute pls
  --   %==
  --     apply (\xs -> permute pls xs >>= permute pls)
  --   %==
  --     apply (\xs -> permute pls xs)
  --       %-- TODO: why not?
  --       %-- %by %extend xs
  --       %-- permute_kleisli_permute_lemma mnd pls xs
  --       %by undefined 
  --   %==
  --     permute pls 
  --       %by %extend xs
  --       %by undefined
  -- |]
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>=>) :: forall a b c. (a -> m b) -> (b -> m c) -> (a -> m c)
    (>=>) = kleisli mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    mnd = plusMonad pls

{-@
permute_kleisli_slowsort ::
  forall m.
  Equality (m (List Elem)) =>
  Monad m ->
  pls:Plus m ->
  xs:List Elem ->
  EqualProp (m (List Elem))
    {kleisli (plusMonad pls) (permute pls) (slowsort pls) xs}
    {slowsort pls xs}
@-}
permute_kleisli_slowsort :: forall m. Equality (m (List Elem)) => Monad m -> Plus m -> List Elem -> EqualityProp (m (List Elem))
permute_kleisli_slowsort _ pls xs =
  [eqpropchain|
      (permute pls >=> slowsort pls) xs 
    %==
      (permute pls >=> (permute pls >=> guardBy pls sorted)) xs
    %==
      slowsort pls xs
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
    mnd = plusMonad pls

{-
## Theorem. `iqsort_spec`
-}

{-@ reflect iqsort_spec_aux1 @-}
iqsort_spec_aux1 :: Array m Elem -> Plus m -> Index -> List Elem -> m ()
iqsort_spec_aux1 ary pls i xs = writeList ary i xs >> iqsort ary pls i (length xs)
  where
    (>>) = seq mnd
    mnd = arrayMonad ary

{-@ reflect iqsort_spec_aux2 @-}
iqsort_spec_aux2 :: Array m Elem -> Plus m -> Index -> List Elem -> m ()
iqsort_spec_aux2 ary pls i xs = slowsort pls xs >>= writeList ary i
  where
    (>>=) = bind mnd
    mnd = arrayMonad ary

-- main theorem
-- [ref] display 12
{-@
iqsort_spec ::
  forall m.
  Equality (m ()) =>
  Monad m ->
  ary:Array m Elem ->
  pls:Plus m ->
  i:Index ->
  xs:List Elem ->
  RefinesPlus m () {pls}
    {iqsort_spec_aux1 ary pls i xs}
    {iqsort_spec_aux2 ary pls i xs}
@-}
iqsort_spec :: forall m. Equality (m ()) => Monad m -> Array m Elem -> Plus m -> Index -> List Elem -> EqualityProp (m ())
iqsort_spec _ ary pls i Nil = undefined
iqsort_spec _ ary pls i (Cons p xs) =
  [eqpropchain|
      (writeList ary i (Cons p xs) >> iqsort ary pls i (length (Cons p xs)))
        <+> (slowsort pls (Cons p xs) >>= writeList ary i)

    %==

      partl' ary pls p (Nil, Nil, (Cons p xs))
        >>= apply
          ( \(ys, zs) ->
              permute pls ys
                >>= apply
                  ( \ys' ->
                      writeList ary i (ys' ++ Cons p Nil ++ zs)
                        >> iqsort ary pls i (length ys)
                        >> iqsort ary pls (S (i + length ys)) (length zs)
                  )
          )
        %by undefined -- TODO: prove

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
    mnd = plusMonad pls
