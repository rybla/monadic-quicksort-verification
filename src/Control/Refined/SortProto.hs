{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Refined.SortProto where

import Control.Refined.Monad
import Control.Refined.Monad.Plus
import Control.Refined.Sort
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Prelude hiding (Monad, all, foldl, length, not, pure, read, readList, seq, (++), (>>), (>>=))

{-@ reflect divide_and_conquer_lemma2_aux @-}
divide_and_conquer_lemma2_aux :: forall m. Plus m -> Elem -> List Elem -> m (List Elem, List Elem)
divide_and_conquer_lemma2_aux pls x xs =
  split pls xs >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs))
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    mnd = monad pls

{-@
divide_and_conquer_lemma2 ::
  forall m.
  Equality (m (List Elem, List Elem)) =>
  Monad m ->
  pls:Plus m ->
  x:Elem ->
  xs:List Elem ->
  RefinesPlus m (List Elem, List Elem) {pls}
    {pure (monad pls) (partition x xs)}
    {divide_and_conquer_lemma2_aux pls x xs}
@-}
divide_and_conquer_lemma2 ::
  forall m.
  Equality (m (List Elem, List Elem)) =>
  Monad m ->
  Plus m ->
  Elem ->
  List Elem ->
  EqualityProp (m (List Elem, List Elem))
divide_and_conquer_lemma2 _ pls x Nil =
  [eqpropchain|

      pure mnd (partition x Nil) <+> divide_and_conquer_lemma2_aux pls x Nil

    %eqprop 

      pure mnd (partition x Nil) <+> (split pls Nil >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)))
        %by undefined
        {-
        -- TODO: not sure of issues 
        %by %rewrite divide_and_conquer_lemma2_aux pls x Nil
                 %to split pls Nil >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs))
        %by %reflexivity
        -}

    %eqprop 

      pure mnd (Nil, Nil) <+> (split pls Nil >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)))

    %eqprop

      pure mnd (Nil, Nil) <+> (pure mnd (Nil, Nil) >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)))

    %eqprop

      pure mnd (Nil, Nil) <+> (guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)) (Nil, Nil))
        
        %by %rewrite pure mnd (Nil, Nil) >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs))
                 %to guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)) (Nil, Nil)
        
        %by bind_identity_left mnd (Nil, Nil) (guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)))

    %eqprop 

      pure mnd (Nil, Nil) <+> (guard pls (all (leq x) Nil && all (geq x) Nil) >> pure mnd (Nil, Nil))

    %eqprop 

      pure mnd (Nil, Nil) <+> (guard pls True >> pure mnd (Nil, Nil))

    %eqprop 

      pure mnd (Nil, Nil) <+> (pure mnd () >> pure mnd (Nil, Nil))

    %eqprop 

      pure mnd (Nil, Nil) <+> pure mnd (Nil, Nil)

        %by %rewrite pure mnd () >> pure mnd (Nil, Nil)
                 %to pure mnd (Nil, Nil)

        %by seq_identity_left mnd () (pure mnd (Nil, Nil))

    %eqprop 

      pure mnd (Nil, Nil) <+> pure mnd (Nil, Nil)

    %eqprop 

      pure mnd (Nil, Nil)

        %by refinesplus_reflexivity pls (pure mnd (Nil, Nil))

    %eqprop 

      pure mnd (Nil, Nil) >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs))

        %by undefined

    %eqprop 
      
      split pls Nil >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs))

    %eqprop

      divide_and_conquer_lemma2_aux pls x Nil

  |]
  where
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = monad pls
divide_and_conquer_lemma2 _ pls x (Cons x' xs) =
  [eqpropchain|
      pure (monad pls) (partition x (Cons x' xs)) <+> divide_and_conquer_lemma2_aux pls x (Cons x' xs)
    %eqprop 
      pure (monad pls) (partition x (Cons x' xs)) <+> (split pls (Cons x' xs) >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)))
    %eqprop
      divide_and_conquer_lemma2_aux pls x (Cons x' xs)
        %by undefined 
  |]
  where
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = monad pls
