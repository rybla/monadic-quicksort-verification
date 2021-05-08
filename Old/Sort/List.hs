{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Sort.List where

import Control.Refined.Monad
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
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (++), (>>), (>>=))

{-@ reflect leq @-}
leq :: Elem -> Elem -> Bool
leq x y = x <= y

{-@ reflect geq @-}
geq :: Elem -> Elem -> Bool
geq x y = y <= x

--
{-@ reflect slowsort @-}
slowsort :: Plus m -> List Elem -> m (List Elem)
slowsort pls = permute pls >=> guardBy pls sorted
  where
    (>=>) = kleisli mnd
    mnd = plusMonad pls

--
{-@ reflect sorted @-}
sorted :: List Elem -> Bool
sorted Nil = True
sorted (Cons x xs) = all (leq x) xs && sorted xs

-- [ref] display 5
{-@ automatic-instances sorted_middle @-}
{-@
sorted_middle ::
  ys:List Elem ->
  x:Elem ->
  zs:List Elem ->
  {sorted (append ys (append (Cons x Nil) zs)) <=>
   sorted ys && sorted zs && all (geq x) ys && all (leq x) zs}
@-}
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
    mnd = plusMonad pls
permute_insertionsort pls (Cons x xs) = permute pls xs >>= insert pls x
  where
    (>>=) = bind mnd
    mnd = plusMonad pls

-- The insert function for insertionsort.
insert :: Plus m -> Elem -> List Elem -> m (List Elem)
insert pls x xs = undefined

-- TODO: prove termination
{-@ lazy permute @-}
{-@ reflect permute @-}
permute :: Plus m -> List a -> m (List a)
permute pls Nil = pure mnd Nil
  where
    mnd = plusMonad pls
permute pls (Cons x xs) =
  split pls xs
    >>= apply
      ( \(ys, zs) ->
          (liftM2 mnd)
            (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs'))
            (permute pls ys)
            (permute pls zs)
      )
  where
    (>>=) = bind mnd
    mnd = plusMonad pls

{-@ reflect split @-}
split :: Plus m -> List a -> m (List a, List a)
split pls Nil = pure mnd (Nil, Nil)
  where
    mnd = plusMonad pls
split pls (Cons x xs) =
  split pls xs
    >>= apply
      ( \(ys, zs) ->
          pure mnd (Cons x ys, zs) <+> pure mnd (ys, Cons x zs)
      )
  where
    (<+>) = plus pls
    (>>=) = bind mnd
    mnd = plusMonad pls

-- [ref] divide and conquer equation chain
{-@ reflect divide_and_conquer_lemma1_aux @-}
divide_and_conquer_lemma1_aux ::
  forall m.
  Plus m ->
  Elem ->
  List Elem ->
  m (List Elem)
divide_and_conquer_lemma1_aux pls x xs =
  split pls xs
    >>= apply
      ( \(ys, zs) ->
          guard pls (all (leq x) ys && all (geq x) zs)
            >> (permute pls ys >>= guardBy pls sorted)
              >>= apply
                ( \ys' ->
                    (permute pls zs >>= guardBy pls sorted)
                      >>= apply
                        ( \zs' ->
                            pure mnd (ys' ++ Cons x Nil ++ zs')
                        )
                )
      )
  where
    -- ! turns out i need the type annotation in order to use infix notation
    -- ! otherwise, assumes specific a and b
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = plusMonad pls

{-@
divide_and_conquer_lemma1 ::
  forall m.
  Equality (m (List Elem)) =>
  Monad m ->
  pls:Plus m ->
  x:Elem ->
  xs:List Elem ->
  EqualProp (m (List Elem))
    {slowsort pls (Cons x xs)}
    {divide_and_conquer_lemma1_aux pls x xs}
@-}
divide_and_conquer_lemma1 ::
  forall m.
  Equality (m (List Elem)) =>
  Monad m ->
  Plus m ->
  Elem ->
  List Elem ->
  EqualityProp (m (List Elem))
divide_and_conquer_lemma1 _ pls x xs =
  [eqpropchain|

      slowsort pls (Cons x xs)
  
    %==
  
      (permute pls >=> guardBy pls sorted) (Cons x xs)
  
    %==
  
      (apply (\x -> permute pls x >>= guardBy pls sorted)) (Cons x xs)
        %by %rewrite permute pls >=> guardBy pls sorted
                 %to apply (\x -> permute pls x >>= guardBy pls sorted)
        %by undefined -- TODO: def (>=>)
  
    %==
  
      permute pls (Cons x xs) >>= guardBy pls sorted
  
    %==
  
      (split pls xs >>= apply (\(ys, zs) -> (liftM2 mnd) (\ys' zs' -> ys' ++ Cons x Nil ++ zs') (permute pls ys) (permute pls zs)))
        >>= guardBy pls sorted
  
    %==
  
      (split pls xs >>= apply (\(ys, zs) -> permute pls ys >>= apply (\ys' -> permute pls zs >>= apply (\zs' -> pure mnd (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs') ys' zs')))))
          >>= guardBy pls sorted
  
    %==
  
      (split pls xs
        >>= apply (\(ys, zs) -> permute pls ys 
          >>= apply (\ys' -> permute pls zs
            >>= apply (\zs' -> pure mnd (ys' ++ Cons x Nil ++ zs')))))
        >>= guardBy pls sorted
  
    %==
  
      split pls xs
        >>= apply (\(ys, zs) -> permute pls ys 
          >>= apply (\ys' -> permute pls zs
            >>= apply (\zs' -> pure mnd (ys' ++ Cons x Nil ++ zs')
              >>= guardBy pls sorted)))
        %by undefined -- TODO: several associativity steps
  
    %==
  
      split pls xs
        >>= apply (\(ys, zs) -> permute pls ys 
          >>= apply (\ys' -> permute pls zs
            >>= apply (\zs' -> 
              guardBy pls sorted (ys' ++ Cons x Nil ++ zs'))))
        %by undefined
        {-
        -- the following proof takes ~3min to check

        %by %rewrite apply (\(ys, zs) -> permute pls ys >>= apply (\ys' -> permute pls zs >>= apply (\zs' -> pure mnd (ys' ++ Cons x Nil ++ zs') >>= guardBy pls sorted)))
                 %to apply (\(ys, zs) -> permute pls ys >>= apply (\ys' -> permute pls zs >>= apply (\zs' ->  guardBy pls sorted (ys' ++ Cons x Nil ++ zs'))))
        %by %extend (ys, zs)
        %by %rewrite apply (\ys' -> permute pls zs >>= apply (\zs' -> pure mnd (ys' ++ Cons x Nil ++ zs') >>= guardBy pls sorted))
                 %to apply (\ys' -> permute pls zs >>= apply (\zs' -> guardBy pls sorted (ys' ++ Cons x Nil ++ zs')))
        %by %extend ys'
        %by %rewrite apply (\zs' -> pure mnd (ys' ++ Cons x Nil ++ zs') >>= guardBy pls sorted)
                 %to apply (\zs' -> guardBy pls sorted (ys' ++ Cons x Nil ++ zs'))
        %by %extend zs'
        %by %rewrite pure mnd (ys' ++ Cons x Nil ++ zs') >>= guardBy pls sorted
                 %to guardBy pls sorted (ys' ++ Cons x Nil ++ zs')
        %by bind_identity_left mnd (ys' ++ Cons x Nil ++ zs') (guardBy pls sorted)
        -}
  
    %==
  
      split pls xs
        >>= apply (\(ys, zs) -> permute pls ys 
          >>= apply (\ys' -> permute pls zs
            >>= apply (\zs' -> 
              guard pls (sorted (ys' ++ Cons x Nil ++ zs'))
                >> pure mnd (ys' ++ Cons x Nil ++ zs'))))
        %by undefined
        {-
        -- the following proof takes ~3min to check 

        %by %rewrite apply (\(ys, zs) -> permute pls ys >>= apply (\ys' -> permute pls zs >>= apply (\zs' -> guardBy pls sorted (ys' ++ Cons x Nil ++ zs'))))
                 %to apply (\(ys, zs) -> permute pls ys >>= apply (\ys' -> permute pls zs >>= apply (\zs' -> guard pls (sorted (ys' ++ Cons x Nil ++ zs')) >> pure mnd (ys' ++ Cons x Nil ++ zs'))))
        %by %extend (ys, zs) 
        %by %rewrite apply (\ys' -> permute pls zs >>= apply (\zs' -> guardBy pls sorted (ys' ++ Cons x Nil ++ zs')))
                 %to apply (\ys' -> permute pls zs >>= apply (\zs' -> guard pls (sorted (ys' ++ Cons x Nil ++ zs')) >> pure mnd (ys' ++ Cons x Nil ++ zs')))
        %by %extend ys' 
        %by %rewrite apply (\zs' -> guardBy pls sorted (ys' ++ Cons x Nil ++ zs'))
                 %to apply (\zs' -> guard pls (sorted (ys' ++ Cons x Nil ++ zs')) >> pure mnd (ys' ++ Cons x Nil ++ zs'))
        %by %extend zs' 
        %by %rewrite guardBy pls sorted (ys' ++ Cons x Nil ++ zs')
                 %to guard pls (sorted (ys' ++ Cons x Nil ++ zs')) >> pure mnd (ys' ++ Cons x Nil ++ zs')
        %by %reflexivity
        -}
  
    %==
  
      split pls xs
        >>= apply (\(ys, zs) -> permute pls ys 
          >>= apply (\ys' -> permute pls zs
            >>= apply (\zs' -> 
              guard pls (sorted ys' && sorted zs' && all (geq x) ys' && all (leq x) zs')
                >> pure mnd (ys' ++ Cons x Nil ++ zs'))))

        %by %rewrite apply (\(ys, zs) -> permute pls ys >>= apply (\ys' -> permute pls zs >>= apply (\zs' -> guard pls (sorted (ys' ++ Cons x Nil ++ zs')) >> pure mnd (ys' ++ Cons x Nil ++ zs'))))
                 %to apply (\(ys, zs) -> permute pls ys >>= apply (\ys' -> permute pls zs >>= apply (\zs' -> guard pls (sorted ys' && sorted zs' && all (geq x) ys' && all (leq x) zs') >> pure mnd (ys' ++ Cons x Nil ++ zs'))))
        %by %extend (ys, zs) 
        %by %rewrite apply (\ys' -> permute pls zs >>= apply (\zs' -> guard pls (sorted (ys' ++ Cons x Nil ++ zs')) >> pure mnd (ys' ++ Cons x Nil ++ zs')))
                 %to apply (\ys' -> permute pls zs >>= apply (\zs' -> guard pls (sorted ys' && sorted zs' && all (geq x) ys' && all (leq x) zs') >> pure mnd (ys' ++ Cons x Nil ++ zs')))
        %by %extend ys' 
        %by %rewrite apply (\zs' -> guard pls (sorted (ys' ++ Cons x Nil ++ zs')) >> pure mnd (ys' ++ Cons x Nil ++ zs'))
                 %to apply (\zs' -> guard pls (sorted ys' && sorted zs' && all (geq x) ys' && all (leq x) zs') >> pure mnd (ys' ++ Cons x Nil ++ zs'))
        %by %extend zs'
        %by %rewrite sorted (ys' ++ Cons x Nil ++ zs')
                 %to sorted ys' && sorted zs' && all (geq x) ys' && all (leq x) zs'
        %by %smt
        %by sorted_middle ys' x zs'
  
    %==

      split pls xs
        >>= apply (\(ys, zs) -> permute pls ys 
          >>= apply (\ys' -> permute pls zs
            >>= apply (\zs' -> 
              (guard pls (sorted ys') >> guard pls (sorted zs') >> guard pls (all (geq x) ys' && all (leq x) zs'))
                >> pure mnd (ys' ++ Cons x Nil ++ zs'))))
        %by undefined -- TODO: several guard_and steps 

    %==

      split pls xs
        >>= apply (\(ys, zs) -> permute pls ys 
          >>= apply (\ys' -> permute pls zs
            >>= apply (\zs' -> 
              guard pls (all (geq x) ys' && all (leq x) zs')
                >> guard pls (sorted ys')
                >> guard pls (sorted zs')
                >> pure mnd (ys' ++ Cons x Nil ++ zs'))))
        %by undefined  -- TODO: rearrange the sequences guards 

    %==      

      split pls xs
        >>= apply (\(ys, zs) -> guard pls (all (leq x) ys && all (geq x) zs)
          >> (permute pls ys >>= guardBy pls sorted)
            >>= apply (\ys' -> apply permute pls zs
              >>= guardBy pls sorted
                >>= apply (\zs' -> pure mnd (ys' ++ Cons x Nil ++ zs'))))
        %by undefined -- TODO

    %==

      divide_and_conquer_lemma1_aux pls x xs 
  |]
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>=>) :: forall a b c. (a -> m b) -> (b -> m c) -> (a -> m c)
    (>=>) = kleisli mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = plusMonad pls

{-@ reflect divide_and_conquer_aux @-}
divide_and_conquer_aux :: forall m. Plus m -> Elem -> List Elem -> m (List Elem)
divide_and_conquer_aux pls x xs =
  pure mnd (partition x xs)
    >>= apply
      ( \(ys, zs) ->
          slowsort pls ys
            >>= apply
              ( \ys' ->
                  slowsort pls zs
                    >>= apply
                      ( \zs' ->
                          pure mnd (ys' ++ Cons x Nil ++ zs')
                      )
              )
      )
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = plusMonad pls

-- [ref] display 8
{-@
divide_and_conquer ::
  Monad m ->
  pls:Plus m ->
  x:Elem ->
  xs:List Elem ->
  RefinesPlus m (List Elem, List Elem) {pls}
    {divide_and_conquer_aux pls x xs}
    {slowsort pls (Cons x xs)}
@-}
divide_and_conquer ::
  Monad m ->
  Plus m ->
  Elem ->
  List Elem ->
  EqualityProp (m (List Elem, List Elem))
divide_and_conquer = undefined

{-@ reflect partition @-}
partition :: Elem -> List Elem -> (List Elem, List Elem)
partition x' Nil = (Nil, Nil)
partition x' (Cons x xs) =
  if leq x x' then (Cons x ys, zs) else (ys, Cons x zs)
  where
    ys = proj1 (partition x' xs)
    zs = proj2 (partition x' xs)

{-@ reflect divide_and_conquer_lemma2_aux1 @-}
divide_and_conquer_lemma2_aux1 :: forall m. Plus m -> Elem -> List Elem -> m (List Elem, List Elem)
divide_and_conquer_lemma2_aux1 pls x xs =
  split pls xs >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs))
  where
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    mnd = plusMonad pls

{-@
divide_and_conquer_lemma2 ::
  forall m.
  Equality (m (List Elem, List Elem)) =>
  Monad m ->
  pls:Plus m ->
  x:Elem ->
  xs:List Elem ->
  RefinesPlus m (List Elem, List Elem) {pls}
    {pure (plusMonad pls) (partition x xs)}
    {divide_and_conquer_lemma2_aux1 pls x xs}
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

        pure mnd (partition x Nil) <+> divide_and_conquer_lemma2_aux1 pls x Nil

      %==

        pure mnd (partition x Nil) <+> (split pls Nil >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)))
          %by %rewrite divide_and_conquer_lemma2_aux1 pls x Nil
                   %to split pls Nil >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs))
          %by undefined -- TODO: why???

      %==

        pure mnd (Nil, Nil) <+> (split pls Nil >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)))

      %==

        pure mnd (Nil, Nil) <+> (pure mnd (Nil, Nil) >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)))

      %==

        pure mnd (Nil, Nil) <+> (guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)) (Nil, Nil))

          %by %rewrite pure mnd (Nil, Nil) >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs))
                   %to guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)) (Nil, Nil)

          %by bind_identity_left mnd (Nil, Nil) (guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)))

      %==

        pure mnd (Nil, Nil) <+> (guard pls (all (leq x) Nil && all (geq x) Nil) >> pure mnd (Nil, Nil))

      %==

        pure mnd (Nil, Nil) <+> (guard pls True >> pure mnd (Nil, Nil))

      %==

        pure mnd (Nil, Nil) <+> (pure mnd () >> pure mnd (Nil, Nil))

      %==

        pure mnd (Nil, Nil) <+> pure mnd (Nil, Nil)

          %by %rewrite pure mnd () >> pure mnd (Nil, Nil)
                   %to pure mnd (Nil, Nil)

          %by seq_identity_left mnd () (pure mnd (Nil, Nil))

      %==

        pure mnd (Nil, Nil) <+> pure mnd (Nil, Nil)

      %==

        guard pls True >> pure mnd (Nil, Nil)

      %==

        guard pls (all (leq x) Nil && all (geq x) Nil) >> pure mnd (Nil, Nil)

      %==

        guard pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs) (Nil, Nil)) >> pure mnd (Nil, Nil)

      %==

        guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)) (Nil, Nil)

      %==

        pure mnd (Nil, Nil) >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs))

          %by %symmetry
          %by bind_identity_left mnd (Nil, Nil) (guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs)))

      %==

        split pls Nil >>= guardBy pls (apply (\(ys, zs) -> all (leq x) ys && all (geq x) zs))

      %==

        divide_and_conquer_lemma2_aux1 pls x Nil

    |]
  where
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = plusMonad pls
{-
TODO: want to get something of the form

  pure mnd (partition x' xs)
    <+> (split pls xs >>= guardBy pls (apply (\(ys, zs) -> all (leq x') ys && all (geq x') zs)))

in order to use induction
-}
divide_and_conquer_lemma2 _ pls x' (Cons x xs) =
  [eqpropchain|

      pure mnd (partition x' (Cons x xs))
        <+> divide_and_conquer_lemma2_aux1 pls x' (Cons x xs)

    %== 

      pure mnd (partition x' (Cons x xs))
        <+> (split pls (Cons x xs) >>= guardBy pls (apply (\(ys', zs') -> all (leq x') ys' && all (geq x) zs')))

    %==

      (pure mnd (if leq x x' then (Cons x ys, zs) else (ys, Cons x zs)))
        <+> (split pls (Cons x xs) >>= guardBy pls (apply (\(ys', zs') -> all (leq x') ys' && all (geq x) zs')))

      %by %rewrite partition x' (Cons x xs)
               %to if leq x x' then (Cons x ys, zs) else (ys, Cons x zs)
      %by undefined -- TODO: why????

    %==

      (pure mnd (if leq x x' then (Cons x ys, zs) else (ys, Cons x zs)))
        <+> ((split pls xs >>= apply (\(ys, zs) -> pure mnd (Cons x ys, zs) <+> pure mnd (ys, Cons x zs)))
          >>= guardBy pls (apply (\(ys', zs') -> all (leq x') ys' && all (geq x) zs')))

    %==

      split pls (Cons x xs) >>= guardBy pls (apply (\(ys', zs') -> all (leq x') ys' && all (geq x) zs'))
        %by undefined -- TODO: some details missing here... need to use induction

    %==

      divide_and_conquer_lemma2_aux1 pls x' (Cons x xs)

  |]
  where
    ys = proj1 (partition x' xs)
    zs = proj2 (partition x' xs)
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = plusMonad pls

{-@ reflect quicksort @-}
quicksort :: List Elem -> List Elem
quicksort Nil = Nil
quicksort (Cons x xs) = quicksort ys ++ Cons x Nil ++ quicksort zs
  where
    ys = proj1 (partition x xs)
    zs = proj2 (partition x xs)

{-@
quicksort_refines_slowsort ::
  forall m.
  Equality (m (List Elem)) =>
  Monad m ->
  pls:Plus m ->
  xs:List Elem ->
  RefinesPlus m (List Elem) {pls}
    {apply (pure (plusMonad pls) . quicksort) xs}
    {slowsort pls xs}
@-}
quicksort_refines_slowsort ::
  forall m.
  Equality (m (List Elem)) =>
  Monad m ->
  Plus m ->
  List Elem ->
  EqualityProp (m (List Elem))
quicksort_refines_slowsort _ pls Nil =
  [eqpropchain|
      (pure mnd . quicksort) Nil <+> slowsort pls Nil
    %==
      pure mnd Nil <+> pure mnd Nil
    %==
      pure mnd Nil
        %by undefined -- TODO: refinesplus_reflexivity pls (pure mnd Nil)
    %==
      slowsort pls Nil
        %by undefined
  |]
  where
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = plusMonad pls
quicksort_refines_slowsort _ pls (Cons x xs) =
  [eqpropchain|
      (pure mnd . quicksort) (Cons x xs) 
        <+> slowsort pls (Cons x xs)
    %==
      pure mnd (quicksort ys ++ Cons x Nil ++ quicksort zs)
        <+> (permute pls >=> guardBy pls sorted) (Cons x xs)
    %==
      pure mnd (quicksort ys ++ Cons x Nil ++ quicksort zs)
        <+> apply (\x -> permute pls x >>= guardBy pls sorted) (Cons x xs)
        %by %rewrite permute pls >=> guardBy pls sorted
                 %to apply (\x -> permute pls x >>= guardBy pls sorted)
        %by undefined -- TODO: why???
    %==
      pure mnd (quicksort ys ++ Cons x Nil ++ quicksort zs)
        <+> (permute pls (Cons x xs) >>= guardBy pls sorted)
    %==
      pure mnd (quicksort ys ++ Cons x Nil ++ quicksort zs)
        <+> ((split pls xs >>= apply (\(ys, zs) -> (liftM2 mnd) (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs')) (permute pls ys) (permute pls zs)))
              >>= guardBy pls sorted)
    %==
      slowsort pls (Cons x xs)
        %by undefined -- TODO: not sure how to progress...
  |]
  where
    ys = proj1 (partition x xs)
    zs = proj2 (partition x xs)
    (<+>) :: forall a. m a -> m a -> m a
    (<+>) = plus pls
    (>>=) :: forall a b. m a -> (a -> m b) -> m b
    (>>=) = bind mnd
    (>=>) :: forall a b c. (a -> m b) -> (b -> m c) -> (a -> m c)
    (>=>) = kleisli mnd
    (>>) :: forall a b. m a -> m b -> m b
    (>>) = seq mnd
    mnd = plusMonad pls
