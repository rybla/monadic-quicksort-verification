{-@ LIQUID "--ple"        @-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Folds where

import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Prelude hiding (foldl, foldr, id)

foldEq :: Equality b => EqualityProp ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq :: EqualProp ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq = extensionality foldl foldl' $ \f ->
  extensionality (foldl f) (foldl' f) $ \b ->
    extensionality (foldl f b) (foldl' f b) $ \xs ->
      reflexivity (foldl f b xs) ? (theorem f b xs)

foldEq' :: Equality b => EqualityProp ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq' :: Equality b => EqualProp ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq' = extensionality foldl foldl' $ \f ->
  extensionality (foldl f) (foldl' f) $ \b ->
    extensionality (foldl f b) (foldl' f b) $ \xs ->
      reflexivity (foldl f b xs) ? theorem f b xs

foldEq_macros :: (Equality b, Equality ((b -> a -> b) -> b -> [a] -> b)) => EqualityProp ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq_macros :: (Equality b, Equality ((b -> a -> b) -> b -> [a] -> b)) => EqualProp ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq_macros =
  [eqp| foldl %== foldl'
          %by %extend f
          %by %extend b
          %by %extend xs
          %by %smt
          %by theorem f b xs
  |]

foldEq'' :: Equality b => EqualityProp ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq'' :: Equality b => EqualProp ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq'' = extensionality foldl foldl' $ \f ->
  extensionality (foldl f) (foldl' f) $ \b ->
    extensionality (foldl f b) (foldl' f b) $ \xs ->
      transitivity
        (foldl f b xs)
        (foldr (construct f) id xs b)
        (foldl' f b xs)
        (foldLemma f b xs)
        (reflexivity (foldl' f b xs))

-- more awkward, original statement of the inner part above
foldSame :: Equality b => (b -> a -> b) -> b -> [a] -> EqualityProp b
{-@ foldSame :: Equality b => f:(b -> a -> b) -> b:b -> xs:[a]
             -> EqualProp b {foldl f b xs} {foldl' f b xs} @-}
foldSame f b xs =
  transitivity
    (foldl' f b xs)
    (foldr (construct f) id xs b)
    (foldl f b xs)
    (reflexivity (foldl' f b xs))
    ( symmetry
        (foldl f b xs)
        (foldr (construct f) id xs b)
        (foldLemma f b xs)
    )

-- more awkward, original statement of the inner part above
foldSame_macros :: Equality b => (b -> a -> b) -> b -> [a] -> EqualityProp b
{-@ foldSame_macros :: Equality b => f:(b -> a -> b) -> b:b -> xs:[a]
             -> EqualProp b {foldl f b xs} {foldl' f b xs} @-}
foldSame_macros f b xs =
  [eqp| foldl f b xs
    %== foldr (construct f) id xs b
          %by foldLemma f b xs
    %== foldl' f b xs
          %by %symmetry
          %by %reflexivity
  |]

foldLemma :: Equality b => (b -> a -> b) -> b -> [a] -> EqualityProp b
{-@ foldLemma :: Equality b => f:(b -> a -> b) -> b:b -> xs:[a] -> EqualProp b {foldl f b xs} {foldr (construct f) id xs b} @-}
foldLemma f b [] =
  transitivity
    (foldl f b [])
    b
    (foldr (construct f) id [] b)
    (reflexivity (foldl f b []))
    ( transitivity
        b
        (id b)
        (foldr (construct f) id [] b)
        (reflexivity b)
        (reflexivity (id b))
    )
foldLemma f b (x : xs) =
  transitivity
    (foldl f b (x : xs))
    (foldl f (f b x) xs)
    (foldr (construct f) id (x : xs) b)
    (reflexivity (foldl f b (x : xs)))
    ( transitivity
        (foldl f (f b x) xs)
        (foldr (construct f) id xs (f b x))
        (foldr (construct f) id (x : xs) b)
        (foldLemma f (f b x) xs)
        ( transitivity
            (foldr (construct f) id xs (f b x))
            (construct f x (foldr (construct f) id xs) b)
            (foldr (construct f) id (x : xs) b)
            (reflexivity (foldr (construct f) id xs (f b x)))
            (reflexivity (construct f x (foldr (construct f) id xs) b))
        )
    )

foldLemma_macros :: Equality b => (b -> a -> b) -> b -> [a] -> EqualityProp b
{-@ foldLemma_macros :: Equality b => f:(b -> a -> b) -> b:b -> xs:[a] -> EqualProp b {foldl f b xs} {foldr (construct f) id xs b} @-}
foldLemma_macros f b [] =
  [eqp| foldl f b []
    %== b
    %== id b
    %== foldr (construct f) id [] b
  |]
foldLemma_macros f b (x : xs) =
  [eqp| foldl f b (x : xs)
    %== foldl f (f b x) xs
    %== foldr (construct f) id xs (f b x)            %by foldLemma f (f b x) xs
    %== construct f x (foldr (construct f) id xs) b
    %== foldr (construct f) id (x : xs) b
  |]

theorem :: (b -> a -> b) -> b -> [a] -> ()
{-@ theorem :: f:(b -> a -> b) -> b:b -> xs:[a]
            -> { foldl f b xs = foldl' f b xs } @-}
theorem f b xs =
  foldl' f b xs
    === foldr (construct f) id xs b
      ? lemma f b xs
    === foldl f b xs
    *** QED

lemma :: (b -> a -> b) -> b -> [a] -> ()
{-@ lemma :: f:(b -> a -> b) -> b:b -> xs:[a]
          -> { foldl f b xs = foldr (construct f) id xs b } @-}
lemma f b [] =
  foldl f b []
    === b
    === id b
    === (foldr (construct f) id []) b
    === foldr (construct f) id [] b
    *** QED
lemma f b (x : xs) =
  foldl f b (x : xs)
    === foldl f (f b x) xs
      ? lemma f (f b x) xs
    === foldr (construct f) id xs (f b x)
    === construct f x (foldr (construct f) id xs) b
    === foldr (construct f) id (x : xs) b
    *** QED

{-@ reflect foldl @-}
foldl :: (b -> a -> b) -> b -> [a] -> b
foldl _ b [] = b
foldl f b (x : xs) = foldl f (b `f` x) xs

{-@ reflect foldl' @-}
foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' f b xs = foldr (construct f) id xs b

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect construct @-}
construct :: (b -> a -> b) -> a -> (b -> c) -> b -> c
construct f x r acc = r (f acc x)

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ b [] = b
foldr f b (x : xs) = f x (foldr f b xs)
