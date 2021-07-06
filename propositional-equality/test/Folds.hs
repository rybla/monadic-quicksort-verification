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

foldEq :: AEq b => EqualityProp ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq :: AEq b => EqualProp ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq = extensionality foldl foldl' $ \f ->
  extensionality (foldl f) (foldl' f) $ \b ->
    extensionality (foldl f b) (foldl' f b) $ \xs ->
      fromEqSMT (foldl f b xs) (foldl' f b xs) (theorem f b xs ? reflP (foldl f b xs))

-- TODO: problem with order format of n-extending?
{-@ ignore foldEq_macros @-}
foldEq_macros :: Equality ((b -> a -> b) -> b -> [a] -> b) => EqualityProp ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq_macros :: Equality ((b -> a -> b) -> b -> [a] -> b) => EqualProp ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq_macros =
  [eqp| foldl
    %== apply (\f -> foldl f)                                     %by                              %extend f %by %reflexivity
    %== apply (\b -> apply (\f -> foldl f) b)                     %by                %extend b %by %extend f %by %reflexivity
    %== apply (\xs -> apply (\b -> apply (\f -> foldl f) b) xs)   %by %extend xs %by %extend b %by %extend f %by %reflexivity
    %== apply (\xs -> apply (\b -> apply (\f -> foldl' f) b) xs)  %by %extend xs %by %extend b %by %extend f %by %smt %by theorem xs b f
    %== apply (\b -> apply (\f -> foldl' f) b)                    %by %extend xs %by %extend b %by %extend f %by %reflexivity
    %== apply (\f -> foldl' f)                                    %by                %extend b %by %extend f %by %reflexivity
    %== foldl'                                                    %by                              %extend f %by %reflexivity
  |]

foldEq' :: Reflexivity b => EqualityProp ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq' :: Reflexivity b => EqualProp ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq' = extensionality foldl foldl' $ \f ->
  extensionality (foldl f) (foldl' f) $ \b ->
    extensionality (foldl f b) (foldl' f b) $ \xs ->
      refl (foldl f b xs) ? theorem f b xs

foldEq'' :: (Reflexivity b, Equality b) => EqualityProp ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq'' :: (Reflexivity b, Equality b) => EqualProp ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq'' = extensionality foldl foldl' $ \f ->
  extensionality (foldl f) (foldl' f) $ \b ->
    extensionality (foldl f b) (foldl' f b) $ \xs ->
      transitivity
        (foldl f b xs)
        (foldr (construct f) id xs b)
        (foldl' f b xs)
        (foldLemma f b xs)
        (refl (foldl' f b xs))

-- more awkward, original statement of the inner part above
foldSame :: (Reflexivity b, Equality b) => (b -> a -> b) -> b -> [a] -> EqualityProp b
{-@ foldSame :: (Reflexivity b, Equality b) => f:(b -> a -> b) -> b:b -> xs:[a]
             -> EqualProp b {foldl f b xs} {foldl' f b xs} @-}
foldSame f b xs =
  transitivity
    (foldl' f b xs)
    (foldr (construct f) id xs b)
    (foldl f b xs)
    (refl (foldl' f b xs))
    ( symmetry
        (foldl f b xs)
        (foldr (construct f) id xs b)
        (foldLemma f b xs)
    )

foldLemma :: (Reflexivity b, Equality b) => (b -> a -> b) -> b -> [a] -> EqualityProp b
{-@ foldLemma :: (Reflexivity b, Equality b) => f:(b -> a -> b) -> b:b -> xs:[a] -> EqualProp b {foldl f b xs} {foldr (construct f) id xs b} @-}
foldLemma f b [] =
  transitivity
    (foldl f b [])
    b
    (foldr (construct f) id [] b)
    (refl (foldl f b []))
    ( transitivity
        b
        (id b)
        (foldr (construct f) id [] b)
        (refl b)
        (refl (id b))
    )
foldLemma f b (x : xs) =
  transitivity
    (foldl f b (x : xs))
    (foldl f (f b x) xs)
    (foldr (construct f) id (x : xs) b)
    (refl (foldl f b (x : xs)))
    ( transitivity
        (foldl f (f b x) xs)
        (foldr (construct f) id xs (f b x))
        (foldr (construct f) id (x : xs) b)
        (foldLemma f (f b x) xs)
        ( transitivity
            (foldr (construct f) id xs (f b x))
            (construct f x (foldr (construct f) id xs) b)
            (foldr (construct f) id (x : xs) b)
            (refl (foldr (construct f) id xs (f b x)))
            (refl (construct f x (foldr (construct f) id xs) b))
        )
    )

foldLemma_macros :: (Reflexivity b, Equality b) => (b -> a -> b) -> b -> [a] -> EqualityProp b
{-@ foldLemma_macros :: (Reflexivity b, Equality b) => f:(b -> a -> b) -> b:b -> xs:[a] -> EqualProp b {foldl f b xs} {foldr (construct f) id xs b} @-}
foldLemma_macros f b [] = undefined
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
