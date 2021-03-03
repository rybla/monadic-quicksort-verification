{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Folds where

import Prelude hiding (foldl, foldr, id)
import Language.Haskell.Liquid.ProofCombinators

import PropositionalEquality
import PEqProperties

foldEq     :: AEq b => EqT  ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq :: AEq b => EqRT ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq = EqFun foldl foldl' $ \f ->
           EqFun (foldl f) (foldl' f) $ \b ->
             EqFun (foldl f b) (foldl' f b) $ \xs ->
               eqSMT (foldl f b xs) (foldl' f b xs) (theorem f b xs ? reflP (foldl f b xs))

foldEq'     :: Reflexivity b => EqT  ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq' :: Reflexivity b => EqRT ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq' = EqFun foldl foldl' $ \f ->
            EqFun (foldl f) (foldl' f) $ \b ->
              EqFun (foldl f b) (foldl' f b) $ \xs ->
                refl (foldl f b xs) ? theorem f b xs

foldEq''     :: (Reflexivity b, Transitivity b) => EqT ((b -> a -> b) -> b -> [a] -> b)
{-@ foldEq'' :: (Reflexivity b, Transitivity b) => EqRT ((b -> a -> b) -> b -> [a] -> b) {foldl} {foldl'} @-}
foldEq'' = EqFun foldl foldl' $ \f ->
               EqFun (foldl f) (foldl' f) $ \b ->
                   EqFun (foldl f b) (foldl' f b) $ \xs ->
                     trans (foldl f b xs) (foldr (construct f) id xs b) (foldl'  f b xs)
                       (foldLemma f b xs)
                       (refl (foldl' f b xs))

-- more awkward, original statement of the inner part above
foldSame     :: (Reflexivity b, Symmetry b, Transitivity b) => (b -> a -> b) -> b -> [a] -> EqT b
{-@ foldSame :: (Reflexivity b, Transitivity b) => f:(b -> a -> b) -> b:b -> xs:[a] 
             -> EqRT b {foldl f b xs} {foldl' f b xs} @-}
foldSame f b xs =
    trans (foldl' f b xs)
        (foldr (construct f) id xs b)
        (foldl f b xs)
    (refl (foldl' f b xs))
    (sym (foldl f b xs)
         (foldr (construct f) id xs b)
       (foldLemma f b xs))

foldLemma     :: (Reflexivity b, Transitivity b) => (b -> a -> b) -> b -> [a] -> EqT b
{-@ foldLemma :: (Reflexivity b, Transitivity b) => f:(b -> a -> b) -> b:b -> xs:[a] -> EqRT b {foldl f b xs} {foldr (construct f) id xs b} @-}
foldLemma f b [] =
  trans (foldl f b [])
        b 
        (foldr (construct f) id [] b)
    (refl (foldl f b []))
    (trans b
           (id b)
           (foldr (construct f) id [] b)
      (refl b)
      (refl (id b)))
foldLemma f b (x:xs) =
  trans (foldl f b (x:xs))
        (foldl f (f b x) xs)
        (foldr (construct f) id (x:xs) b)
    (refl (foldl f b (x:xs)))
    (trans (foldl f (f b x) xs)
           (foldr (construct f) id xs (f b x))
           (foldr (construct f) id (x:xs) b)
      (foldLemma f (f b x) xs)
      (trans (foldr (construct f) id xs (f b x))
             (construct f x (foldr (construct f) id xs) b)
             (foldr (construct f) id (x:xs) b)
        (refl (foldr (construct f) id xs (f b x)))
        (refl (construct f x (foldr (construct f) id xs) b))))

theorem :: (b -> a -> b) -> b -> [a] -> ()
{-@ theorem :: f:(b -> a -> b) -> b:b -> xs:[a] 
            -> { foldl f b xs = foldl' f b xs } @-}
theorem f b xs 
  =   foldl'  f b xs 
  === foldr (construct f) id xs b
      ? lemma f b xs 
  === foldl  f b xs
  *** QED 

lemma :: (b -> a -> b) -> b -> [a] -> ()
{-@ lemma :: f:(b -> a -> b) -> b:b -> xs:[a] 
          -> { foldl f b xs = foldr (construct f) id xs b } @-}
lemma f b []
  =   foldl f b []
  === b 
  === id b 
  === (foldr (construct f) id []) b
  === foldr (construct f) id [] b
  *** QED 
lemma f b (x:xs) 
  =   foldl f b (x:xs)
  === foldl f (f b x) xs 
      ? lemma f (f b x) xs
  === foldr (construct f) id xs (f b x)
  === construct f x (foldr (construct f) id xs) b
  === foldr (construct f) id (x:xs) b
  *** QED 

{-@ reflect foldl @-}
foldl :: (b -> a -> b) -> b -> [a] -> b
foldl _ b []     = b
foldl f b (x:xs) = foldl f (b `f` x) xs 

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
foldr _ b []     = b
foldr f b (x:xs) = f x (foldr f b xs) 

