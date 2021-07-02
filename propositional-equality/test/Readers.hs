{-# LANGUAGE FlexibleInstances, UndecidableInstances, IncoherentInstances #-}

{-@ LIQUID "--reflection"  @-} 
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--fast"        @-}
{-@ LIQUID "--no-adt"      @-} 

module Readers where

import Language.Haskell.Liquid.ProofCombinators
import PEqProperties
import PropositionalEquality

import Prelude hiding (id, fmap, (<$>), pure, (<*>), (>>=))

type Reader a b = a -> b

{-@ reflect fmap @-}
fmap :: (a -> b) -> Reader r a -> Reader r b
fmap fab fra r = fab (fra r)

{-@ reflect id @-}
id :: a -> a 
id x = x

{-@ reflect dollar @-}
dollar :: (a -> b) -> a -> b
dollar f v = f v

{-@ reflect on @-}
on :: a -> (a -> b) -> b
on v f = f v

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> (a -> c)
compose g f x = g (f x)

functorLaw_identity :: Reflexivity a => EqT (Reader r a -> Reader r a)
{-@ functorLaw_identity :: Reflexivity a -> EqRT (Reader r a -> Reader r a) (fmap id) id @-}
functorLaw_identity =
  EqFun (fmap id) id
  (\r -> EqFun (fmap id r) (id r)
    (\a -> refl (fmap id r a)
      ? (    fmap id r a
         =~= id (r a)
         =~= id r a
         *** QED)))

functorLaw_composition :: Reflexivity c => (a -> b) -> (b -> c) -> EqT (Reader r a -> Reader r c)
{-@ functorLaw_composition :: Reflexivity c => f:(a -> b) -> g:(b -> c) ->
      EqRT (Reader r a -> Reader r c) (fmap (compose g f)) (compose (fmap g) (fmap f)) @-}
functorLaw_composition f g =
  EqFun (fmap (compose g f)) (compose (fmap g) (fmap f))
    (\rdr -> EqFun (fmap (compose g f) rdr) ((compose (fmap g) (fmap f)) rdr)
      (\r -> refl
        (fmap (compose g f) rdr r) ?
        (    fmap (compose g f) rdr r
         =~= (compose g f) (rdr r)
         =~= g (f (rdr r))
         =~= g (((fmap f) rdr) r)
         =~= fmap g ((fmap f) rdr) r    
         =~= (compose (fmap g) (fmap f)) rdr r
         *** QED)))

{-@ reflect pure @-}
pure :: a -> Reader r a
pure a _r = a

{-@ reflect ap @-}
ap :: Reader r (a -> b) -> Reader r a -> Reader r b
ap frab fra r = frab r (fra r)

applicativeLaw_identity :: (Reflexivity a, Transitivity a) => Reader r a -> EqT (Reader r a)
{-@ applicativeLaw_identity :: (Reflexivity a, Transitivity a) => v:Reader r a ->
      EqRT (Reader r a) (ap (pure id) v) v @-}
applicativeLaw_identity v =
  EqFun (ap (pure id) v) v
  (\r ->
     trans (ap (pure id) v r)
           ((pure id) r (v r))
           (v r)
       (refl (ap (pure id) v r))
       (trans ((pure id) r (v r))
              (id (v r))
              (v r)
         (refl ((pure id) r (v r)))
         (refl (id (v r)))))

applicativeLaw_homomorphism :: (Reflexivity b, Transitivity b) => (a -> b) -> a -> EqT (Reader r b)
{-@ applicativeLaw_homomorphism :: (Reflexivity b, Transitivity b) => f:(a->b) -> v:a ->
      EqRT (Reader r b) (ap (pure f) (pure v)) (pure (f v)) @-}
applicativeLaw_homomorphism f v =
  EqFun (ap (pure f) (pure v)) (pure (f v))
  (\r ->
     trans (ap (pure f) (pure v) r)
           (pure f r (pure v r))
           (pure (f v) r)
       (refl (ap (pure f) (pure v) r))
       (trans (pure f r (pure v r))
              (pure f r v)
              (pure (f v) r)
         (refl (pure f r (pure v r)))
         (trans (pure f r v)
                (f v)
                (pure (f v) r)
           (refl (pure f r v))
           (refl (f v)))))
  
applicativeLaw_interchange :: (Reflexivity b, Transitivity b) => Reader r (a -> b) -> a -> EqT (Reader r b)
{-@ applicativeLaw_interchange :: (Reflexivity b, Transitivity b) => u:(Reader r (a -> b)) -> y:a ->
      EqRT (Reader r b) (ap u (pure y)) (ap (pure (on y)) u) @-}
applicativeLaw_interchange u y =
  EqFun (ap u (pure y)) (ap (pure (on y)) u) 
  (\r ->
     trans (ap u (pure y) r)
           (u r (pure y r))
           (ap (pure (on y)) u r)
       (refl (ap u (pure y) r))
       (trans (u r (pure y r))
              (u r y)
              (ap (pure (on y)) u r)
         (refl (u r (pure y r)))
         (trans (u r y)
                ((on y) (u r))
                (ap (pure (on y)) u r)
           (refl (u r y))
           (trans ((on y) (u r))
                  ((pure (on y)) r (u r))
                  (ap (pure (on y)) u r)
             (refl ((on y) (u r)))
             (refl ((pure (on y)) r (u r)))))))

--- WHEW this one takes a long time
applicativeLaw_composition :: (Reflexivity c, Transitivity c) =>
  Reader r (b -> c) -> Reader r (a -> b) -> Reader r a -> EqT (Reader r c)
{-@ applicativeLaw_composition :: (Reflexivity c, Transitivity c) =>
      u:(Reader r (b -> c)) -> v:(Reader r (a -> b)) -> w:(Reader r a) ->
      EqRT (Reader r c) (ap (ap (ap (pure compose) u) v) w) (ap u (ap v w)) @-}
applicativeLaw_composition u v w =
  EqFun (ap (ap (ap (pure compose) u) v) w)
        (ap u (ap v w))
  (\r ->
      trans (ap (ap (ap (pure compose) u) v) w r)
            ((ap (ap (pure compose) u) v) r (w r))
            (ap u (ap v w) r)
        (refl (ap (ap (ap (pure compose) u) v) w r))
        (trans ((ap (ap (pure compose) u) v) r (w r))
               ((ap (pure compose) u) r (v r) (w r))
               (ap u (ap v w) r)
          (refl ((ap (ap (pure compose) u) v) r (w r)))
          (trans ((ap (pure compose) u) r (v r) (w r))
                 ((pure compose) r (u r) (v r) (w r))          
                 (ap u (ap v w) r)
            (refl ((ap (pure compose) u) r (v r) (w r)))
            (trans ((pure compose) r (u r) (v r) (w r))  -- skipped ((\_r -> compose) r (u r) (v r) (w r))
                   (compose (u r) (v r) (w r))
                   (ap u (ap v w) r)
              (refl ((pure compose) r (u r) (v r) (w r)))
              (trans (compose (u r) (v r) (w r))
                     ((u r) ((v r) (w r)))
                     (ap u (ap v w) r)
                (refl (compose (u r) (v r) (w r)))
                (trans ((u r) ((v r) (w r)))
                       (u r (v r (w r)))
                       (ap u (ap v w) r)
                  (refl ((u r) ((v r) (w r))))
                  (trans (u r (v r (w r)))
                         (u r (ap v w r))
                         (ap u (ap v w) r)
                    (refl (u r (v r (w r))))
                    (refl (u r (ap v w r))))))))))

ap_fmap :: (Reflexivity b, Transitivity b) => (a -> b) -> Reader r a -> EqT (Reader r b)
{-@ ap_fmap :: f:(a -> b) -> a:(Reader r a) -> EqRT (Reader r b) (fmap f a) (ap (pure f) a) @-}
ap_fmap f a =
  EqFun (fmap f a) (ap (pure f) a)
  (\r ->
     trans (fmap f a r)
           (f (a r))
           (ap (pure f) a r)
      (refl (fmap f a r))
      (trans (f (a r))
             ((pure f) r (a r))
             (ap (pure f) a r)
        (refl (f (a r)))
        (refl ((pure f) r (a r)))))

{-@ reflect bind @-}
bind :: Reader r a -> (a -> Reader r b) -> Reader r b
bind fra farb = \r -> farb (fra r) r

monadLaw_leftIdentity :: (Reflexivity b, Transitivity b) => a -> (a -> Reader r b) -> EqT (Reader r b)
{-@ monadLaw_leftIdentity :: Reflexivity b => a:a -> f:(a -> Reader r b) ->
      EqRT (Reader r b) (bind (pure a) f) (f a)
@-}
monadLaw_leftIdentity a f =
  EqFun (bind (pure a) f) (f a)
  (\r ->
      trans (bind (pure a) f r) (f (pure a r) r) (f a r)
            (refl (bind (pure a) f r))
            (refl (f (pure a r) r)))

monadLaw_leftIdentity' :: (Reflexivity b, Transitivity b) => a -> (a -> Reader r b) -> EqT (Reader r b)
{-@ monadLaw_leftIdentity' :: Reflexivity b => a:a -> f:(a -> Reader r b) ->
      EqRT (Reader r b) (bind (pure a) f) (f a)
@-}
monadLaw_leftIdentity' a f =
  EqFun (bind (pure a) f) (f a)
  (\r ->
      refl (bind (pure a) f r) ? 
      (bind (pure a) f r =~= f (pure a r) r  *** QED)) 

monadLaw_rightIdentity :: Reflexivity a => (Reader r a) -> EqT (Reader r a)
{-@ monadLaw_rightIdentity :: Reflexivity a => m:(Reader r a) -> EqRT (Reader r a) (bind m pure) m @-}
monadLaw_rightIdentity m =
  EqFun (bind m pure) m
  (\r ->
     refl (bind m pure r) ?
     (    (bind m pure r)
      =~= pure (m r) r
      *** QED))

{-@ reflect kleisli @-}
kleisli :: (a -> Reader r b) -> (b -> Reader r c) -> a -> Reader r c
kleisli f g x = bind (f x) g

monadLaw_associativity
  :: (Reflexivity c, Transitivity c)=> (Reader r a) -> (a -> Reader r b) -> (b -> Reader r c) -> EqT (Reader r c)
{-@ monadLaw_associativity :: (Reflexivity c, Transitivity c) =>
      m:(Reader r a) -> f:(a -> Reader r b) -> g:(b -> Reader r c) ->
      EqRT (Reader r c) (bind (bind m f) g) (bind m (kleisli f g))
@-}
monadLaw_associativity m f g =
  EqFun (bind (bind m f) g) (bind m (kleisli f g)) (\r ->
     let el  = bind (bind m f) g r
         eml = g (bind m f r) r
         em  = (bind (f (m r)) g) r
         emr = kleisli f g (m r) r
         er  = bind m (kleisli f g) r 
     in trans el em er 
           (trans el eml em (refl el) (refl eml))
           (trans em emr er (refl em) (refl emr))
  )
