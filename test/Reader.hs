module Reader where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop

{-
# Reader Monad
-}

{-
## Definitions
-}

type Reader r a = r -> a

{-@ reflect pure @-}
pure :: a -> Reader r a
pure a = \_ -> a

{-@ reflect bind @-}
bind :: Reader r a -> (a -> Reader r b) -> Reader r b
bind m k = \r -> k (m r) r

{-@ reflect kleisli @-}
kleisli :: (a -> Reader r b) -> (b -> Reader r c) -> (a -> Reader r c)
kleisli f g x = bind (f x) g

{-
## Laws
-}

{-@
identityLeft ::
  Equality b =>
  x:a ->
  k:(a -> Reader r b) ->
  EqualProp (Reader r b)
    {bind (pure x) k}
    {k x}
@-}
identityLeft ::
  Equality b =>
  a ->
  (a -> Reader r b) ->
  EqualityProp (Reader r b)
identityLeft x k =
  extensionality (bind (pure x) k) (k x) $ \r ->
    reflexivity (bind (pure x) k r)
      ? ( bind (pure x) k r
            =~= k (pure x r) r
            =~= k x r
            *** QED
        )

{-@
identityRight ::
  Equality a =>
  m:Reader r a ->
  EqualProp (Reader r a)
    {bind m pure}
    {m}
@-}
identityRight ::
  Equality a =>
  Reader r a ->
  EqualityProp (Reader r a)
identityRight m =
  extensionality (bind m pure) m $ \r ->
    reflexivity (bind m pure r)
      ? ( bind m pure r
            =~= pure (m r) r
            =~= m r
            *** QED
        )

{-@
associativity ::
  Equality c =>
  m:Reader r a ->
  k1:(a -> Reader r b) ->
  k2:(b -> Reader r c) ->
  EqualProp (Reader r c)
    {bind (bind m k1) k2}
    {bind m (kleisli k1 k2)}
@-}
associativity ::
  Equality c =>
  Reader r a ->
  (a -> Reader r b) ->
  (b -> Reader r c) ->
  EqualityProp (Reader r c)
associativity m k1 k2 =
  extensionality (bind (bind m k1) k2) (bind m (kleisli k1 k2)) $ \r ->
    let t1 = bind (bind m k1) k2 r
        t2 = k2 (bind m k1 r) r
        t3 = bind (k1 (m r)) k2 r
        t4 = kleisli k1 k2 (m r) r
        t5 = bind m (kleisli k1 k2) r
     in (transitivity t1 t3 t5)
          ( (transitivity t1 t2 t3)
              (reflexivity t1)
              (reflexivity t2)
          )
          ( (transitivity t3 t4 t5)
              (reflexivity t3)
              (reflexivity t4)
          )
