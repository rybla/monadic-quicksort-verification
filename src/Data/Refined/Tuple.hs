module Data.Refined.Tuple where

import Relation.Equality.Prop

{-@
type Pair a b = (a, b)
@-}
type Pair a b = (a, b)

{-@ reflect proj1 @-}
proj1 :: Pair a b -> a
proj1 (x, y) = x

{-@ reflect proj2 @-}
proj2 :: Pair a b -> b
proj2 (x, y) = y

instance (Eq a, Eq b, Equality a, Equality b) => Equality (a, b) where
  __Equality = Nothing

instance (Eq a, Eq b, Eq c, Equality a, Equality b, Equality c) => Equality (a, b, c) where
  __Equality = Nothing
