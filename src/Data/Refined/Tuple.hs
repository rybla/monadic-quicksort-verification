module Data.Refined.Tuple where

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
