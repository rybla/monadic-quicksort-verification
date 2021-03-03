module Function where

import Prelude hiding (flip, map)

{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect given @-}
given :: a -> (a -> b) -> b
given x f = f x

{-@ reflect map @-}
map :: (a -> b) -> ([a] -> [b])
map f [] = []
map f (x : xs) = f x : map f xs

{-@ reflect flip @-}
flip :: (a -> b -> c) -> (b -> a -> c)
flip f y x = f x y
