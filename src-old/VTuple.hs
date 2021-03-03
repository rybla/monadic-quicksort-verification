module VTuple where

{-@ type VTuple2D a = (a, a) @-}
type VTuple2D a = (a, a)

{-@ type VTuple3D a = (a, a, a) @-}
type VTuple3D a = (a, a, a)

{-@ type VTuple4D a = (a, a, a, a) @-}
type VTuple4D a = (a, a, a, a)

{-@ inline vtuple2D @-}
vtuple2D :: forall a. a -> a -> VTuple2D a
vtuple2D x1 x2 = (x1, x2)

{-@ inline vtuple3D @-}
vtuple3D :: forall a. a -> a -> a -> VTuple3D a
vtuple3D x1 x2 x3 = (x1, x2, x3)

{-@ inline fst2 @-}
fst2 :: (a, b) -> a
fst2 (x, _) = x

{-@ inline snd2 @-}
snd2 :: (a, b) -> b
snd2 (_, y) = y

{-@ inline fst2D @-}
fst2D :: VTuple2D a -> a
fst2D (x, _) = x

{-@ inline snd2D @-}
snd2D :: VTuple2D a -> a
snd2D (_, y) = y

{-@ inline fst3 @-}
fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

{-@ inline snd3 @-}
snd3 :: (a, b, c) -> b
snd3 (_, y, _) = y

{-@ inline thd3 @-}
thd3 :: (a, b, c) -> c
thd3 (_, _, z) = z

{-@ inline fst2D @-}
fst3D :: VTuple3D a -> a
fst3D (x, _, _) = x

{-@ inline snd2D @-}
snd3D :: VTuple3D a -> a
snd3D (_, y, _) = y

{-@ inline thd3D @-}
thd3D :: VTuple3D a -> a
thd3D (_, _, z) = z