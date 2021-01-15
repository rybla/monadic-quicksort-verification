module VTuple where

{-@ type VTuple2D a = (a, a) @-}
type VTuple2D a = (a, a)

{-@ type VTuple3D a = (a, a, a) @-}
type VTuple3D a = (a, a, a)

{-@ type VTuple4D a = (a, a, a, a) @-}
type VTuple4D a = (a, a, a, a)

{-@ reflect vtuple2D @-}
vtuple2D :: forall a. a -> a -> VTuple2D a
vtuple2D x1 x2 = (x1, x2)

{-@ reflect vtuple3D @-}
vtuple3D :: forall a. a -> a -> a -> VTuple3D a
vtuple3D x1 x2 x3 = (x1, x2, x3)

{-@ reflect fst2D @-}
fst2D :: VTuple2D a -> a
fst2D (x, _) = x

{-@ reflect snd2D @-}
snd2D :: VTuple2D a -> a
snd2D (_, y) = y

{-@ reflect fst3 @-}
fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

{-@ reflect snd3 @-}
snd3 :: (a, b, c) -> b
snd3 (_, y, _) = y

{-@ reflect thd3 @-}
thd3 :: (a, b, c) -> c
thd3 (_, _, z) = z

{-@ reflect fst2D @-}
fst3D :: VTuple3D a -> a
fst3D (x, _, _) = x

{-@ reflect snd2D @-}
snd3D :: VTuple3D a -> a
snd3D (_, y, _) = y

{-@ reflect thd3D @-}
thd3D :: VTuple3D a -> a
thd3D (_, _, z) = z