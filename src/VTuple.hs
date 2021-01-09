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
