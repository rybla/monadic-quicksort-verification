module Function where


-- Types

{-@ type Op1 a = a -> a @-}
type Op1 a = a -> a

{-@ type Op2 a = a -> a -> a @-}
type Op2 a = a -> a -> a


-- Predicates
-- NOTE. Predicate parameters must be capitalized.

{-@ predicate IsAssociative  F X Y Z   = F X (F Y Z) = F (F X Y) Z @-}
{-@ predicate IsCommutative  F X Y     = F X Y = F Y X @-}
{-@ predicate IsDistributive F G X Y Z = F X (G Y Z) = G (F X Y) (F X Z) @-}

{-@ predicate IsIdentityLeft  F E X = F E X = X @-}
{-@ predicate IsIdentityRight F E X = F X E = X @-}
{-@ predicate IsIdentity      F E X = IsIdentityLeft F E X && IsIdentityRight F E X @-}

{-@ predicate IsZeroLeft  F Z X = F Z X = Z @-}
{-@ predicate IsZeroRight F Z X = F X Z = Z @-}
{-@ predicate IsZero      F Z X = IsZeroLeft F Z X && IsZeroRight F Z X @-}


-- Functions
-- NOTE. Doesn't allow reference to these functions unless I use `reflect`
-- i.e. I can't give them my own liquid type declarations

{-@ reflect vid @-}
vid :: forall a . a -> a
vid x = x


{-@ reflect vcomp @-}
vcomp :: forall a b c . (b -> c) -> (a -> b) -> (a -> c)
vcomp f g = \x -> f (g x)


{-@ reflect vconst @-}
vconst :: forall a b . a -> b -> a
vconst x _ = x


{-@ reflect vconstF @-}
vconstF :: forall a b c . (b -> c) -> (a -> b -> c)
vconstF f _ y = f y


{-@ reflect vflip @-}
vflip :: forall a b c . (b -> a -> c) -> (a -> b -> c)
vflip f x y = f y x


{-@ reflect vdiagonalize @-}
vdiagonalize :: forall a b . (a -> a -> a) -> (a -> a)
vdiagonalize f x = f x x


{-@ infix 0 & @-}
infix 0 &
{-@ reflect & @-}
(&) :: forall a b . a -> (a -> b) -> b
x & f = f x
