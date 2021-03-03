module Test where

import Language.Haskell.Liquid.Equational

-- Data. A list is either `LNil` or constructed with a `vhead` element and a
-- `vtail` list.
data LList a = LNil | LCons {vhead :: a, vtail :: LList a}

-- Function. Append two lists.
{-@ reflect lappend @-}
lappend :: LList a -> LList a -> LList a
lappend LNil ys = ys
lappend (LCons x xs) ys = LCons x (lappend xs ys)

-- Function. Construct a list with 1 element.
{-@ reflect llist1 @-}
llist1 :: a -> LList a
llist1 x = LCons x LNil

{-@ reflect lsingleton @-}
lsingleton :: a -> LList a
lsingleton = llist1

-- Function. Construct a list with 2 elements.
{-@ reflect llist2 @-}
llist2 :: a -> a -> LList a
llist2 x y = llist1 x `lappend` llist1 y

-- Function. Map a list-function over a list and concatenate the resulting
-- lists (i.e. list-monadic bind).
{-@ reflect lbind @-}
lbind :: LList a -> (a -> LList b) -> LList b
lbind LNil f = LNil
lbind (LCons x xs) f = f x `lappend` lbind xs f

-- Function. Map a function over a list.
{-@ reflect lmap @-}
lmap :: (a -> b) -> (LList a -> LList b)
lmap f LNil = LNil
lmap f (LCons x xs) = LCons (f x) (lmap f xs)

{-@ reflect lzip @-}
-- Function. Map a binary function over two lists (zipping).
lzip :: (a -> b -> c) -> LList a -> LList b -> LList c
lzip f xs ys = lbind xs (\x -> lbind ys (\y -> llist1 (f x y)))

-- Function. Nondeterministically split a list into two sublists.
{-@ reflect split @-}
split :: LList a -> LList (LList a, LList a)
split LNil = llist1 (LNil, LNil)
split (LCons x xs) =
  split xs
    `lbind` \(ys, zs) ->
      llist1 (LCons x ys, zs) `lappend` llist1 (ys, LCons x zs)

-- Function. Nondeterministically permute a list.
{-@ reflect permute @-}
permute :: LList a -> LList (LList a)
permute LNil = llist1 LNil
permute (LCons x xs) = permute_LCons x xs

-- Function. The `LCons` case for `permute`.
{-@ reflect permute_LCons @-}
permute_LCons :: a -> LList a -> LList (LList a)
permute_LCons x xs = split xs `lbind` (permute_LCons_f1 x)

-- Function. Auxilliary for `permute_LCons`.
{-@ reflect permute_LCons_f1 @-}
permute_LCons_f1 :: a -> (LList a, LList a) -> LList (LList a)
permute_LCons_f1 x (ys, zs) = lzip (permute_LCons_f2 x) (permute ys) (permute zs)

-- Function. Auxilliary for `permute_LCons_f2`.
{-@ reflect permute_LCons_f2 @-}
permute_LCons_f2 :: a -> LList a -> LList a -> LList a
permute_LCons_f2 x ys' zs' = ys' `lappend` llist1 x `lappend` zs'

-- Example.
{-@
permute_LCons_check :: x:a -> xs:LList a ->
  {permute (LCons x xs) = lbind (split xs) (permute_LCons_f1 x)}
@-}
permute_LCons_check :: a -> LList a -> Proof
permute_LCons_check x xs =
  permute (LCons x xs)
    ==. permute_LCons x xs
    ==. split xs `lbind` (permute_LCons_f1 x)
    *** QED

--
-- ! OLD 1
--

-- -- Function. Nondeterministically permute a list.
-- {-@ reflect permute @-}
-- permute :: LList a -> LList (LList a)
-- permute LNil = llist1 LNil
-- permute (LCons x xs) =
--   split xs `lbind` \(ys, zs) ->
--     lzip
--       (\ys' zs' -> ys' `lappend` llist1 x `lappend` zs')
--       (permute ys)
--       (permute zs)

-- -- Function. The expanded form of `permute` on an `LCons`.
-- {-@ reflect permute_LCons_expansion @-}
-- permute_LCons_expansion :: a -> LList a -> LList (LList a)
-- permute_LCons_expansion x xs =
--   split xs
--     `lbind` ( \(ys, zs) ->
--                 lzip
--                   (\ys' zs' -> ys' `lappend` llist1 x `lappend` zs')
--                   (permute ys)
--                   (permute zs)
--             )

-- -- -- Theorem. `permute_LCons_expansion` corresponds to `permute` on an `LCons`.
-- -- {-@
-- -- permute_LCons_expansion_correct :: x:a -> xs:LList a ->
-- --   {permute (LCons x xs) = permute_LCons_expansion x xs}
-- -- @-}
-- permute_LCons_expansion_correct :: a -> LList a -> Proof
-- permute_LCons_expansion_correct x xs =
--   permute (LCons x xs)
--     ==. ( split xs
--             >>= ( \(ys, zs) ->
--                     lzip
--                       (\ys' zs' -> ys' `lappend` llist1 x `lappend` zs')
--                       (permute ys)
--                       (permute zs)
--                 )
--         )
--     ==. permute_LCons_expansion x xs
--     *** QED
