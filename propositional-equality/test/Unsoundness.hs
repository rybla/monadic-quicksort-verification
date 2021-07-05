module Unsoundness where 

import Function 

{-@ assume funExt :: f:(a -> b) -> g:(a -> b) -> (x:a -> {f x = g x}) -> {f = g} @-}
funExt :: (a -> b) -> (a -> b) -> (a -> ()) -> ()
funExt _ _ _ = ()


{-@ reflect incrInt @-}
{-@ reflect incrPos @-}
incrInt :: Integer -> Integer
incrPos :: Integer -> Integer
incrInt n = n + 1
incrPos n = if 0 < n then n + 1 else 0 

{-@ ple incrSamePos @-}
{-@ type Pos = {n:Integer | 0 < n } @-}
{-@ incrSamePos :: n:Pos -> {incrPos n = incrInt n} @-}
incrSamePos :: Integer -> ()
incrSamePos _ = ()


{-@ incrExt :: () -> { incrPos = incrInt } @-}
incrExt :: () -> ()
incrExt _ = funExt incrPos incrInt incrSamePos 

{-@ incrMap :: xs:[Integer] -> {map incrPos xs = map incrInt xs} @-}
incrMap :: [Integer] -> ()
incrMap xs = incrExt ()

{-@ ple inconsistencyI @-}
{-@ inconsistencyI :: () -> {incrPos (0-5) = incrInt (0-5)} @-}
inconsistencyI :: () -> ()
inconsistencyI _ = incrExt ()


{-@ reflect plus2 @-}
plus2 :: Integer -> Integer
plus2 x = x + 2 


{-@ type Empty = {v:Integer | false } @-}
{-@ ple incrSameEmpty @-}
incrSameEmpty :: Integer -> ()
{-@ incrSameEmpty :: n:Empty -> {incrInt n = plus2 n} @-}
incrSameEmpty _ = ()

{-@ incrPlus2Ext :: () -> { incrInt = plus2 } @-}
incrPlus2Ext :: () -> ()
incrPlus2Ext _ = funExt incrInt plus2 incrSameEmpty

inconsistencyII :: () -> () 
{-@ inconsistencyII :: () -> { incrInt 0 = plus2 0 } @-} 
inconsistencyII _ = incrPlus2Ext ()