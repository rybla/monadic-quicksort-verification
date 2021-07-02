module Unsoundness where 


{-@ assume hab :: (x:a -> {false} ) -> { false }@-}
hab :: (a -> ()) -> ()
hab _ = ()

{-@ client :: () -> {false} @-}
client :: () -> ()
client _ = hab evidH 

{-@ evidH :: Int -> () @-}
evidH :: Int -> ()
evidH _ = () 


{-@ assume funExt :: f:(a -> b) -> g:(a -> b) -> (x:a -> {f x = g x}) -> {f = g} @-}
funExt :: (a -> b) -> (a -> b) -> (a -> ()) -> ()
funExt _ _ _ = ()

unsoundEq :: () -> ()
{-@ unsoundEq :: () -> {f = g} @-}
unsoundEq _ = funExt f g (\_ -> ())

totalUnsoundness :: () -> ()
{-@ totalUnsoundness :: () -> { 1 = 2 } @-}
totalUnsoundness _ = unsoundEq () `const` f 0 `const` g 0

{-@ reflect f @-}
{-@ reflect g @-}
f, g :: Integer -> Integer 
f x = x + 1 
g x = x + 2