{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-} 

module RunTimeCheck where 

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding ((++))
import PropositionalEquality
import PEqProperties


{-@ critical :: {x:a | slowSpec x } -> a @-}
critical :: a -> a 
critical x = x 

{-@ bar :: EqRT (a -> Bool) {fastSpec} {slowSpec} -> a -> Maybe a @-}
bar :: EqT (a -> Bool) -> a -> Maybe a 
bar pf x = if fastSpec x ? toSMT (fastSpec x) (slowSpec x) (unExt x pf)
            then Just (critical x)
            else Nothing 

{-@ unExt :: x:a -> EqRT (a -> Bool) {fastSpec} {slowSpec} -> EqRT Bool {fastSpec x} {slowSpec x} @-}
unExt :: a -> EqT (a -> Bool) -> EqT Bool 
unExt x p = EqCtx fastSpec slowSpec p (flip' x) ? flip' x fastSpec ? flip' x slowSpec 



{-@ reflect flip' @-}
flip' :: a -> (a -> b) -> b
flip' x f = f x  

{-@ reflect fastSpec @-}
fastSpec :: a -> Bool
fastSpec _ = True 

{-@ reflect slowSpec @-}
slowSpec :: a -> Bool
slowSpec _ = True  