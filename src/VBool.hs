module VBool where

import Function
import Relation

{-@ reflect vand @-}
vand :: Op2 Bool
vand b1 b2 = if b1 then b2 else False

{-@ reflect vnot @-}
vnot :: Op1 Bool
vnot b = if b then False else True

{-@ reflect vbranch @-}
vbranch :: forall a. Bool -> a -> a -> a
vbranch b x y = if b then x else y
