module Data.Refined.Bool where

import Prelude hiding (not)

{-@ reflect not @-}
not :: Bool -> Bool
not True = False
not False = True
