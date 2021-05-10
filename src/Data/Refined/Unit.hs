module Data.Refined.Unit where

import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop

{-@
type Unit = ()
@-}
type Unit = ()

{-@ reflect it @-}
it :: ()
it = ()

instance Equality Unit where
  __Equality = Nothing
