module Data.Refined.Unit where

import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop

{-@
type Unit = ()
@-}
type Unit = ()

{-@ reflect it @-}
it :: Unit
it = ()

instance EqSMT Unit where
  eqSMT x y = x == y
