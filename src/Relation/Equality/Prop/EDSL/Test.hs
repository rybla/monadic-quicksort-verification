{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Relation.Equality.Prop.EDSL.Test where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL

{-
test
-}

{-@
data Bit = B0 | B1
@-}
data Bit = B0 | B1

{-@
test_bit ::
  (Equality (Bit -> Bit), Equality Bit) =>
  EqualProp (Bit -> Bit)
    {identity (\x:Bit -> x)}
    {identity (\x:Bit -> x)}
@-}
test_bit :: (Equality (Bit -> Bit), Equality Bit) => EqualityProp (Bit -> Bit)
test_bit =
  extensionality
    (identity (\x -> x))
    (identity (\x -> x))
    (\x -> reflexivity x ? identity (\x -> x) x)
