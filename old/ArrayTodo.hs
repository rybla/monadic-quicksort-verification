{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Sort.ArrayTodo where

import Data.Refined.Bool
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Tuple
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.TH.Syntax
import Placeholder.M
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Sort.List
import Prelude hiding (all, foldl, length, pure, read, readList, seq)
