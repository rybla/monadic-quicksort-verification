{-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--no-termination" @-}
-- needed this because `partl` threw termination checking errors even with lazy annotation
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Sort.IPartl where

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
import Sorr.IPartlWork
import Sort.IPartl
import Sort.List
import Prelude hiding (all, concat, foldl, length, pure, read, readList, seq)
