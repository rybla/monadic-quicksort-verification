{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Control.Refined.Monad.ArrayPlus where

import Control.Refined.Monad
import Control.Refined.Monad.Array (Array)
import Control.Refined.Monad.Plus (Plus)
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Prelude hiding (Monad, length, pure, read, readList, seq, (>>), (>>=))

{-@
data ArrayPlus m a = ArrayPlus
  { monad :: Monad m,
    plusm :: Plus m,
    array :: Array m a
  }
@-}
data ArrayPlus m a = ArrayPlus
  { monad :: Monad m,
    plusm :: Plus m,
    array :: Array m a
  }
