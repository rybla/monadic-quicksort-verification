{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Sort.ArrayProto where

import Control.Refined.Monad
import Control.Refined.Monad.Array hiding (monad)
import Control.Refined.Monad.ArrayPlus
import Control.Refined.Monad.Plus hiding (monad)
import Data.Refined.Bool
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Tuple
import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Sort.Array
import Sort.List
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (*), (+), (++), (>>), (>>=))

-- [ref] display 12
{-@
iqsort_spec ::
  Equality (m ()) =>
  Monad m ->
  Array m Elem ->
  Plus m ->
  arp:ArrayPlus m Elem ->
  i:Index ->
  xs:List Elem ->
  RefinesPlus m () {plusm arp}
    {iqsort_spec_aux1 arp i xs}
    {iqsort_spec_aux2 arp i xs}
@-}
iqsort_spec :: Equality (m ()) => Monad m -> Array m Elem -> Plus m -> ArrayPlus m Elem -> Index -> List Elem -> EqualityProp (m ())
iqsort_spec _ _ _ arp i xs = undefined -- TODO
