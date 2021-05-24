{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Sort.ArrayProto where

import Data.Refined.Bool
import Data.Refined.List
import Data.Refined.Natural
import Data.Refined.Tuple
import Data.Refined.Unit
import Data.Text (Text, unpack)
import Function
import Language.Haskell.Liquid.Equational
import Language.Haskell.TH.Ppr (pprint)
import Language.Haskell.TH.Syntax
import NeatInterpolation (text)
import Placeholder.M
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL
import Relation.Equality.Prop.Reasoning
import Sort.Array
import Sort.List
import Prelude hiding (Monad, all, foldl, length, pure, read, readList, seq, (*), (+), (++), (>>), (>>=))

-- uses:
-- - defn of `dispatch`
-- - function calls distribute into `if`
-- - `permute_preserves_length`
-- - commutativity
-- - [ref 9]
{-@
ipartl_spec_steps4to7 ::
  (Equality (M (Natural, Natural)), Equality (M (Natural, Natural, Natural)), Equality (M (List Int, List Int, List Int))) =>
  p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
  RefinesPlus (Natural, Natural)
    {ipartl_spec_step4 p i x xs ys zs}
    {ipartl_spec_step7 p i x xs ys zs}
@-}
ipartl_spec_steps4to7 :: (Equality (M (Natural, Natural)), Equality (M (Natural, Natural, Natural)), Equality (M (List Int, List Int, List Int))) => Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps4to7 p i x xs ys zs = undefined

{- -- * correct
  (refinesplus_equalprop (ipartl_spec_step4 p i x xs ys zs) (ipartl_spec_step7 p i x xs ys zs))
    [eqpropchain|
        ipartl_spec_step4 p i x xs ys zs
      %==
        ipartl_spec_step5 p i x xs ys zs
          %by undefined %-- TODO: either this is wrong: ipartl_spec_steps4to5 p i x xs ys zs
      %==
        ipartl_spec_step6 p i x xs ys zs
          %by undefined %-- TODO: or this is wrong: ipartl_spec_steps5to6 p i x xs ys zs
      %==
        ipartl_spec_step7 p i x xs ys zs
          %by ipartl_spec_steps6to7 p i x xs ys zs
    |]
-}
