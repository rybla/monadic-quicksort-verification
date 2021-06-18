{-# LANGUAGE TemplateHaskell #-}

module Relation.Equality.Prop.Reasoning where

import Control.Monad
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import Relation.Equality.Prop

-- [(a, Equality a)] -> a -> Equality a
transitivity_chain :: [Q Exp] -> Q Exp -> Q Exp
transitivity_chain [] x = [|reflexivity $x|]
transitivity_chain [x_exy] y = [|transitivity $x $y $y $exy (reflexivity x')|]
  where
    x = [|fst $x_exy|]
    exy = [|snd $x_exy|]
transitivity_chain [x_exy, y_eyz] z = [|transitivity $x $y $z $exy $eyz|]
  where
    x = [|fst $x_exy|]
    exy = [|snd $x_exy|]
    y = [|fst $y_eyz|]
    eyz = [|snd $y_eyz|]
transitivity_chain (x_exy : y_eyz : steps) z = [|transitivity $x $y $z $exy $eyz|]
  where
    x = [|fst $x_exy|]
    exy = [|snd $x_exy|]
    y = [|fst $y_eyz|]
    eyz = transitivity_chain (y_eyz : steps) z
