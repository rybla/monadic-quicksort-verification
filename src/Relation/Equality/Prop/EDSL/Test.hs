{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Relation.Equality.Prop.EDSL.Test where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL

{-
-- test :: [a] -> [EqualityProp a] -> Q Chain
-- test [t1, t2, t3, t4, t5, t6] [e12, e23, e34, e45, e56] =

testChainString :: String
testChainString =
  "t1\
  \%eqprop\
  \t2\
  \%by e12\
  \%eqprop\
  \t3\
  \%by e23\
  \%eqprop\
  \t4\
  \%by e34\
  \%eqprop\
  \t5\
  \%by e45\
  \%eqprop\
  \t6\
  \%by e56"

testChainQ = parseChain testChainString

-- testChain :: Chain
-- testChain =
--   Chain
--     (VarE t1)
--     [ ChainClause (VarE t2) (ChainExpln_Proof (VarE e12)),
--       ChainClause (VarE t3) (ChainExpln_Proof (VarE e23)),
--       ChainClause (VarE t4) (ChainExpln_Proof (VarE e34)),
--       ChainClause (VarE t5) (ChainExpln_Proof (VarE e45)),
--       ChainClause (VarE t6) (ChainExpln_Proof (VarE e56))
--     ]

testChainExpQ = compileChain testChainString

-- testChainExp =
--   AppE
--     ( AppE
--         ( AppE
--             ( AppE
--                 ( AppE
--                     (VarE Relation.Equality.Prop.transitivity)
--                     (VarE t1)
--                 )
--                 (VarE t5)
--             )
--             (VarE t6)
--         )
--         ( AppE
--             ( AppE
--                 ( AppE
--                     ( AppE
--                         ( AppE
--                             (VarE Relation.Equality.Prop.transitivity)
--                             (VarE t1)
--                         )
--                         (VarE t4)
--                     )
--                     (VarE t5)
--                 )
--                 ( AppE
--                     ( AppE
--                         ( AppE
--                             ( AppE
--                                 ( AppE
--                                     (VarE Relation.Equality.Prop.transitivity)
--                                     (VarE t1)
--                                 )
--                                 (VarE t3)
--                             )
--                             (VarE t4)
--                         )
--                         ( AppE
--                             ( AppE
--                                 ( AppE
--                                     ( AppE
--                                         ( AppE
--                                             (VarE Relation.Equality.Prop.transitivity)
--                                             (VarE t1)
--                                         )
--                                         (VarE t2)
--                                     )
--                                     (VarE t3)
--                                 )
--                                 (VarE e12)
--                             )
--                             (VarE e23)
--                         )
--                     )
--                     (VarE e23)
--                 )
--             )
--             (VarE e34)
--         )
--     )
--     (VarE e45)

Relation.Equality.Prop.transitivity
  t1
  t5
  t6
  ( Relation.Equality.Prop.transitivity
      t1
      t4
      t5
      ( Relation.Equality.Prop.transitivity
          t1
          t3
          t4
          ( Relation.Equality.Prop.transitivity
              t1
              t2
              t3
              e12
              e23
          )
          e34
      )
      e45
  )
  e56
-}
