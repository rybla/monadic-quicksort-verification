{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Relation.Equality.Prop.EDSL.Test where

import Data.Refined.Natural
import Function
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import Relation.Equality.Prop.EDSL

{-@ reflect test1_aux1 @-}
test1_aux1 :: Natural -> Natural
test1_aux1 x = add x (S Z)

{-@ reflect test1_aux2 @-}
test1_aux2 :: Natural -> Natural
test1_aux2 x = add (S Z) x

{-@
test1 ::
  Equality (Natural -> Natural) =>
  EqualProp (Natural -> Natural)
    {test1_aux1}
    {test1_aux2}
@-}
test1 :: Equality (Natural -> Natural) => EqualityProp (Natural -> Natural)
test1 =
  transitivity
    test1_aux1
    (apply (\x -> add x (S Z)))
    test1_aux2
    ( transitivity
        test1_aux1
        (apply (\x -> test1_aux1 x))
        (apply (\x -> add x (S Z)))
        trivialProp
        undefined
        -- ( extensionality
        --     (apply (\x -> test1_aux1 x))
        --     (apply (\x -> add x (S Z)))
        --     (\x -> (?) ((?) (reflexivity (apply (\x -> test1_aux1 x) x)) (apply (\x -> test1_aux1 x) x)) (apply (\x -> add x (S Z)) x))
        -- )
    )
    undefined

{-
{-@
test2 ::
  (Equality (Natural -> Natural), Equality Natural) =>
  EqualProp (Natural -> Natural)
    {apply (\x:Data.Refined.Natural.Natural -> test1_aux1 x)}
    {apply (\x:Data.Refined.Natural.Natural -> add x (S Z))}
@-}
test2 :: (Equality (Natural -> Natural), Equality Natural) => EqualityProp (Natural -> Natural)
test2 =
  extensionality
    (apply (\x -> test1_aux1 x))
    (apply (\x -> add x (S Z)))
    test2_lemma

{-@
test2_lemma :: Equality Natural => x:Natural -> EqualProp Natural {test1_aux1 x} {add x (S Z)}
@-}
test2_lemma :: Equality Natural => Natural -> EqualityProp Natural
test2_lemma x = reflexivity (test1_aux1 x) ? undefined
-}

{-
  [eqpropchain|
      test1_aux1
    %==
      apply (\x -> test1_aux1 x)
    %==
      apply (\x -> add x (S Z))
        %by %extend x
        %by %reflexivity
    %==
      test1_aux2
        %by undefined
  |]
-}

-- test1_exp =
--   compileChain
--     "test1_aux1\
--     \%==\
--     \apply (\\x -> test1_aux1 x)\
--     \%==\
--     \apply (\\x -> add x (S Z))\
--     \%by %extend x \
--     \%by %reflexivity \
--     \%==\
--     \test1_aux2\
--     \%by undefined"

-- _ =
--   Chain
--     (VarE test1_aux1)
--     [ ChainClause
--         ( AppE
--             (VarE apply)
--             ( ParensE
--                 ( LamE
--                     [VarP x]
--                     ( AppE
--                         (VarE test1_aux1)
--                         (VarE x)
--                     )
--                 )
--             )
--         )
--         ChainExpln_Trivial,
--       ChainClause
--         ( AppE
--             (VarE apply)
--             ( ParensE
--                 ( LamE
--                     [VarP x]
--                     ( AppE
--                         ( AppE
--                             (VarE add)
--                             (VarE x)
--                         )
--                         ( ParensE
--                             ( AppE
--                                 (ConE S)
--                                 (ConE Z)
--                             )
--                         )
--                     )
--                 )
--             )
--         )
--         (ChainExpln_Extend (VarP x) ChainExpln_Reflexivity),
--       ChainClause (VarE test1_aux2) (ChainExpln_Proof (VarE undefined))
--     ]

{-
-- test :: [a] -> [EqualityProp a] -> Q Chain
-- test [t1, t2, t3, t4, t5, t6] [e12, e23, e34, e45, e56] =

testChainString :: String
testChainString =
  "t1\
  \%==\
  \t2\
  \%by e12\
  \%==\
  \t3\
  \%by e23\
  \%==\
  \t4\
  \%by e34\
  \%==\
  \t5\
  \%by e45\
  \%==\
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
--                     (VarE transitivity)
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
--                             (VarE transitivity)
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
--                                     (VarE transitivity)
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
--                                             (VarE transitivity)
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

transitivity
  t1
  t5
  t6
  ( transitivity
      t1
      t4
      t5
      ( transitivity
          t1
          t3
          t4
          ( transitivity
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
