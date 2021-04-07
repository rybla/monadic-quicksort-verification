{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Relation.Equality.Prop.EDSL
  ( eqpropchain,
    compileChain,
    parseChain,
    Chain (..),
    ChainClause (..),
    ChainExpln (..),
  )
where

import Control.Applicative
import Control.Monad
import Data.Char
import qualified Data.Char as Char
import Data.List
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Meta.Parse as MP
import Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Relation.Equality.Prop
import qualified Text.Parsec as P
import Text.Printf (printf)

sym_eqprop, sym_expln, sym_rewrite, sym_rewrite_to, sym_reflexivity, sym_symmetry, sym_extend, sym_retract, sym_smt :: String
sym_eqprop = "%eqprop"
sym_expln = "%by"
sym_rewrite = "%rewrite"
sym_rewrite_to = "%to"
sym_reflexivity = "%reflexivity"
sym_symmetry = "%symmetry"
sym_extend = "%extend"
sym_retract = "%retract"
sym_smt = "%smt"

syms_expln :: [String]
syms_expln = [sym_reflexivity, sym_symmetry, sym_rewrite, sym_extend, sym_retract, sym_smt]

data Chain = Chain Exp [ChainClause]
  deriving (Show)

data ChainClause = ChainClause Exp ChainExpln
  deriving (Show)

-- explanation
data ChainExpln
  = ChainExpln_Trivial
  | ChainExpln_Proof Exp -- %by <proof>
  | ChainExpln_Reflexivity -- %by %reflexivity
  | ChainExpln_Symmetry ChainExpln -- %by %symmetry %by <clause>
  | ChainExpln_Rewrite Exp Exp ChainExpln -- %by %rewrite <exp> %to <exp> %by <clause>
  | ChainExpln_Extend Name ChainExpln -- %by %extend <exp> %by <clause>
  | ChainExpln_Retract Name ChainExpln -- %by %retract <exp> %by <clause>
  | ChainExpln_SMT Exp -- %by %smt %by <exp>
  deriving (Show)

instance Lift Exp where
  lift = return
  liftTyped = unsafeTExpCoerce . lift

instance Lift Chain where
  -- lift :: Chain -> Q Exp
  lift (Chain t1 _clauses) = go (reverse _clauses)
    where
      go :: [ChainClause] -> Q Exp
      go [] = do
        [|reflexivity t1|]
      go (ChainClause t2 expln : []) = do
        e12 <- reifyExpln t1 t2 expln
        [|transitivity t1 t2 t2 e12 (reflexivity t2)|]
      go (ChainClause t3 expln23 : ChainClause t2 expln12 : []) = do
        e12 <- reifyExpln t1 t2 expln12
        e23 <- reifyExpln t2 t3 expln23
        [|transitivity t1 t2 t3 e12 e23|]
      go (ChainClause tk explnjk : ChainClause tj explnij : clauses) = do
        e1j <- go (ChainClause tj explnij : clauses)
        ejk <- reifyExpln tj tk explnjk
        [|transitivity t1 tj tk e1j ejk|]

      reifyExpln :: Exp -> Exp -> ChainExpln -> Q Exp
      reifyExpln ti tj = \case
        ChainExpln_Trivial ->
          [|trivialProp|]
        ChainExpln_Proof eij ->
          [|eij|]
        ChainExpln_Reflexivity ->
          [|reflexivity ti|]
        ChainExpln_Symmetry expln -> do
          eji <- reifyExpln ti tj expln
          [|symmetry tj ti eji|]
        ChainExpln_Rewrite s3 s4 expln -> do
          e34 <- reifyExpln s3 s4 expln
          rewrite [|s3|] [|s4|] [|e34|] [|ti|]
        ChainExpln_Extend x expln -> do
          let ti_x = AppE ti (VarE x)
          let tj_x = AppE tj (VarE x)
          eij_x <- reifyExpln ti_x tj_x expln
          let eij = LamE [VarP x] eij_x
          [|extensionality ti tj eij|]
        ChainExpln_Retract x expln -> do
          -- TODO: is ChainExpln_Retract even defined well?
          undefined
        ChainExpln_SMT eSMTij ->
          [|(reflexivity ti ? eSMTij)|]

  -- liftTyped :: Chain -> Q TExp
  liftTyped = unsafeTExpCoerce . lift

eqpropchain :: QuasiQuoter
eqpropchain =
  QuasiQuoter
    { quoteExp = compileChain,
      quotePat = undefined,
      quoteType = undefined,
      quoteDec = undefined
    }

compileChain :: String -> Q Exp
compileChain s = do
  chain <- parseChain s
  [|chain|]

parseChain :: String -> Q Chain
parseChain s = do
  clauses <- traverse parseChainClause . split sym_eqprop $ s
  case clauses of
    [] ->
      fail "empty eqpropchain"
    [ChainClause tm expln] ->
      return $ Chain tm [ChainClause tm expln]
    (ChainClause tm ChainExpln_Trivial : clauses) ->
      return $ Chain tm clauses
    (ChainClause tm _ : clauses) ->
      fail $ printf "first eqpropchain clause cannot have explanation: `%s`" s

parseChainClause :: String -> Q ChainClause
parseChainClause sClause = case splitFirst sym_expln (dropSpace sClause) of
  Just (sTm, expln) -> ChainClause <$> parseExpQ sTm <*> parseChainExpln expln
  Nothing -> ChainClause <$> parseExpQ sClause <*> return ChainExpln_Trivial

parseChainExpln :: String -> Q ChainExpln
parseChainExpln sExpln =
  case foldl (<|>) Nothing $
    map (\sym -> (sym,) <$> stripPrefix sym (dropSpace sExpln)) syms_expln of
    --
    Just (sym, sExpln1) ->
      if
          -- %reflexivity
          | sym == sym_reflexivity -> do
            parseCmdEnd sym sExpln1
            return ChainExpln_Reflexivity
          -- %symmetry %by <expln>
          | sym == sym_symmetry -> do
            sExpln2 <- parseCmd sym_expln sExpln1
            expln <- parseChainExpln sExpln2
            return $ ChainExpln_Symmetry expln
          -- %rewrite <exp> %to <exp> %by <expln>
          | sym == sym_rewrite -> do
            (sTm1, sExpln2) <- parseToCmd sym_rewrite_to sExpln1
            (sTm2, sExpln3) <- parseToCmd sym_expln sExpln2
            tm1 <- parseExpQ sTm1
            tm2 <- parseExpQ sTm2
            expln <- parseChainExpln sExpln3
            return $ ChainExpln_Rewrite tm1 tm2 expln
          -- %extend <name> %by <expln>
          | sym == sym_extend -> do
            (sName, sExpln2) <- parseToCmd sym_expln sExpln1
            name <-
              parseExpQ sName >>= \case
                VarE name -> return name
                e -> fail $ printf "the eqpropchain command `%s` expects a <name> argument instead of `%s`" sym (show e)
            expln <- parseChainExpln sExpln2
            return $ ChainExpln_Extend name expln
          -- %retract <name> %by <expln>
          | sym == sym_retract -> do
            (sName, sExpln2) <- parseToCmd sym_expln sExpln1
            name <-
              parseExpQ sName >>= \case
                VarE name -> return name
                e -> fail $ printf "the eqpropchain command `%s` expects a <name> argument instead of `%s`" sym (show e)
            expln <- parseChainExpln sExpln2
            return $ ChainExpln_Retract name expln
          -- %smt %by <exp>
          | sym == sym_smt -> do
            sTm <- parseCmd sym_expln sExpln1
            tm <- parseExpQ sTm
            return $ ChainExpln_SMT tm
          | otherwise ->
            fail $ printf "the eqpropchain command `%s` is not implemented" sym
    --
    Nothing ->
      ChainExpln_Proof <$> parseExpQ sExpln
  where
    parseToCmd :: String -> String -> Q (String, String)
    parseToCmd cmd str = case splitFirst cmd (dropSpace str) of
      Just (str1, str2) -> return (str1, str2)
      Nothing -> fail $ printf "expected expression followed by eqpropchain command `%s` instead of `%s`" cmd str
    parseCmd :: String -> String -> Q String
    parseCmd cmd str = case stripPrefix cmd (dropSpace str) of
      Just str' -> return str'
      Nothing -> fail $ printf "expected eqpropchain command `%s` instead of `%s`" cmd str
    parseCmdEnd :: String -> String -> Q ()
    parseCmdEnd cmd str =
      unless (all isSpace str) $
        fail $ printf "eqpropchain command `%s` does not expect argument `%s`" cmd str

parseExpQ :: String -> Q Exp
parseExpQ s = case parseExp s of
  Left err -> fail err
  Right exp -> return exp

-- x:a -> y:a -> EqualProp a {x} {y} -> e:c -> EqualProp b {f x} {f y}
-- where f is extracted from e by abstracting out the appearances of x
rewrite :: Q Exp -> Q Exp -> Q Exp -> Q Exp -> Q Exp
rewrite xQ yQ exyQ eQ = do
  x <- xQ
  e <- eQ
  holeName <- newName "rewrite_hole"
  let extract :: Exp -> Q Exp
      extract _e =
        if _e == x
          then varE holeName
          else case _e of
            AppE e1 e2 -> AppE <$> extract e1 <*> extract e2
            AppTypeE e t -> AppTypeE <$> extract e <*> return t
            InfixE mb_e1 e2 mb_e3 -> InfixE <$> traverse extract mb_e1 <*> extract e2 <*> traverse extract mb_e3
            UInfixE e1 e2 e3 -> UInfixE <$> extract e1 <*> extract e2 <*> extract e3
            ParensE e -> ParensE <$> extract e
            LamE pats e -> LamE pats <$> extract e
            LamCaseE mats -> LamCaseE <$> traverse extractMatch mats
            TupE mb_es -> TupE <$> (traverse . traverse) extract mb_es
            UnboxedTupE mb_es -> UnboxedTupE <$> (traverse . traverse) extract mb_es
            UnboxedSumE e i1 i2 -> UnboxedSumE <$> extract e <*> return i1 <*> return i2
            CondE e1 e2 e3 -> CondE <$> extract e1 <*> extract e2 <*> extract e3
            MultiIfE grds_es -> MultiIfE <$> traverse extractGuardExp grds_es
            LetE decs e -> LetE <$> traverse extractDec decs <*> extract e
            CaseE e mats -> CaseE <$> extract e <*> traverse extractMatch mats
            DoE stmts -> DoE <$> traverse extractStmt stmts
            MDoE stmts -> MDoE <$> traverse extractStmt stmts
            CompE stmts -> CompE <$> traverse extractStmt stmts
            ArithSeqE rng -> ArithSeqE <$> extractRange rng
            ListE es -> ListE <$> traverse extract es
            SigE e t -> SigE <$> extract e <*> return t
            RecConE n ns_es -> RecConE n <$> (traverse . traverse) extract ns_es
            RecUpdE e ns_es -> RecUpdE <$> extract e <*> (traverse . traverse) extract ns_es
            StaticE e -> StaticE <$> extract e
            _ -> return _e
      extractStmt :: Stmt -> Q Stmt
      extractStmt = \case
        BindS pat e -> BindS pat <$> extract e
        LetS decs -> LetS <$> traverse extractDec decs
        NoBindS e -> NoBindS <$> extract e
        ParS stmtss -> ParS <$> (traverse . traverse) extractStmt stmtss
        RecS stmts -> RecS <$> traverse extractStmt stmts
      extractDec :: Dec -> Q Dec
      extractDec = \case
        FunD n clauses -> FunD n <$> traverse extractClause clauses
        ValD pat bod decs -> ValD pat <$> extractBody bod <*> traverse extractDec decs
        ClassD cxt n tybs fundeps decs -> ClassD cxt n tybs fundeps <$> traverse extractDec decs
        InstanceD overlap cxt ty decs -> InstanceD overlap cxt ty <$> traverse extractDec decs
        ImplicitParamBindD str e -> ImplicitParamBindD str <$> extract e
        dec -> return dec
      extractBody :: Body -> Q Body
      extractBody = \case
        GuardedB grds_es -> GuardedB <$> traverse extractGuardExp grds_es
        NormalB e -> NormalB <$> extract e
      extractGuard :: Guard -> Q Guard
      extractGuard = \case
        NormalG e -> NormalG <$> extract e
        PatG stmts -> PatG <$> traverse extractStmt stmts
      extractRange :: Range -> Q Range
      extractRange = \case
        FromR e -> FromR <$> extract e
        FromThenR e1 e2 -> FromThenR <$> extract e1 <*> extract e2
        FromToR e1 e2 -> FromToR <$> extract e1 <*> extract e2
        FromThenToR e1 e2 e3 -> FromThenToR <$> extract e1 <*> extract e2 <*> extract e3
      extractClause :: Clause -> Q Clause
      extractClause (Clause pats bod decs) = Clause pats <$> extractBody bod <*> traverse extractDec decs
      extractMatch :: Match -> Q Match
      extractMatch (Match pat bod decs) = Match pat <$> extractBody bod <*> traverse extractDec decs
      extractGuardExp :: (Guard, Exp) -> Q (Guard, Exp)
      extractGuardExp (grd, e) = (,) <$> extractGuard grd <*> extract e
  --
  f <- [|$(lamE [varP holeName] (extract e))|]
  [|(((substitutability (apply f) $xQ $yQ $exyQ) ? apply f $xQ) ? apply f $yQ)|]

--
--
--

split :: String -> String -> [String]
split sep _str = go _str ""
  where
    go "" "" = []
    go "" wrk = [wrk]
    go str@(c : str') wrk = case stripPrefix sep str of
      Just str2 -> wrk : go str2 ""
      Nothing -> go str' (wrk ++ [c])

splitFirst :: String -> String -> Maybe (String, String)
splitFirst sep _str = go _str ""
  where
    go str wrk =
      case stripPrefix sep str of
        Just str' -> Just (wrk, str')
        Nothing ->
          case str of
            "" -> Nothing
            (c : str') -> go str' (wrk ++ [c])

dropSpace :: String -> String
dropSpace = dropWhile Char.isSpace

--
--
--
