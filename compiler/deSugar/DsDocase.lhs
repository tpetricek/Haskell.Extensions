%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%

Desugaring docase notation

\begin{code}
module DsDocase ( dsDocaseExpr ) where

#include "HsVersions.h"

import Match
import DsUtils
import DsMonad

import HsSyn	hiding (collectPatBinders, collectPatsBinders )
import TcHsSyn
import {-# SOURCE #-} DsExpr ( dsExpr, dsLExpr ) --, dsLocalBinds )

--import TcType
import Type
import CoreSyn
--import CoreFVs
import CoreUtils
import MkCore

--import Name
import Var
--import Id
--import DataCon
import TysWiredIn
import BasicTypes
--import PrelNames
import Outputable
--import Bag
--import VarSet
import SrcLoc

--import Data.List
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Control.Monad
\end{code}

%************************************************************************
%*                                                                      *
		Docase
%*                                                                      *
%************************************************************************

\begin{code}
dsDocaseExpr :: (DocaseGroup TcId) -> DsM CoreExpr
dsDocaseExpr (DocaseGroup args clauses bind_op) = do {
    
    ; newArgs <- mapM (\(idx, (arg, (abind_op, aalias_op))) -> do {
        ; arg' <- dsLExpr arg
        ; avar <- newSysLocalDs (exprType arg')
        ; let trans = \body -> do {
            ; aalias_op' <- dsExpr aalias_op
            ; abind_op' <- dsExpr abind_op
            ; return $ mkApps abind_op' [mkApps aalias_op' [arg'], Lam avar body] }
        ; return (idx, (avar, trans)) }) (Map.toList args)

      -- Translate all clauses separately and combine them using 'morelse'
    ; let args' = Map.fromList [ (idx, Var avar) | (idx, (avar, _)) <- newArgs ]
    ; clauseExpr <- dsOrElseClauses args' clauses

      -- Add '>>= \freeVar -> freeVar' at the end to unwrap the body
	; bind_op' <- dsExpr bind_op 
    ; let idArgTy = typeOfBindBody bind_op'
    ; idVar <- newSysLocalDs idArgTy
    ; let body = mkApps bind_op' [clauseExpr, Lam idVar (Var idVar)] 
    ; foldM (\ inBody (_, (_, trans)) -> trans inBody ) body newArgs }

  where 
    dsOrElseClauses args [clause] =
        dsDocaseClause args clause

    dsOrElseClauses args (clause@(DocaseClause _ _ _ (Just morelse_op) _):tail) = do {
        ; e1 <- dsDocaseClause args clause
        ; e2 <- dsOrElseClauses args tail
        ; morelse_op' <- dsExpr morelse_op
        ; return $ mkApps morelse_op' [e1, e2] }
    
    dsDocaseClause args (DocaseClause pats patTy (cbind_op, cret_op, czero_op) morelse_op body) = do {
        ; cbind_op' <- dsExpr cbind_op

          -- Create expression that zips desugared arguments
        ; inputArgs <- dsZipArgs args pats 

          -- Create a function that performs the pattern matching
          -- '(\ freshVar -> case freshVar of 
          --    (p1, (p2, (..))) -> return $ <body>;   _ -> fail "!")
        ; inpVar <- newSysLocalDs patTy
        ; let pat = foldr1 mkTuplePattern [ p | (_, p, _) <- pats ]
        ; body' <- dsLExpr body
        
          -- Construct the body for successful case & create 'case' expression
        ; cret_op' <- dsExpr cret_op
        ; let bindBody = cantFailMatchResult $ mkCoreApp cret_op' body'
        ; match <- matchSinglePat (Var inpVar) DocaseAlt pat (typeOfBindBody cbind_op') bindBody
          -- Add case that handles match failure 
	    ; match_code <- handle_failure pat match czero_op

        ; return $ mkApps cbind_op' [inputArgs, Lam inpVar match_code] }


    mkTuplePattern p1 p2 =
      let tupTy = mkBoxedTupleTy [hsLPatType p1, hsLPatType p2] 
      in L (combineLocs p1 p2) (TuplePat [p1, p2] Boxed tupTy)

    -- Returns the type at the location T3 in 'T1 -> (T2 -> T3) -> T4'
    typeOfBindBody expr = 
        funResultTy (funArgTy (funResultTy (exprType expr)))

    dsZipArgs args [(idx, pat, _)] = return $ args Map.! idx

    dsZipArgs args ((idx, pat, Just mzip_op):tail) = do {
        ; let e1 = args Map.! idx
        ; e2 <- dsZipArgs args tail
        ; mzip_op' <- dsExpr mzip_op
        ; return $ mkApps mzip_op' [e1, e2] }

    dsZipArgs _ _ = error "zip args - should not happen (mzip missing or zero patterns)"


-- ***************** Copied from DsExpr *****************

handle_failure :: LPat Id -> MatchResult -> SyntaxExpr Id -> DsM CoreExpr
    -- In a do expression, pattern-match failure just calls
    -- the monadic 'fail' rather than throwing an exception
handle_failure pat match fail_op
  | matchCanFail match
  = do { fail_op' <- dsExpr fail_op
       ; extractMatchResult match (fail_op') }
  | otherwise
  = extractMatchResult match (error "It can't fail")
\end{code}
