%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
Typecheck docase notation

\begin{code}
module TcDocase ( tcDocase ) where

import {-# SOURCE #-}	TcExpr( tcSyntaxOp, tcMonoExpr, tcPolyExpr )
import Data.Maybe (fromMaybe)
import Control.Monad (liftM)

import HsSyn
--import TcMatches
import TcType
import TcMType
--import TcBinds
import TcPat
--import TcUnify
import TcRnMonad
--import TcEnv
--import Coercion
--import Id( mkLocalId )
--import Inst
import Name
import TysWiredIn
--import VarSet 
import TysPrim

import SrcLoc
--import Outputable
--import FastString
--import Util

--import Control.Monad
import qualified Data.Map as Map
import Data.Maybe (fromJust)
\end{code}

%************************************************************************
%*                                                                      *
		Docase
%*                                                                      *
%************************************************************************


\begin{code}


tcDocase :: (DocaseGroup Name) -> TcRhoType -> TcM (DocaseGroup TcId)
tcDocase (DocaseGroup args clauses bind_global_op) resTy = do {

      -- Add types to arguments and store them in a temporary list
      -- Also specify the type of 'malias' for each argument.
    ; argsList' <- mapM (\ (idx, (arg, (bind_op, malias_op) )) -> do {
        ; argTy      <- newFlexiTyVarTy liftedTypeKind
        ; arg'       <- tcMonoExpr arg argTy 
        ; aliasedTy <- newFlexiTyVarTy liftedTypeKind
        ; malias_op' <- tcSyntaxOp DocaseOrigin malias_op (mkFunTy argTy aliasedTy)
        ; bind_op'   <- tcSyntaxOp DocaseOrigin bind_op (mkFunTys [aliasedTy, mkFunTy argTy resTy] resTy)
        ; return (idx, (arg', argTy, (bind_op', malias_op') )) }) (Map.toList args)
    
      -- Type-check clauses. Clause with body of type (m a) has a 
      -- type (m (m a)), which is shared by all clauses.
    ; clauseTy <- newFlexiTyVarTy liftedTypeKind
    ; bodyTy <- newFlexiTyVarTy liftedTypeKind
    ; clauses' <- mapM (tcDocaseClause (Map.fromList argsList') clauseTy bodyTy) clauses

      -- Specify the type instatiation for '>>= id' call at the end
    ; bind_global_op' <- tcSyntaxOp DocaseOrigin bind_global_op (mkFunTys [clauseTy, mkFunTy bodyTy bodyTy] resTy)

      -- Create arguments map & return type-checked DocaseGroup
    ; let args' = Map.fromList [ (i, (a, mop)) | (i, (a, _, mop)) <- argsList' ]
    ; return $ DocaseGroup args' clauses' bind_global_op' }

  where 
    -- Type checking of a single clause. We are provided with the expected body 
    -- type (bodyTy) and the clause type which wraps 'bodyTy' in an additional monad.
    tcDocaseClause argsMap clauseTy bodyTy (DocaseClause pats _ bind_ops (Just morelse_op) body) = do {

          -- Type check patterns and then the body in the inner scope
        ; (pats', patTy', zippedTy, body') <- tcDocaseClausePats argsMap pats $ do {
            ; body' <- tcMonoExpr body bodyTy
            ; return body' }

          -- Type instantiation for operations used to translate the clause
        ; let (cbind_op, cret_op, czero_op) = bind_ops 
        ; cbind_op' <- tcSyntaxOp DocaseOrigin cbind_op (mkFunTys [zippedTy, mkFunTy patTy' clauseTy] clauseTy)
        ; cret_op'  <- tcSyntaxOp DocaseOrigin cret_op  (mkFunTy bodyTy clauseTy)
        ; czero_op' <- tcSyntaxOp DocaseOrigin czero_op clauseTy
        ; let bind_ops' = (cbind_op', cret_op', czero_op')

          -- Instantiation of 'morelse' used to combine the clauses
        ; morelse_op' <- tcSyntaxOp DocaseOrigin morelse_op (mkFunTys [clauseTy, clauseTy] clauseTy)        
        ; return $ DocaseClause pats' patTy' bind_ops' (Just morelse_op') body' }


    -- Type checking of 'e1 `mzip` (e2 `mzip` e3) >>= (p1, (p2, p3)) -> ...'
    -- Type-checks current pattern; in the continuation recursively processes
    -- the rest of patterns. It takes the type of the zipped monadic expression
    -- and returns: new list of patterns, type of composed pattern, type-checked body.
    tcDocaseClausePats args ((idx, pat, mzip_op):tail) cont = do {

        -- Get the type of corresponding argument
      ; let (_, argTy, _) = args Map.! idx

        -- Create type for pattern & type-check (using 'pat :: patTy')
        -- Then recursively type-check remaining patterns and body (thing)
      ; patTy <- newFlexiTyVarTy liftedTypeKind
      
      ; case tail of
          [] -> do {
              -- Type-check the last pattern of a clause (nothing to zip with)
            ; (pat', thing) <- tcPat DocaseAlt pat patTy $ cont
            
              -- Construct results
            ; let pats = [(idx, pat', Nothing)]
            ; return (pats, patTy, argTy, thing) }

          _:_ -> do {
              -- Type-check pattern that is not last (zip with the rest)
            ; (pat', (tail', tailPatTy, tailArgTy, thing)) <- tcPat DocaseAlt pat patTy $ 
                tcDocaseClausePats args tail cont 

              -- Type-check mzip using:  arg (`mzip` :: argTy -> tailArgTy -> zippedTy) tail
            ; zippedTy <- newFlexiTyVarTy liftedTypeKind
            ; mzip_op' <- tcSyntaxOp DocaseOrigin (fromJust mzip_op) (mkFunTys [argTy, tailArgTy] zippedTy)

              -- Construct results
            ; let pats = (idx, pat', Just mzip_op'):tail'
            ; let combinedPatTy = mkBoxedTupleTy [ patTy, tailPatTy ]
            ; return (pats, combinedPatTy, zippedTy, thing) } }

    -- There must be at least one pattern    
    tcDocaseClausePats _ [] _ = error "No patterns in clause" -- TODO: nice error message

\end{code}