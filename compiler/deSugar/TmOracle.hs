
{-
  Author: George Karachalias <george.karachalias@cs.kuleuven.be>
-}

{-# OPTIONS_GHC -Wwarn #-}   -- unused variables
{-# LANGUAGE CPP, MultiWayIf #-}

module TmOracle (

        -- re-exported from PmExpr
        PmExpr(..), PmLit(..), SimpleEq, ComplexEq, PmVarEnv, falsePmExpr,
        notForced, eqPmLit, filterComplex, isNotPmExprOther, runPmPprM,
        pprPmExprWithParens, lhsExprToPmExpr, hsExprToPmExpr,

        -- the term oracle
        tmOracle, TmState, initialTmState,

        -- misc.
        exprDeepLookup, pmLitType, flattenPmVarEnv
    ) where

#include "HsVersions.h"

import PmExpr

import Id
import TysWiredIn
import Type    -- ( Type )
import HsLit   -- overLitType
import TcHsSyn -- hsLitType
-- import FastString -- sLit
-- import Outputable
import MonadUtils
import Util

import qualified Data.Map as Map
-- import Data.Maybe

{-
%************************************************************************
%*                                                                      *
\subsection{The term equality oracle}
%*                                                                      *
%************************************************************************
-}

-- ----------------------------------------------------------------------------
-- | Oracle Types

type PmVarEnv = Map.Map Id PmExpr

-- | The environment of the oracle contains
--     1. A boolean value (are there any constraints we cannot handle? (PmExprOther stuff)).
--     2. A substitution we extend with every step and return as a result.
type TmOracleEnv = (Bool, PmVarEnv)


-- | Check whether a variable has been refined to (at least) a WHNF
notForced :: Id -> PmVarEnv -> Bool
notForced x env = case varDeepLookup env x of
  PmExprVar _ -> True
  _other_expr -> False

-- | Flatten the DAG. (Could be improved in terms of performance)
flattenPmVarEnv :: PmVarEnv -> PmVarEnv
flattenPmVarEnv env = Map.map (exprDeepLookup env) env

-- ----------------------------------------------------------------------------

type TmState = ([ComplexEq], TmOracleEnv)  -- constraints that cannot be solved yet (we need more info) and subst

initialTmState :: TmState
initialTmState = ([], (False, Map.empty))

solveSimpleEq :: TmState -> SimpleEq -> Maybe TmState
solveSimpleEq solver_env@(_,(_,env)) simple
  = solveComplexEq solver_env -- do the actual *merging* with existing solver state
  $ simplifyComplexEq          -- simplify as much as you can
  $ applySubstSimpleEq env simple -- replace everything we already know

solveComplexEq :: TmState -> ComplexEq -> Maybe TmState
solveComplexEq solver_state@(standby, (unhandled, env)) eq@(e1, e2) = case eq of
  -- We cannot do a thing about these cases
  (PmExprOther _,_)            -> Just (standby, (True, env))
  (_,PmExprOther _)            -> Just (standby, (True, env))
  -- Look at the catch-all.. (PmExprLit _, PmExprCon _ _) -> Just (standby, (eq:unhandled, env))
  -- Look at the catch-all.. (PmExprCon _ _, PmExprLit _) -> Just (standby, (eq:unhandled, env))
  -- Look at the catch-all.. (PmExprLit _, PmExprEq _ _)  -> Just (standby, (eq:unhandled, env))
  -- Look at the catch-all.. (PmExprEq _ _, PmExprLit _)  -> Just (standby, (eq:unhandled, env))

  (PmExprLit l1, PmExprLit l2) -> case eqPmLit l1 l2 of
    Just True  -> Just solver_state           -- we are sure: equal
    Just False -> Nothing                     -- we are sure: not equal
    -- Maybe just drop. We use this boolean to check also whether something is forced and I know
    -- that nothing is if both are literals. Hence, just assume true and give (Just solver_state)?
    Nothing    -> Just (standby, (True, env)) -- no clue (and won't get one)!

  (PmExprCon c1 ts1, PmExprCon c2 ts2)
    | c1 == c2  -> foldlM solveComplexEq solver_state (zip ts1 ts2)
    | otherwise -> Nothing
  (PmExprCon c [], PmExprEq t1 t2)
    | c == trueDataCon  -> solveComplexEq solver_state (t1, t2)
    | c == falseDataCon -> Just (eq:standby, (unhandled, env))
  (PmExprEq t1 t2, PmExprCon c [])
    | c == trueDataCon  -> solveComplexEq solver_state (t1, t2)
    | c == falseDataCon -> Just (eq:standby, (unhandled, env))

  (PmExprVar x, PmExprVar y)
    | x == y    -> Just solver_state
    | otherwise -> extendSubstAndSolve x e2 solver_state {- CHOOSE ONE AND EXTEND SUBST & LOOK AT STB -}

  (PmExprVar x, _) -> extendSubstAndSolve x e2 solver_state {- EXTEND SUBST & LOOK AT STB -}
  (_, PmExprVar x) -> extendSubstAndSolve x e1 solver_state {- EXTEND SUBST & LOOK AT STB -}
  -- (PmExprVar x, PmExprCon {}) -> extendSubstAndSolve x e2 solver_state {- EXTEND SUBST & LOOK AT STB -}
  -- (PmExprCon {}, PmExprVar x) -> extendSubstAndSolve x e1 solver_state {- EXTEND SUBST & LOOK AT STB -}
  -- (PmExprVar x, PmExprLit {}) -> extendSubstAndSolve x e2 solver_state {- EXTEND SUBST & LOOK AT STB -}
  -- (PmExprLit {}, PmExprVar x) -> extendSubstAndSolve x e1 solver_state {- EXTEND SUBST & LOOK AT STB -}
  -- (PmExprVar x,  PmExprEq {}) -> extendSubstAndSolve x e2 solver_state {- EXTEND SUBST & LOOK AT STB -}
  -- (PmExprEq  {}, PmExprVar x) -> extendSubstAndSolve x e1 solver_state {- EXTEND SUBST & LOOK AT STB -}

  (PmExprEq _ _, PmExprEq _ _) -> Just (eq:standby, (unhandled, env))

  _ -> Just (standby, (True, env)) -- I HATE CATCH-ALLS

extendSubstAndSolve :: Id -> PmExpr -> TmState -> Maybe TmState
extendSubstAndSolve x e (standby, (unhandled, env))
  = foldlM solveComplexEq new_incr_state changed
  where
    (changed, unchanged) = partitionWith (substComplexEq x e) standby  -- apply substitution to residual to see if there is any progress. leave the unchanged ones behind
    new_incr_state       = (unchanged, (unhandled, Map.insert x e env)) -- extend the substitution.

simplifyComplexEq :: ComplexEq -> ComplexEq
simplifyComplexEq (e1, e2) = (fst $ simplifyPmExpr e1, fst $ simplifyPmExpr e2)

simplifyPmExpr :: PmExpr -> (PmExpr, Bool) -- may we need more?
simplifyPmExpr e = case e of
  PmExprCon c ts -> case mapAndUnzip simplifyPmExpr ts of
                      (ts', bs) -> (PmExprCon c ts', or bs)
  PmExprEq t1 t2 -> simplifyEqExpr t1 t2
  _other_expr    -> (e, False) -- the others are terminals

simplifyEqExpr :: PmExpr -> PmExpr -> (PmExpr, Bool) -- deep equalities
simplifyEqExpr e1 e2 = case (e1, e2) of
  -- Varables
  (PmExprVar x, PmExprVar y)
    | x == y -> (truePmExpr, True)

  -- Literals
  (PmExprLit l1, PmExprLit l2) -> case eqPmLit l1 l2 of
    Just True  -> (truePmExpr,  True)
    Just False -> (falsePmExpr, True)
    Nothing    -> (original,   False)
  -- (PmExprLit l1@(PmSLit {}), PmExprLit l2@(PmSLit {}))
  --   | eqPmLit l1 l2 -> (truePmExpr,  True)
  --   | otherwise     -> (falsePmExpr, True)
  -- (PmExprLit l1@(PmOLit {}), PmExprLit l2@(PmOLit {}))
  --   | eqPmLit l1 l2 -> (truePmExpr,  True)
  --   | otherwise     -> (falsePmExpr, True)

  -- simplify bottom-up
  (PmExprEq {}, _) -> case (simplifyPmExpr e1, simplifyPmExpr e2) of
    ((e1', True ), (e2', _    )) -> simplifyEqExpr e1' e2'
    ((e1', _    ), (e2', True )) -> simplifyEqExpr e1' e2'
    ((e1', False), (e2', False)) -> (PmExprEq e1' e2', False) -- cannot go further
  (_, PmExprEq {}) -> case (simplifyPmExpr e1, simplifyPmExpr e2) of
    ((e1', True ), (e2', _    )) -> simplifyEqExpr e1' e2'
    ((e1', _    ), (e2', True )) -> simplifyEqExpr e1' e2'
    ((e1', False), (e2', False)) -> (PmExprEq e1' e2', False) -- cannot go further

  -- Constructors
  (PmExprCon c1 ts1, PmExprCon c2 ts2) -- constructors
    | c1 == c2 ->
        let (ts1', bs1) = mapAndUnzip simplifyPmExpr ts1 -- simplify them separately first
            (ts2', bs2) = mapAndUnzip simplifyPmExpr ts2 -- simplify them separately first
            (tss, _bss) = zipWithAndUnzip simplifyEqExpr ts1' ts2'
            worst_case  = PmExprEq (PmExprCon c1 ts1') (PmExprCon c2 ts2')
        in  if | not (or bs1 || or bs2) -> (worst_case, False) -- "no progress" (first for efficiency)
               | all isTruePmExpr  tss  -> (truePmExpr, True)
               | any isFalsePmExpr tss  -> (falsePmExpr, True)
               | otherwise              -> (worst_case, False)
    | otherwise -> (falsePmExpr, True)

  -- We cannot do anything about the rest..
  _other_equality -> (original, False)

  where
    original = PmExprEq e1 e2 -- reconstruct equality


-- | Look up stuff in an (un-flattened) substitution
-- -------------------------------------------------
applySubstSimpleEq :: PmVarEnv -> SimpleEq -> ComplexEq
applySubstSimpleEq env (x, e) = (varDeepLookup env x, exprDeepLookup env e)

varDeepLookup :: PmVarEnv -> Id -> PmExpr
varDeepLookup env x
  | Just e <- Map.lookup x env = exprDeepLookup env e -- go deeper
  | otherwise                  = PmExprVar x          -- terminal
{-# INLINE varDeepLookup #-}

exprDeepLookup :: PmVarEnv -> PmExpr -> PmExpr
exprDeepLookup env (PmExprVar x)    = varDeepLookup env x
exprDeepLookup env (PmExprCon c es) = PmExprCon c (map (exprDeepLookup env) es)
exprDeepLookup env (PmExprEq e1 e2) = PmExprEq (exprDeepLookup env e1) (exprDeepLookup env e2)
exprDeepLookup _   other_expr       = other_expr -- lit ==> lit, expr_other ==> expr_other

-- | External interface to the solver
-- ----------------------------------------------------------------------------
tmOracle :: TmState -> [SimpleEq] -> Maybe TmState
tmOracle = foldlM solveSimpleEq

-- ----------------------------------------------------------------------------

-- Should be in PmExpr gives cyclic imports :(
pmLitType :: PmLit -> Type
pmLitType (PmSLit   lit) = hsLitType   lit
pmLitType (PmOLit _ lit) = overLitType lit

-- ----------------------------------------------------------------------------

{-
NOTE [Deep equalities]

Solving nested equalities is the most difficult part. The general strategy
is the following:

  * Equalities of the form (True ~ (e1 ~ e2)) are transformed to just
    (e1 ~ e2) and then treated recursively.

  * Equalities of the form (False ~ (e1 ~ e2)) cannot be analyzed unless
    we know more about the inner equality (e1 ~ e2). That's exactly what
    `certainlyEqual' tries to do: It takes e1 and e2 and either returns
    truePmExpr, falsePmExpr or (e1' ~ e2') in case it is uncertain. Note
    that it is not e but rather e', since it may perform some
    simplifications deeper.
-}

