
{-
  Author: George Karachalias <george.karachalias@cs.kuleuven.be>
-}

{-# OPTIONS_GHC -Wwarn #-}   -- unused variables

{-# LANGUAGE CPP, MultiWayIf #-}

module TmOracle (
          PmExpr(..), PmLit(..), PmVarEnv, SimpleEq, ComplexEq, PmNegLitCt,
          hsExprToPmExpr, lhsExprToPmExpr, isNotPmExprOther,
          pmLitType, eqPmLit, tmOracle, notForced, flattenPmVarEnv,
          falsePmExpr, getValuePmExpr, filterComplex, runPmPprM,
          pprPmExprWithParens,

          IncrState, tmOracleIncr, initialIncrState
    ) where

#include "HsVersions.h"

import PmExpr
import Id
import DataCon
import TysWiredIn
import Type    -- ( Type )
import HsLit   -- overLitType
import TcHsSyn -- hsLitType
import Outputable
import MonadUtils
import Util

import Control.Arrow (first)
import Data.List (foldl')
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class (lift)
import qualified Data.Map as Map

{-
%************************************************************************
%*                                                                      *
\subsection{The term equality oracle}
%*                                                                      *
%************************************************************************

-- NOTE [Term oracle strategy]

Because of the incremental nature of the algorithm, initially all constraints
are shallow and most of them are simple equalities between variables. In
general, even if we start only with equalities of the form (x ~ e), the oracle
distinguishes between equalities of 3 different forms:

  * Variable equalities (VE) of the form (x ~ y)
  * Simple   equalities (SE) of the form (x ~ e)
  * Complex  equalities (CE) of the form (e ~ e')

The overall strategy works in 2 phases:

A. Preparation Phase
====================
1) Partition initial set into VE and 'actual simples' SE (partitionSimple).
2) Solve VE (solveVarEqs) and apply the resulting substitution in SE.
3) Repeatedly apply [x |-> e] to SE, as long as a simple equality (x ~ e)
   exists in it (eliminateSimples). The result is a set of 'actual' complex
   equalities CE.

Steps (1),(2),(3) are all performed by `prepComplexEq' on CE, which is the
most general form of equality.

B. Solving Phase
================
1) Try to simplify the constraints by means of flattening, evaluation of
   expressions etc. (simplifyComplexEqs).
2) If some simplification happens, prepare the constraints (prepComplexEq) and
   repeat the Solving Phase.
-}

-- ----------------------------------------------------------------------------
-- | Oracle Types

-- | The oracle will try and solve the wanted term constraints. If there is no
-- problem we get back a list of residual constraints. If an inconsistent
-- constraint is found, it will be returned as the evidence of failure.
type Failure = ComplexEq

-- | The substitution. As the solver processess the constraints, a
-- substitution theta is generated. Since at every step the algorithm completely
-- eliminates a variable, we end up with a DAG. If there were loops, the
-- algorithm would also loop (we do not inspect function calls that may be
-- recursive so there is not termination problem at the moment).
type PmVarEnv = Map.Map Id PmExpr

-- | The environment of the oracle contains
--     1. A set of constraints that cannot be handled (PmExprOther stuff).
--     2. A substitution we extend with every step and return as a result.
type TmOracleEnv = ([ComplexEq], PmVarEnv)

-- | The oracle monad.
type TmOracleM a = StateT TmOracleEnv (Except Failure) a

-- ----------------------------------------------------------------------------
-- | Oracle utils

-- | Monad stuff
runTmOracleM :: TmOracleM a -> Either Failure (a, TmOracleEnv)
runTmOracleM m = runExcept (runStateT m ([], Map.empty))

-- | To lift stuff that has no failure possibility into the monad
liftTmOracleM :: (PmVarEnv -> (res, PmVarEnv)) -> TmOracleM res
liftTmOracleM f = do
  (other_eqs, env) <- get
  let (res, env') = f env
  put (other_eqs, env')
  return res

-- | Add unhandled equalities in the state.
addUnhandledEqs :: [ComplexEq] -> TmOracleM ()
addUnhandledEqs eqs = modify (first (eqs++))

-- | Extend the substitution.
addSubst :: Id -> PmExpr -> PmVarEnv -> PmVarEnv
addSubst x e env = case Map.lookup x env of
  Nothing -> Map.insert x e env
  Just e' -> pprPanic "Check.addSubst:" (ppr x $$ ppr e $$ ppr e')

-- | Non-satisfiable set of constraints.
mismatch :: ComplexEq -> TmOracleM a
mismatch eq = lift (throwE eq)

-- ----------------------------------------------------------------------------

partitionSimpleM :: [SimpleEq] -> TmOracleM ([VarEq], [SimpleEq])
partitionSimpleM in_cs = do addUnhandledEqs (map toComplex res_eqs)
                            return (var_eqs, other_eqs)
  where (var_eqs, other_eqs, res_eqs) = partitionSimple in_cs

partitionComplexM :: [ComplexEq] -> TmOracleM ([VarEq], [SimpleEq], [ComplexEq])
partitionComplexM in_cs = do addUnhandledEqs (map toComplex res_eqs)
                             return (var_eqs, simpl_eqs, other_eqs)
  where (var_eqs, simpl_eqs, other_eqs, res_eqs) = partitionComplex in_cs

-- ----------------------------------------------------------------------------
-- | Solving equalities between variables

-- | A set of equalities between variables is always satisfiable.
solveVarEqs :: PmVarEnv -> [VarEq] -> (Id -> Id, PmVarEnv)
solveVarEqs env eqs = foldl' combine (id, env) eqs
  where
    combine (f, e) = first (.f) . solveVarEq e . idSubstVarEq f

solveVarEq :: PmVarEnv -> VarEq -> (Id -> Id, PmVarEnv)
solveVarEq env (x,y)
  | x == y    = (id, env)
  | otherwise = (subst, addSubst y (PmExprVar x) env)
  where subst = \z -> if z == y then x else z -- (x,y) -> [y |-> x]

-- Monadic version
solveVarEqsM :: [VarEq] -> TmOracleM (Id -> Id)
solveVarEqsM var_eqs = liftTmOracleM (\env -> solveVarEqs env var_eqs)

-- ----------------------------------------------------------------------------
-- | Solving simple equalities

eliminateSimples :: PmVarEnv -> [SimpleEq] -> [ComplexEq] -> ([ComplexEq], PmVarEnv)
eliminateSimples env [] complex_eqs = (complex_eqs, env)
eliminateSimples env ((x,e):eqs) complex_eqs
  = eliminateSimples env' simple_eqs (complex_eqs1 ++ complex_eqs2)
  where
    env' = addSubst x e env
    (simple_eqs, complex_eqs1) = substSimpleEqs x e eqs
    complex_eqs2 = map (substComplexEq x e) complex_eqs

-- Monadic version
eliminateSimplesM :: [SimpleEq] -> [ComplexEq] -> TmOracleM [ComplexEq]
eliminateSimplesM simple_eqs complex_eqs
  = liftTmOracleM (\env -> eliminateSimples env simple_eqs complex_eqs)

-- ----------------------------------------------------------------------------
-- | Solving complex equalities (workhorse)

prepComplexEqM :: [ComplexEq] -> TmOracleM [ComplexEq]
prepComplexEqM []  = return []
prepComplexEqM eqs = do
  (var_eqs, simple_eqs', complex_eqs') <- partitionComplexM eqs
  subst <- solveVarEqsM var_eqs
  let simple_eqs  = map (idSubstSimpleEq  subst) simple_eqs'
  let complex_eqs = map (idSubstComplexEq subst) complex_eqs'
  eliminateSimplesM simple_eqs complex_eqs

-- NB: Call only on prepped equalities (e.g. after prepComplexEq)
iterateComplex :: [ComplexEq] -> TmOracleM [ComplexEq]
iterateComplex []  = return []
iterateComplex eqs = do
  (done, eqs') <- simplifyComplexEqs eqs -- did we have any progress? continue
  if done then prepComplexEqM eqs' >>= iterateComplex
          else return eqs'               -- otherwise, return residual

simplifyComplexEqs :: [ComplexEq] -> TmOracleM (Bool, [ComplexEq])
simplifyComplexEqs eqs = do
  (done, new_eqs) <- mapAndUnzipM simplifyComplexEq eqs
  return (or done, concat new_eqs)

simplifyComplexEq :: ComplexEq -> TmOracleM (Bool, [ComplexEq])
simplifyComplexEq eq =
  case eq of
    -- variables
    (PmExprVar x, PmExprVar y)
      | x == y    -> return (True, [])
      | otherwise -> return (False, [eq])
    (PmExprVar _, _) -> return (False, [eq])
    (_, PmExprVar _) -> return (False, [eq])

    -- literals
    (PmExprLit l1, PmExprLit l2)
      | eqPmLit l1 l2 -> return (True, [])
      | otherwise     -> mismatch eq

    -- constructors
    (PmExprCon c1 es1, PmExprCon c2 es2)
      | c1 == c2  -> simplifyComplexEqs (es1 `zip` es2)
      | otherwise -> mismatch eq

    -- See NOTE [Deep equalities]
    (PmExprCon c es, PmExprEq e1 e2) -> handleDeepEq c es e1 e2
    (PmExprEq e1 e2, PmExprCon c es) -> handleDeepEq c es e1 e2

    -- Overloaded error
    (PmExprCon _ _, PmExprLit l)
      | PmOLit {} <- l -> overloaded_syntax
      | otherwise      -> panic "simplifyComplexEq: constructor-literal"
    (PmExprLit l, PmExprCon _ _)
      | PmOLit {} <- l -> overloaded_syntax
      | otherwise      -> panic "simplifyComplexEq: literal-constructor"

    _other_equality -> return (False, [eq]) -- can't simplify :(

  where
    overloaded_syntax = addUnhandledEqs [eq] >> return (True,[])

    handleDeepEq :: DataCon -> [PmExpr] -- constructor and arguments
                 -> PmExpr  -> PmExpr   -- the equality
                 -> TmOracleM (Bool, [ComplexEq])
    handleDeepEq c es e1 e2
      | c == trueDataCon = do
          (_, new) <- simplifyComplexEq (e1,e2)
          return (True, new)
      | otherwise = do
         let pmexpr = certainlyEqual e1 e2
         if isTruePmExpr pmexpr || isFalsePmExpr pmexpr
            then return (True,  [(PmExprCon c es,pmexpr)])
            else return (False, [eq])

certainlyEqual :: PmExpr -> PmExpr -> PmExpr -- NOTE [Deep equalities]
certainlyEqual e1 e2 =
  case (e1, e2) of

    -- Simple cases
    (PmExprVar  x, PmExprVar  y) -> eqVars x y  -- variables
    (PmExprLit l1, PmExprLit l2) -> eqLit l1 l2 -- literals

    -- Constructor case (unfold)
    (PmExprCon c1 es1, PmExprCon c2 es2) -- constructors
      | c1 == c2  -> certainlyEqualMany es1 es2
      | otherwise -> falsePmExpr

    -- Cannot be sure about the rest
    _other_equality -> expr -- Not really expressive, are we?

  where
    expr = PmExprEq e1 e2 -- reconstruct the equality from the arguments

    eqVars :: Id -> Id -> PmExpr
    eqVars x y = if x == y then truePmExpr else expr

    eqLit :: PmLit -> PmLit -> PmExpr
    eqLit l1 l2 = case (l1, l2) of
      (PmSLit {}, PmSLit {})
        | eqPmLit l1 l2 -> truePmExpr
        | otherwise     -> falsePmExpr
      (PmOLit {}, PmOLit {})
        | eqPmLit l1 l2 -> truePmExpr
        | otherwise     -> falsePmExpr
      _overloaded       -> expr

    certainlyEqualMany :: [PmExpr] -> [PmExpr] -> PmExpr
    certainlyEqualMany es1 es2 =
      let args   = zipWith certainlyEqual es1 es2
          result | all isTruePmExpr  args = truePmExpr
                 | any isFalsePmExpr args = falsePmExpr
                 | otherwise              = expr -- inconclusive
      in  result

-- ----------------------------------------------------------------------------
-- | Entry point to the solver

-- | The term oracle. Returns residual constraints, unhandled constraints and
-- the final mapping. In case of failure, it returns a witness.

tmOracle :: [SimpleEq] -> Either Failure ([ComplexEq], TmOracleEnv)
tmOracle simple_eqs = runTmOracleM (solveAll simple_eqs)

solveAll :: [SimpleEq] -> TmOracleM [ComplexEq]
solveAll []  = return []
solveAll eqs = do
  (var_eqs, simple_eqs') <- partitionSimpleM eqs
  subst <- solveVarEqsM var_eqs
  let simple_eqs = map (idSubstSimpleEq subst) simple_eqs'
  complex_eqs <- eliminateSimplesM simple_eqs []
  iterateComplex complex_eqs

-- ----------------------------------------------------------------------------
-- | Some more utilities

-- | Traverse the DAG to get the final value of a PmExpr
getValuePmExpr :: PmVarEnv -> PmExpr -> PmExpr
getValuePmExpr env (PmExprVar x)
  | Just e <- Map.lookup x env = getValuePmExpr env e
  | otherwise                  = PmExprVar x
getValuePmExpr env (PmExprCon c es) = PmExprCon c (map (getValuePmExpr env) es)
getValuePmExpr env (PmExprEq e1 e2) = PmExprEq (getValuePmExpr env e1) (getValuePmExpr env e2)
getValuePmExpr _   other_expr       = other_expr

-- | Check whether a variable has been refined to (at least) a WHNF
notForced :: Id -> PmVarEnv -> Bool
notForced x env = case getValuePmExpr env (PmExprVar x) of
  PmExprVar _ -> True
  _other_expr -> False

-- | Flatten the DAG. (Could be improved in terms of performance)
flattenPmVarEnv :: PmVarEnv -> PmVarEnv
flattenPmVarEnv env = Map.map (getValuePmExpr env) env

-- ----------------------------------------------------------------------------

type IncrState = ( [ComplexEq]   -- constraints that cannot be solved yet (we need more info)
                 , TmOracleEnv ) -- ([ComplexEq], PmVarEnv == Map Id PmExpr)
                                 --   1. A set of constraints that cannot be handled (PmExprOther stuff).
                                 --   2. A substitution we extend with every step

initialIncrState :: IncrState
initialIncrState = ([], ([], Map.empty))

solveSimpleEqIncr :: IncrState -> SimpleEq -> Maybe IncrState
solveSimpleEqIncr solver_env@(_,(_,env)) simple
  = solveComplexEqIncr solver_env -- do the actual *merging* with existing solver state
  $ simplifyComplexEqNew          -- simplify as much as you can
  $ applySubstSimpleEq env simple -- replace everything we already know

solveComplexEqIncr :: IncrState -> ComplexEq -> Maybe IncrState
solveComplexEqIncr solver_state@(standby, (unhandled, env)) eq@(e1, e2) = case eq of
  -- We cannot do a thing about these cases
  (PmExprOther _,_)            -> Just (standby, (eq:unhandled, env))
  (_,PmExprOther _)            -> Just (standby, (eq:unhandled, env))
  -- Look at the catch-all.. (PmExprLit _, PmExprCon _ _) -> Just (standby, (eq:unhandled, env))
  -- Look at the catch-all.. (PmExprCon _ _, PmExprLit _) -> Just (standby, (eq:unhandled, env))
  -- Look at the catch-all.. (PmExprLit _, PmExprEq _ _)  -> Just (standby, (eq:unhandled, env))
  -- Look at the catch-all.. (PmExprEq _ _, PmExprLit _)  -> Just (standby, (eq:unhandled, env))

  (PmExprLit l1, PmExprLit l2)
    | eqPmLit l1 l2 -> Just solver_state
    | otherwise     -> Nothing
  (PmExprCon c1 ts1, PmExprCon c2 ts2)
    | c1 == c2  -> foldlM solveComplexEqIncr solver_state (zip ts1 ts2)
    | otherwise -> Nothing
  (PmExprCon c [], PmExprEq t1 t2)
    | c == trueDataCon  -> solveComplexEqIncr solver_state (t1, t2)
    | c == falseDataCon -> Just (eq:standby, (unhandled, env))
  (PmExprEq t1 t2, PmExprCon c [])
    | c == trueDataCon  -> solveComplexEqIncr solver_state (t1, t2)
    | c == falseDataCon -> Just (eq:standby, (unhandled, env))

  (PmExprVar x, PmExprVar y)
    | x == y    -> Just solver_state
    | otherwise -> extendSubstAndSolve x e2 solver_state {- CHOOSE ONE AND EXTEND SUBST & LOOK AT STB -}

  (PmExprVar x, PmExprCon {}) -> extendSubstAndSolve x e2 solver_state {- EXTEND SUBST & LOOK AT STB -}
  (PmExprCon {}, PmExprVar x) -> extendSubstAndSolve x e1 solver_state {- EXTEND SUBST & LOOK AT STB -}
  (PmExprVar x, PmExprLit {}) -> extendSubstAndSolve x e2 solver_state {- EXTEND SUBST & LOOK AT STB -}
  (PmExprLit {}, PmExprVar x) -> extendSubstAndSolve x e1 solver_state {- EXTEND SUBST & LOOK AT STB -}
  (PmExprVar x,  PmExprEq {}) -> extendSubstAndSolve x e2 solver_state {- EXTEND SUBST & LOOK AT STB -}
  (PmExprEq  {}, PmExprVar x) -> extendSubstAndSolve x e1 solver_state {- EXTEND SUBST & LOOK AT STB -}

  (PmExprEq _ _, PmExprEq _ _) -> Just (eq:standby, (unhandled, env))

  _ -> Just (standby, (eq:unhandled, env)) -- I HATE CATCH-ALLS

extendSubstAndSolve :: Id -> PmExpr -> IncrState -> Maybe IncrState
extendSubstAndSolve x e (standby, (unhandled, env))
  = foldlM solveComplexEqIncr new_incr_state changed
  where
    (changed, unchanged) = partitionWith (substComplexEqB x e) standby  -- apply substitution to residual to see if there is any progress. leave the unchanged ones behind
    new_incr_state       = (unchanged, (unhandled, Map.insert x e env)) -- extend the substitution.

simplifyComplexEqNew :: ComplexEq -> ComplexEq
simplifyComplexEqNew (e1, e2) = (fst $ simplifyPmExpr e1, fst $ simplifyPmExpr e2)

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
  (PmExprLit l1@(PmSLit {}), PmExprLit l2@(PmSLit {}))
    | eqPmLit l1 l2 -> (truePmExpr,  True)
    | otherwise     -> (falsePmExpr, True)
  (PmExprLit l1@(PmOLit {}), PmExprLit l2@(PmOLit {}))
    | eqPmLit l1 l2 -> (truePmExpr,  True)
    | otherwise     -> (falsePmExpr, True)

  -- simplify bottom-up
  (PmExprEq {}, _) -> case (simplifyPmExpr e1, simplifyPmExpr e2) of
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


-- | Look up stuff in an (un-flattened) substitution (same as getValuePmExpr)
-- ----------------------------------------------------------------------------
applySubstSimpleEq :: PmVarEnv -> SimpleEq -> ComplexEq
applySubstSimpleEq env (x, e) = (varDeepLookup env x, exprDeepLookup env e)

varDeepLookup :: PmVarEnv -> Id -> PmExpr
varDeepLookup env x
  | Just e <- Map.lookup x env = exprDeepLookup env e -- go deeper
  | otherwise                  = PmExprVar x          -- terminal

exprDeepLookup :: PmVarEnv -> PmExpr -> PmExpr
exprDeepLookup env (PmExprVar x)    = varDeepLookup env x
exprDeepLookup env (PmExprCon c es) = PmExprCon c (map (exprDeepLookup env) es)
exprDeepLookup env (PmExprEq e1 e2) = PmExprEq (exprDeepLookup env e1) (exprDeepLookup env e2)
exprDeepLookup _   other_expr       = other_expr -- lit ==> lit, expr_other ==> expr_other

-- | External interface to the solver
-- ----------------------------------------------------------------------------
tmOracleIncr :: IncrState -> [SimpleEq] -> Maybe IncrState
tmOracleIncr env eqs = foldlM solveSimpleEqIncr env eqs

-- ----------------------------------------------------------------------------

-- Should be in PmExpr gives cyclic imports :(
pmLitType :: PmLit -> Type
pmLitType (PmSLit   lit) = hsLitType   lit
pmLitType (PmOLit _ lit) = overLitType lit

-- ----------------------------------------------------------------------------

{-
NOTE [Representation of substitution]

Throughout the code we use 2 different ways to represent substitutions:
  * Substitutions from variables to variables are represented using Haskell
    functions with type (Id -> Id).
  * Substitutions from variables to expressions are usually passed explicitly
    as two arguments (the Id and the PmExpr to substitute it with)
By convention, substitutions of the first kind are prefixed by `idSubst'
while the latter are prefixed simply by 'subst'.
-}

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

