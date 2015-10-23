
{-
  Author: George Karachalias <george.karachalias@cs.kuleuven.be>
-}

{-# OPTIONS_GHC -Wwarn #-}   -- unused variables

{-# LANGUAGE CPP #-}

module Check (
        -- Actual check
        checkSingle, checkMatches, PmResult,

        -- Pretty printing
        pprUncovered,

        -- See NOTE [Type and Term Equality Propagation]
        genCaseTmCs1, genCaseTmCs2
    ) where

#include "HsVersions.h"

import TmOracle

import HsSyn
import TcHsSyn
import Id
import ConLike
import DataCon
import Name
import TysWiredIn
import TyCon
import SrcLoc
import Util
import BasicTypes
import Outputable
import FastString

import DsMonad    -- DsM, initTcDsForSolver, getDictsDs
import TcSimplify -- tcCheckSatisfiability
import TcType     -- toTcType, toTcTypeBag
import Bag
import ErrUtils
import MonadUtils -- MonadIO
import Var        -- EvVar
import Type
import UniqSupply
import DsGRHSs    -- isTrueLHsExpr

-- || import qualified Data.Map as Map -- let's check performance
import Data.List     -- find
import Data.Maybe    -- isNothing, isJust, fromJust
import Control.Monad -- liftM3, forM

{-
This module checks pattern matches for:
\begin{enumerate}
  \item Equations that are redundant
  \item Equations with inaccessible right-hand-side
  \item Exhaustiveness
\end{enumerate}

The algorithm used is described in the paper:

  "GADTs Meet Their Match:
     Pattern-matching Warnings That Account for GADTs, Guards, and Laziness"

    http://people.cs.kuleuven.be/~george.karachalias/papers/p424-karachalias.pdf

%************************************************************************
%*                                                                      *
\subsection{Pattern Match Check Types}
%*                                                                      *
%************************************************************************
-}

type PmM a = DsM a

data PmConstraint = TmConstraint Id PmExpr -- Term equalities: x ~ e
                  | TyConstraint [EvVar]   -- Type equalities
                  | BtConstraint Id        -- Strictness constraints: x ~ _|_

-- The *arity* of a PatVec [p1,..,pn] is
-- the number of p1..pn that are not Guards

data PmPat p = PmCon { pm_con_con     :: DataCon
                     , pm_con_arg_tys :: [Type]  -- The univeral arg types, 1-1 with the universal
                                                 --   tyvars of the constructor
                     , pm_con_tvs     :: [TyVar] -- Existentially bound type variables (tyvars only)
                     , pm_con_dicts   :: [EvVar] -- Ditto *coercion variables* and *dictionaries*
                     , pm_con_args    :: [p] }
             | PmVar { pm_var_id      :: Id }

data Pattern = PmGuard PatVec PmExpr      -- Guard Patterns
             | NonGuard (PmPat Pattern)   -- Other Patterns

newtype ValAbs = VA (PmPat ValAbs) -- Value Abstractions

type PatVec    = [Pattern] -- Pattern Vectors
type ValVecAbs = [ValAbs]  -- Value Vector Abstractions

-- data T a where
--     MkT :: forall p q. (Eq p, Ord q) => p -> q -> T [p]
-- or  MkT :: forall p q r. (Eq p, Ord q, [p] ~ r) => p -> q -> T r

data ValSetAbs   -- Reprsents a set of value vector abstractions
                 -- Notionally each value vector abstraction is a triple:
                 --   (Gamma |- us |> Delta)
                 -- where 'us'    is a ValueVec
                 --       'Delta' is a constraint
  -- INVARIANT VsaInvariant: an empty ValSetAbs is always represented by Empty
  -- INVARIANT VsaArity: the number of Cons's in any path to a leaf is the same
  -- The *arity* of a ValSetAbs is the number of Cons's in any path to a leaf
  = Empty                               -- {}
  | Union ValSetAbs ValSetAbs           -- S1 u S2
  | Singleton                           -- { |- empty |> empty }
  | Constraint [PmConstraint] ValSetAbs -- Extend Delta
  | Cons ValAbs ValSetAbs               -- map (ucon u) vs

type PmResult = ( [[LPat Id]] -- redundant clauses
                , [[LPat Id]] -- clauses with inaccessible rhs
                , [(ValVecAbs,([ComplexEq], PmVarEnv))] ) -- missing

{-
%************************************************************************
%*                                                                      *
\subsection{Entry points to the checker: checkSingle and checkMatches}
%*                                                                      *
%************************************************************************
-}

-- Check a single pattern binding (let)
checkSingle :: Id -> Pat Id -> DsM PmResult
checkSingle var p = do
  let lp = [noLoc p]
  vec <- liftUs (translatePat p)
  vsa <- initial_uncovered [var]
  (c,d,us') <- patVectProc (vec,[]) vsa -- no guards
  us <- pruneValSetAbs us'
  return $ case (c,d) of
    (True,  _)     -> ([],   [],   us)
    (False, True)  -> ([],   [lp], us)
    (False, False) -> ([lp], [],   us)

-- Check a matchgroup (case, etc)
checkMatches :: [Id] -> [LMatch Id (LHsExpr Id)] -> DsM PmResult
checkMatches vars matches
  | null matches = return ([],[],[])
  | otherwise    = do
      missing    <- initial_uncovered vars
      (rs,is,us) <- go matches missing
      return (map hsLMatchPats rs, map hsLMatchPats is, us)
  where
    go [] missing = do
      missing' <- pruneValSetAbs missing
      return ([], [], missing')

    go (m:ms) missing = do
      clause        <- liftUs (translateMatch m)
      (c,  d,  us ) <- patVectProc clause missing
      (rs, is, us') <- go ms us
      return $ case (c,d) of
        (True,  _)     -> (  rs,   is, us')
        (False, True)  -> (  rs, m:is, us')
        (False, False) -> (m:rs,   is, us')

initial_uncovered :: [Id] -> DsM ValSetAbs
initial_uncovered vars = do
  ty_cs <- TyConstraint . bagToList <$> getDictsDs
  tm_cs <- map (uncurry TmConstraint) . bagToList <$> getTmCsDs
  let vsa = map (VA . PmVar) vars
  return $ mkConstraint (ty_cs:tm_cs) (foldr Cons Singleton vsa)

{-
%************************************************************************
%*                                                                      *
\subsection{Transform source syntax to *our* syntax}
%*                                                                      *
%************************************************************************
-}

-- -----------------------------------------------------------------------
-- | Utilities

nullaryConPattern :: DataCon -> Pattern
-- Nullary data constructor and nullary type constructor
nullaryConPattern con = NonGuard $
  PmCon { pm_con_con = con, pm_con_arg_tys = []
        , pm_con_tvs = [], pm_con_dicts = [], pm_con_args = [] }

truePattern :: Pattern
truePattern = nullaryConPattern trueDataCon

-- | A fake guard pattern (True <- _) used to represent cases we *cannot* handle
fake_pat :: Pattern
fake_pat = PmGuard [truePattern] (PmExprOther EWildPat)

vanillaConPattern :: DataCon -> [Type] -> PatVec -> Pattern
-- ADT constructor pattern => no existentials, no local constraints
vanillaConPattern con arg_tys args = NonGuard $
  PmCon { pm_con_con = con, pm_con_arg_tys = arg_tys
        , pm_con_tvs = [], pm_con_dicts = [], pm_con_args = args }

nilPattern :: Type -> Pattern
nilPattern ty = NonGuard $ PmCon { pm_con_con = nilDataCon, pm_con_arg_tys = [ty]
                                 , pm_con_tvs = [], pm_con_dicts = []
                                 , pm_con_args = [] }

mkListPatVec :: Type -> PatVec -> PatVec -> PatVec
mkListPatVec ty xs ys = [NonGuard $ PmCon { pm_con_con = consDataCon
                                          , pm_con_arg_tys = [ty]
                                          , pm_con_tvs = [], pm_con_dicts = []
                                          , pm_con_args = xs++ys }]

mkSLitGuard :: Id -> HsLit -> Pattern
mkSLitGuard var lit = PmGuard [truePattern] (PmExprEq (PmExprVar var) e)
  where e = PmExprLit (PmSLit lit)

mkOLitGuard :: Id -> Maybe (SyntaxExpr Id) -> HsOverLit Id -> Pattern
mkOLitGuard var mb_negate olit = PmGuard [truePattern] (PmExprEq (PmExprVar var) e)
  where b = case mb_negate of
              Just _  -> True
              Nothing -> False
        e = PmExprLit (PmOLit b olit)

-- Specifically for overloaded strings. If we know that an overloaded x is a
-- string, we can remove the fromString function since we know that it is the
-- identity.
oStrToHsLit_mb :: HsOverLit Id -> Maybe HsLit
oStrToHsLit_mb olit
  | ol_type olit == stringTy
  , HsIsString src fs <- ol_val olit
  = Just (HsString src fs)
  | otherwise = Nothing

-- -----------------------------------------------------------------------
-- | Transform a Pat Id into a list of (PmPat Id) -- Note [Translation to PmPat]

translatePat :: Pat Id -> UniqSM PatVec
translatePat pat = case pat of
  WildPat ty         -> mkPatternVarsSM [ty]
  VarPat  id         -> return [idPatternVar id]
  ParPat p           -> translatePat (unLoc p)
  LazyPat p          -> mkPatternVarsSM [hsPatType pat] -- translatePat (unLoc p) -- COMEHERE: We ignore laziness   for now
  BangPat p          -> translatePat (unLoc p)                                    -- COMEHERE: We ignore strictness for now
                                                                                  -- This might affect the divergence checks?
  AsPat lid p -> do
    ps <- translatePat (unLoc p)
    let [e] = map valAbsToPmExpr (coercePatVec ps) -- NOTE [Translating As Patterns]
        g   = PmGuard [idPatternVar (unLoc lid)] e
    return (ps ++ [g])

  SigPatOut p _ty -> translatePat (unLoc p) -- TODO: Use the signature?

  CoPat wrapper p ty -> do
    ps      <- translatePat p
    (xp,xe) <- mkPmId2FormsSM ty {- IS THIS TYPE CORRECT OR IS IT THE OPPOSITE?? -}
    let g = mkGuard ps (HsWrap wrapper (unLoc xe))
    return [xp,g]

  -- (n + k)  ===>   x (True <- x >= k) (n <- x-k)
  NPlusKPat n k ge minus -> do
    (xp, xe) <- mkPmId2FormsSM $ idType (unLoc n)
    let ke = noLoc (HsOverLit k)         -- k as located expression
        g1 = mkGuard [truePattern]            $ OpApp xe (noLoc ge)    no_fixity ke -- True <- (x >= k)
        g2 = mkGuard [idPatternVar (unLoc n)] $ OpApp xe (noLoc minus) no_fixity ke -- n    <- (x -  k)
    return [xp, g1, g2]

  -- (fun -> pat)   ===>   x (pat <- fun x)
  ViewPat lexpr lpat arg_ty -> do
    (xp,xe) <- mkPmId2FormsSM arg_ty
    ps      <- translatePat (unLoc lpat) -- p translated recursively
    let g  = mkGuard ps (HsApp lexpr xe) -- p <- f x
    return [xp,g]

  -- list
  ListPat ps ty Nothing -> do
    foldr (mkListPatVec ty) [nilPattern ty] <$> translatePatVec (map unLoc ps)

  -- overloaded list
  ListPat lpats elem_ty (Just (pat_ty, to_list))
    | Just e_ty <- splitListTyConApp_maybe pat_ty, elem_ty `eqType` e_ty ->
        -- Watch out for horrible hack: See Note [Comparison with OpenTypeKind]
        -- We have to ensure that the element types are the same. Otherwise, one
        -- may give an instance IsList [Int] (more specific than the default IsList [a])
        -- with a different implementation for `toList'
        translatePat (ListPat lpats e_ty Nothing)
    | otherwise -> do
        (xp, xe) <- mkPmId2FormsSM pat_ty
        ps       <- translatePatVec (map unLoc lpats) -- list as value abstraction
        let pats = foldr (mkListPatVec elem_ty) [nilPattern elem_ty] ps
            g  = mkGuard pats (HsApp (noLoc to_list) xe) -- [...] <- toList x -- THIS IS WRONG
        return [xp,g]

  ConPatOut { pat_con = L _ (PatSynCon _) } -> do
    -- Pattern synonyms have a "matcher" (see Note [Pattern synonym representation] in PatSyn.hs
    -- We should be able to transform (P x y)
    -- to   v (Just (x, y) <- matchP v (\x y -> Just (x,y)) Nothing
    -- That is, a combination of a variable pattern and a guard
    -- But there are complications with GADTs etc, and this isn't done yet
    var <- mkPatternVarSM (hsPatType pat)
    return [var,fake_pat]

  ConPatOut { pat_con     = L _ (RealDataCon con)
            , pat_arg_tys = arg_tys
            , pat_tvs     = ex_tvs
            , pat_dicts   = dicts
            , pat_args    = ps } -> do
    args <- translateConPatVec arg_tys ex_tvs con ps
    return [ NonGuard $ PmCon { pm_con_con     = con
                              , pm_con_arg_tys = arg_tys
                              , pm_con_tvs     = ex_tvs
                              , pm_con_dicts   = dicts
                              , pm_con_args    = args }]

  NPat lit mb_neg _eq
    | Just hs_lit <- oStrToHsLit_mb lit ->
        translatePat (LitPat hs_lit) -- overloaded string
    | otherwise -> do
        var <- mkPmIdM (hsPatType pat)
        let guard = mkOLitGuard var mb_neg lit
        return [NonGuard (PmVar var), guard] -- don't like it. make a function for this sort of thing

  LitPat lit
      -- If it is a string then convert it to a list of characters
    | HsString src s <- lit ->
        foldr (mkListPatVec charTy) [nilPattern charTy] <$>
          translatePatVec (map (LitPat . HsChar src) (unpackFS s))
    | otherwise -> do
        var <- mkPmIdM (hsPatType pat)
        let guard = mkSLitGuard var lit
        return [NonGuard (PmVar var), guard]

  PArrPat ps ty -> do
    tidy_ps <- translatePatVec (map unLoc ps)
    let fake_con = parrFakeCon (length ps)
    return [vanillaConPattern fake_con [ty] (concat tidy_ps)]

  TuplePat ps boxity tys -> do
    tidy_ps   <- translatePatVec (map unLoc ps)
    let tuple_con = tupleCon (boxityNormalTupleSort boxity) (length ps)
    return [vanillaConPattern tuple_con tys (concat tidy_ps)]

  -- --------------------------------------------------------------------------
  -- Not supposed to happen
  ConPatIn {}      -> panic "Check.translatePat: ConPatIn"
  SplicePat {}     -> panic "Check.translatePat: SplicePat"
  QuasiQuotePat {} -> panic "Check.translatePat: QuasiQuotePat"
  SigPatIn {}      -> panic "Check.translatePat: SigPatIn"

translatePatVec :: [Pat Id] -> UniqSM [PatVec] -- Do not concatenate them (sometimes we need them separately)
translatePatVec pats = mapM translatePat pats

translateConPatVec :: [Type] -> [TyVar] -> DataCon -> HsConPatDetails Id -> UniqSM PatVec
translateConPatVec _univ_tys _ex_tvs _ (PrefixCon ps)   = concat <$> translatePatVec (map unLoc ps)
translateConPatVec _univ_tys _ex_tvs _ (InfixCon p1 p2) = concat <$> translatePatVec (map unLoc [p1,p2])
translateConPatVec  univ_tys  ex_tvs c (RecCon (HsRecFields fs _))
    -- Nothing matched. Make up some fresh term variables
  | null fs        = mkPatternVarsSM arg_tys
    -- The data constructor was not defined using record syntax. For the
    -- pattern to be in record syntax it should be empty (e.g. Just {}).
    -- So just like the previous case.
  | null orig_lbls = ASSERT (null matched_lbls) mkPatternVarsSM arg_tys
    -- Some of the fields appear, in the original order (there may be holes).
    -- Generate a simple constructor pattern and make up fresh variables for
    -- the rest of the fields
  | matched_lbls `subsetOf` orig_lbls = ASSERT (length orig_lbls == length arg_tys)
      let translateOne (lbl, ty) = case lookup lbl matched_pats of
            Just p  -> translatePat p
            Nothing -> mkPatternVarsSM [ty]
      in  concatMapM translateOne (zip orig_lbls arg_tys)
    -- The fields that appear are not in the correct order. Make up fresh
    -- variables for all fields and add guards after matching, to force the
    -- evaluation in the correct order.
  | otherwise = do
      arg_var_pats    <- mkPatternVarsSM arg_tys
      translated_pats <- forM matched_pats $ \(x,pat) -> do
        pvec <- translatePat pat
        return (x, pvec)

      let zipped = zip orig_lbls [ x | NonGuard (PmVar x) <- arg_var_pats ] -- [(Name, Id)]
          guards = map (\(name,pvec) -> case lookup name zipped of
                            Just x  -> PmGuard pvec (PmExprVar x)
                            Nothing -> panic "translateConPatVec: lookup")
                       translated_pats

      return (arg_var_pats ++ guards)
  where
    -- The actual argument types (instantiated)
    arg_tys = dataConInstOrigArgTys c (univ_tys ++ mkTyVarTys ex_tvs)

    -- Some label information
    orig_lbls    = dataConFieldLabels c
    matched_lbls = [ idName id     | L _ (HsRecField (L _ id) _       _) <- fs]
    matched_pats = [(idName id,p)  | L _ (HsRecField (L _ id) (L _ p) _) <- fs]

    subsetOf :: Eq a => [a] -> [a] -> Bool
    subsetOf []     _  = True
    subsetOf (_:_)  [] = False
    subsetOf (x:xs) (y:ys)
      | x == y    = subsetOf    xs  ys
      | otherwise = subsetOf (x:xs) ys

translateMatch :: LMatch Id (LHsExpr Id) -> UniqSM (PatVec,[PatVec])
translateMatch (L _ (Match lpats _ grhss)) = do
  pats'   <- concat <$> translatePatVec pats
  guards' <- mapM translateGuards guards
  return (pats', guards')
  where
    extractGuards :: LGRHS Id (LHsExpr Id) -> [GuardStmt Id]
    extractGuards (L _ (GRHS gs _)) = map unLoc gs

    pats   = map unLoc lpats
    guards = map extractGuards (grhssGRHSs grhss)

-- -----------------------------------------------------------------------
-- | Transform source guards (GuardStmt Id) to PmPats (Pattern)

-- A. What to do with lets?

translateGuards :: [GuardStmt Id] -> UniqSM PatVec
translateGuards guards = do
  all_guards <- concat <$> mapM translateGuard guards
  -- return $ all_guards
  return (replace_unhandled all_guards) -- Just some ad-hoc pruning
  where
    replace_unhandled :: PatVec -> PatVec
    replace_unhandled gv
      | any_unhandled gv = fake_pat : [ p | p <- gv, shouldKeep p ]
      | otherwise        = gv

    any_unhandled :: PatVec -> Bool
    any_unhandled gv = or [ not (shouldKeep p) | p <- gv ]

    -- unhandled :: PatVec -> PmExpr -> Bool
    -- unhandled [p] expr
    --   | NonGuard (PmVar {}) <- p = True  -- Binds to variable? We don't branch (Y)
    -- unhandled _pv expr
    --   | isNotPmExprOther expr    = True  -- The expression is "normal"? We branch but we want that
    --   | otherwise                = False -- Otherwise it branches without being useful

    shouldKeep :: Pattern -> Bool
    shouldKeep (NonGuard p)
      | PmVar {} <- p      = True
      | PmCon {} <- p      = length (allConstructors (pm_con_con p)) == 1
                             && all shouldKeep (pm_con_args p)
    shouldKeep (PmGuard pv e)
      | all shouldKeep pv  = True
      | isNotPmExprOther e = True -- expensive but we want it
    shouldKeep _other_pat  = False -- let the rest..
    -- OPTIMIZE THIS

translateGuard :: GuardStmt Id -> UniqSM PatVec
translateGuard (BodyStmt e _ _ _) = translateBoolGuard e
translateGuard (LetStmt    binds) = translateLet binds
translateGuard (BindStmt p e _ _) = translateBind p e
translateGuard (LastStmt      {}) = panic "translateGuard LastStmt"
translateGuard (ParStmt       {}) = panic "translateGuard ParStmt"
translateGuard (TransStmt     {}) = panic "translateGuard TransStmt"
translateGuard (RecStmt       {}) = panic "translateGuard RecStmt"

translateLet :: HsLocalBinds Id -> UniqSM PatVec
translateLet _binds = return [] -- NOT CORRECT: A let cannot fail so in a way we
  -- are fine with it but it can bind things which we do not bring in scope.
  -- Hence, they are free while they shouldn't. More constraints would make it
  -- more expressive but omitting some is always safe (Is it? Make sure it is)

translateBind :: LPat Id -> LHsExpr Id -> UniqSM PatVec
translateBind (L _ p) e = do
  ps <- translatePat p
  return [mkGuard ps (unLoc e)]

translateBoolGuard :: LHsExpr Id -> UniqSM PatVec
translateBoolGuard e
  | isJust (isTrueLHsExpr e) = return []
    -- The formal thing to do would be to generate (True <- True)
    -- but it is trivial to solve so instead we give back an empty
    -- PatVec for efficiency
  | otherwise = return [PmGuard [truePattern] (lhsExprToPmExpr e)]

{-
%************************************************************************
%*                                                                      *
\subsection{Main Pattern Matching Check}
%*                                                                      *
%************************************************************************
-}

-- ----------------------------------------------------------------------------
-- | Process a vector

-- Covered, Uncovered, Divergent
process_guards :: UniqSupply -> [PatVec] -> (ValSetAbs, ValSetAbs, ValSetAbs)
process_guards _us [] = (Singleton, Empty, Empty) -- No guard == True guard
process_guards us  gs
  | any null gs = (Singleton, Empty, Singleton) -- Contains an empty guard? == it is exhaustive [Too conservative for divergence]
  | otherwise   = go us Singleton gs
  where
    go _usupply missing []       = (Empty, missing, Empty)
    go  usupply missing (gv:gvs) = (mkUnion cs css, uss, mkUnion ds dss)
      where
        (us1, us2, us3, us4) = splitUniqSupply4 usupply

        cs = covered   us1 Singleton gv missing
        us = uncovered us2 Empty     gv missing
        ds = divergent us3 Empty     gv missing

        (css, uss, dss) = go us4 us gvs

-- ----------------------------------------------------------------------------
-- | Getting some more uniques

splitUniqSupply3 :: UniqSupply -> (UniqSupply, UniqSupply, UniqSupply)
splitUniqSupply3 us = (us1, us2, us3)
  where
    (us1, us') = splitUniqSupply us
    (us2, us3) = splitUniqSupply us'

splitUniqSupply4 :: UniqSupply -> (UniqSupply, UniqSupply, UniqSupply, UniqSupply)
splitUniqSupply4 us = (us1, us2, us3, us4)
  where
    (us1, us2, us') = splitUniqSupply3 us
    (us3, us4)      = splitUniqSupply us'

getUniqueSupplyM3 :: MonadUnique m => m (UniqSupply, UniqSupply, UniqSupply)
getUniqueSupplyM3 = liftM3 (,,) getUniqueSupplyM getUniqueSupplyM getUniqueSupplyM

-- ----------------------------------------------------------------------------
-- | Basic utilities

patternType :: Pattern -> Type
patternType (PmGuard pv _) = ASSERT (patVecArity pv == 1) (patternType p)
  where Just p = find ((==1) . patternArity) pv
patternType (NonGuard pat) = pmPatType pat

-- | Get the type out of a PmPat. For guard patterns (ps <- e) we use the type
-- of the first (or the single -WHEREVER IT IS- valid to use?) pattern
pmPatType :: PmPat p -> Type
pmPatType (PmCon { pm_con_con = con, pm_con_arg_tys = tys })
                                     = mkTyConApp (dataConTyCon con) tys
pmPatType (PmVar { pm_var_id  = x }) = idType x

mkOneConFull :: Id -> UniqSupply -> DataCon -> (PmPat ValAbs, [PmConstraint])
--  *  x :: T tys, where T is an algebraic data type
--     NB: in the case of a data familiy, T is the *representation* TyCon
--     e.g.   data instance T (a,b) = T1 a b
--       leads to
--            data TPair a b = T1 a b  -- The "representation" type
--       It is TPair, not T, that is given to mkOneConFull
--
--  * 'con' K is a constructor of data type T
--
-- After instantiating the universal tyvars of K we get
--          K tys :: forall bs. Q => s1 .. sn -> T tys
--
-- Results: ValAbs:          K (y1::s1) .. (yn::sn)
--          [PmConstraint]:  Q, x ~ K y1..yn

mkOneConFull x usupply con = (con_abs, constraints)
  where

    (usupply1, usupply2, usupply3) = splitUniqSupply3 usupply

    res_ty = idType x -- res_ty == TyConApp (dataConTyCon (cabs_con cabs)) (cabs_arg_tys cabs)
    (univ_tvs, ex_tvs, eq_spec, thetas, arg_tys, _dc_res_ty) = dataConFullSig con
    data_tc = dataConTyCon con   -- The representation TyCon
    tc_args = case splitTyConApp_maybe res_ty of
                 Just (tc, tys) -> ASSERT( tc == data_tc ) tys
                 Nothing -> pprPanic "mkOneConFull: Not TyConApp:" (ppr res_ty)

    subst1  = zipTopTvSubst univ_tvs tc_args

    -- IS THE SECOND PART OF THE TUPLE THE SET OF FRESHENED EXISTENTIALS? MUST BE
    (subst, ex_tvs') = cloneTyVarBndrs subst1 ex_tvs usupply1

    arguments  = mkConVars usupply2 (substTys subst arg_tys)      -- Constructor arguments (value abstractions)
    theta_cs   = substTheta subst (eqSpecPreds eq_spec ++ thetas) -- All the constraints bound by the constructor
    evvars     = zipWith (nameType "oneCon") (listSplitUniqSupply usupply3) theta_cs
    con_abs    = PmCon { pm_con_con     = con
                       , pm_con_arg_tys = tc_args
                       , pm_con_tvs     = ex_tvs'
                       , pm_con_dicts   = evvars
                       , pm_con_args    = arguments }

    constraints = [ TmConstraint x (pmPatToPmExpr con_abs)
                  , TyConstraint evvars ] -- Both term and type constraints

mkConVars :: UniqSupply -> [Type] -> [ValAbs] -- ys, fresh with the given type
mkConVars us tys = zipWith mkValAbsVar (listSplitUniqSupply us) tys


tailValSetAbs :: ValSetAbs -> ValSetAbs
tailValSetAbs Empty               = Empty
tailValSetAbs Singleton           = panic "tailValSetAbs: Singleton"
tailValSetAbs (Union vsa1 vsa2)   = tailValSetAbs vsa1 `mkUnion` tailValSetAbs vsa2
tailValSetAbs (Constraint cs vsa) = cs `mkConstraint` tailValSetAbs vsa
tailValSetAbs (Cons _ vsa)        = vsa -- actual work

-- update this (pass the additional (type-related) arguments)
wrapK :: DataCon -> [Type] -> [TyVar] -> [EvVar] -> ValSetAbs -> ValSetAbs
wrapK con arg_tys ex_tvs dicts = wrapK_aux (dataConSourceArity con) emptylist
  where
    wrapK_aux :: Int -> DList ValAbs -> ValSetAbs -> ValSetAbs
    wrapK_aux _ _    Empty               = Empty
    wrapK_aux 0 args vsa                 = VA (PmCon { pm_con_con  = con, pm_con_arg_tys = arg_tys
                                                     , pm_con_tvs  = ex_tvs, pm_con_dicts = dicts
                                                     , pm_con_args = toList args }) `mkCons` vsa
    wrapK_aux _ _    Singleton           = panic "wrapK: Singleton"
    wrapK_aux n args (Cons vs vsa)       = wrapK_aux (n-1) (args `snoc` vs) vsa
    wrapK_aux n args (Constraint cs vsa) = cs `mkConstraint` wrapK_aux n args vsa
    wrapK_aux n args (Union vsa1 vsa2)   = wrapK_aux n args vsa1 `mkUnion` wrapK_aux n args vsa2

newtype DList a = DL { unDL :: [a] -> [a] }

toList :: DList a -> [a]
toList = ($[]) . unDL
{-# INLINE toList #-}

emptylist :: DList a
emptylist = DL id
{-# INLINE emptylist #-}

infixl `snoc`
snoc :: DList a -> a -> DList a
snoc xs x = DL (unDL xs . (x:))
{-# INLINE snoc #-}

-- ----------------------------------------------------------------------------
-- | Smart Value Set Abstraction constructors
-- (NB: An empty value set can only be represented as `Empty')

mkConstraint :: [PmConstraint] -> ValSetAbs -> ValSetAbs
-- The smart constructor for Constraint (maintains VsaInvariant)
mkConstraint _cs Empty                = Empty
mkConstraint cs1 (Constraint cs2 vsa) = Constraint (cs1++cs2) vsa -- careful about associativity
mkConstraint cs  other_vsa            = Constraint cs other_vsa

mkUnion :: ValSetAbs -> ValSetAbs -> ValSetAbs
-- The smart constructor for Union (maintains VsaInvariant)
mkUnion Empty vsa = vsa
mkUnion vsa Empty = vsa
mkUnion vsa1 vsa2 = Union vsa1 vsa2

mkCons :: ValAbs -> ValSetAbs -> ValSetAbs
-- The smart constructor for Cons (maintains VsaInvariant)
mkCons _ Empty = Empty
mkCons va vsa  = Cons va vsa

-- ----------------------------------------------------------------------------
-- | More smart constructors and fresh variable generation

mkGuard :: PatVec -> HsExpr Id -> Pattern
mkGuard pv e = PmGuard pv (hsExprToPmExpr e)

mkPmVar :: UniqSupply -> Type -> PmPat p
mkPmVar usupply ty = PmVar (mkPmId usupply ty)

idPatternVar :: Id -> Pattern
idPatternVar x = NonGuard (PmVar x)

mkPatternVar :: UniqSupply -> Type -> Pattern
mkPatternVar us ty = NonGuard (mkPmVar us ty)

mkValAbsVar :: UniqSupply -> Type -> ValAbs
mkValAbsVar us ty = VA (mkPmVar us ty)

mkPatternVarSM :: Type -> UniqSM Pattern
mkPatternVarSM ty = flip mkPatternVar ty <$> getUniqueSupplyM

mkPatternVarsSM :: [Type] -> UniqSM PatVec
mkPatternVarsSM tys = mapM mkPatternVarSM tys

mkPmId :: UniqSupply -> Type -> Id
mkPmId usupply ty = mkLocalId name ty
  where
    unique  = uniqFromSupply usupply
    occname = mkVarOccFS (fsLit (show unique))
    name    = mkInternalName unique occname noSrcSpan

mkPmIdM :: Type -> UniqSM Id
mkPmIdM ty = flip mkPmId ty <$> getUniqueSupplyM

mkPmId2FormsSM :: Type -> UniqSM (Pattern, LHsExpr Id)
mkPmId2FormsSM ty = do
  us <- getUniqueSupplyM
  let x = mkPmId us ty
  return (idPatternVar x, noLoc (HsVar x))

-- ----------------------------------------------------------------------------
-- | Converting between Value Abstractions, Patterns and PmExpr

hsLitToPmExpr :: HsLit -> PmExpr
hsLitToPmExpr lit = PmExprLit (PmSLit lit)

valAbsToPmExpr :: ValAbs -> PmExpr
valAbsToPmExpr (VA va) = pmPatToPmExpr va

pmPatToPmExpr :: PmPat ValAbs -> PmExpr
pmPatToPmExpr (PmCon { pm_con_con  = c
                     , pm_con_args = ps }) = PmExprCon c (map valAbsToPmExpr ps)
pmPatToPmExpr (PmVar { pm_var_id   = x  }) = PmExprVar x

-- Convert a pattern vector to a value list abstraction by dropping the guards
-- recursively (See NOTE [Translating As Patterns])
coercePatVec :: PatVec -> [ValAbs]
coercePatVec pv = [ VA (coercePmPat p) | NonGuard p <- pv]

coercePmPat :: PmPat Pattern -> PmPat ValAbs
coercePmPat (PmVar { pm_var_id  = x }) = PmVar { pm_var_id  = x }
coercePmPat (PmCon { pm_con_con = con, pm_con_arg_tys = arg_tys
                   , pm_con_tvs = tvs, pm_con_dicts = dicts
                   , pm_con_args = args })
  = PmCon { pm_con_con  = con, pm_con_arg_tys = arg_tys
          , pm_con_tvs  = tvs, pm_con_dicts = dicts
          , pm_con_args = coercePatVec args }

no_fixity :: a -- CHECKME: Can we retrieve the fixity from the operator name?
no_fixity = panic "Check: no fixity"

-- Get all constructors in the family (including given)
allConstructors :: DataCon -> [DataCon]
allConstructors = tyConDataCons . dataConTyCon

-- -----------------------------------------------------------------------
-- | Types and constraints

newEvVar :: Name -> Type -> EvVar
newEvVar name ty = mkLocalId name (toTcType ty)

nameType :: String -> UniqSupply -> Type -> EvVar
nameType name usupply ty = newEvVar idname ty
  where
    unique  = uniqFromSupply usupply
    occname = mkVarOccFS (fsLit (name++"_"++show unique))
    idname  = mkInternalName unique occname noSrcSpan

valSetAbsToList :: ValSetAbs -> [([ValAbs],[PmConstraint])]
valSetAbsToList Empty               = []
valSetAbsToList (Union vsa1 vsa2)   = valSetAbsToList vsa1 ++ valSetAbsToList vsa2
valSetAbsToList Singleton           = [([],[])]
valSetAbsToList (Constraint cs vsa) = [(vs, cs ++ cs') | (vs, cs') <- valSetAbsToList vsa]
valSetAbsToList (Cons va vsa)       = [(va:vs, cs) | (vs, cs) <- valSetAbsToList vsa]

splitConstraints :: [PmConstraint] -> ([EvVar], [(Id, PmExpr)], Maybe Id) -- Type constraints, term constraints, forced variables
splitConstraints [] = ([],[],Nothing)
splitConstraints (c : rest)
  = case c of
      TyConstraint cs  -> (cs ++ ty_cs, tm_cs, bot_cs)
      TmConstraint x e -> (ty_cs, (x,e):tm_cs, bot_cs)
      BtConstraint cs  -> ASSERT (isNothing bot_cs) (ty_cs, tm_cs, Just cs) -- NB: Only one x ~ _|_
  where
    (ty_cs, tm_cs, bot_cs) = splitConstraints rest

{-
%************************************************************************
%*                                                                      *
\subsection{The oracles}
%*                                                                      *
%************************************************************************
-}

anySatValSetAbs :: ValSetAbs -> PmM Bool
anySatValSetAbs vsa = isNotEmpty <$> pruneValSetAbsBound 1 vsa

-- TAKE THE INT AS AN ARGUMENT
pruneValSetAbs :: ValSetAbs -> PmM [(ValVecAbs,([ComplexEq], PmVarEnv))]
pruneValSetAbs vsa = pruneValSetAbsBoundVec 5 vsa

pruneValSetAbsBound :: Int -> ValSetAbs -> PmM ValSetAbs
pruneValSetAbsBound n v = fst <$> pruneValSetAbsBound' n init_cs v
  where
    init_cs :: ([EvVar], TmState, Maybe Id)
    init_cs = ([], initialTmState, Nothing)

    pruneValSetAbsBound' :: Int -> ([EvVar], TmState, Maybe Id) -> ValSetAbs -> PmM (ValSetAbs, Int) -- how many left. @$#%$ Union!
    pruneValSetAbsBound' n all_cs@(ty_cs, tm_env, bot_ct) in_vsa
      | n <= 0    = return (Empty, 0) -- no need to keep going
      | otherwise = case in_vsa of
          Empty -> return (Empty, n)
          Union vsa1 vsa2 -> do
            (vsa1', m) <- pruneValSetAbsBound' n all_cs vsa1
            (vsa2', k) <- pruneValSetAbsBound' m all_cs vsa2
            return (mkUnion vsa1' vsa2', k)
          Singleton -> do -- return (Singleton, n-1)
            sat <- tyOracle (listToBag ty_cs) -- it would be nice to have this incremental too
            return $ case sat of
              True  -> (Singleton, n-1)
              False -> (Empty, n)
          Constraint cs vsa -> case splitConstraints cs of -- undefined {- FIXME -}
            (new_ty_cs, new_tm_cs, new_bot_ct) -> case tmOracle tm_env new_tm_cs of
              Just (new_tm_env@(residual, (expr_eqs, subst))) ->
                let bot = mergeBotCs new_bot_ct bot_ct
                    ans = isNothing bot || notNull residual || expr_eqs || notForced (fromJust bot) subst
                in  case ans of
                      True  -> pruneValSetAbsBound' n (new_ty_cs++ty_cs, new_tm_env, bot) vsa
                      False -> return (Empty, n)
              Nothing -> return (Empty, n)
          Cons va vsa -> do
            (vsa', m) <- pruneValSetAbsBound' n all_cs vsa
            return (mkCons va vsa', m)

mergeBotCs :: Maybe Id -> Maybe Id -> Maybe Id
mergeBotCs (Just x) Nothing  = Just x
mergeBotCs Nothing  (Just y) = Just y
mergeBotCs Nothing  Nothing  = Nothing
mergeBotCs (Just _) (Just _) = panic "mergeBotCs: two (x ~ _|_) constraints"

wrapUpTmState :: TmState -> ([ComplexEq], PmVarEnv)
wrapUpTmState (residual, (_unhandled, subst)) = (residual, flattenPmVarEnv subst)

pruneValSetAbsBoundVec :: Int -> ValSetAbs -> PmM [(ValVecAbs,([ComplexEq], PmVarEnv))]
pruneValSetAbsBoundVec n v = fst <$> pruneValSetAbsBoundVec' n init_cs emptylist v
  where
    init_cs :: ([EvVar], TmState, Maybe Id)
    init_cs = ([], initialTmState, Nothing)

    pruneValSetAbsBoundVec' :: Int -> ([EvVar], TmState, Maybe Id) -> DList ValAbs -> ValSetAbs -> PmM ([(ValVecAbs,([ComplexEq], PmVarEnv))], Int)
    pruneValSetAbsBoundVec' n all_cs@(ty_cs, tm_env, bot_ct) vec in_vsa
      | n <= 0    = return ([], 0) -- no need to keep going
      | otherwise = case in_vsa of
          Empty -> return ([], n)
          Union vsa1 vsa2 -> do
            (vecs1, m) <- pruneValSetAbsBoundVec' n all_cs vec vsa1
            (vecs2, k) <- pruneValSetAbsBoundVec' m all_cs vec vsa2
            return (vecs1 ++ vecs2, k)
          Singleton -> do -- return (Singleton, n-1)
            sat <- tyOracle (listToBag ty_cs) -- it would be nice to have this incremental too
            return $ case sat of
              True  -> ([(toList vec, wrapUpTmState tm_env)], n-1)
              False -> ([], n)
          Constraint cs vsa -> case splitConstraints cs of -- undefined {- FIXME -}
            (new_ty_cs, new_tm_cs, new_bot_ct) -> case tmOracle tm_env new_tm_cs of
                Just (new_tm_env@(residual, (expr_eqs, subst))) ->
                  let bot = mergeBotCs new_bot_ct bot_ct
                      ans = isNothing bot || notNull residual || expr_eqs || notForced (fromJust bot) subst
                  in  case ans of
                        True  -> pruneValSetAbsBoundVec' n (new_ty_cs++ty_cs, new_tm_env, bot) vec vsa
                        False -> return ([], n)
                Nothing -> return ([], n)
          Cons va vsa -> pruneValSetAbsBoundVec' n all_cs (vec `snoc` va) vsa

isNotEmpty :: ValSetAbs -> Bool
isNotEmpty Empty = False
isNotEmpty _vsa  = True

-- we need to decouple this from the tc. for now let's redo it
prunePure :: ValSetAbs -> ValSetAbs
prunePure = prunePureVSA (initialTmState, Nothing)
  where
    prunePureVSA :: (TmState, Maybe Id) -> ValSetAbs -> ValSetAbs
    prunePureVSA all_cs@(tm_env, bot_ct) in_vsa = case in_vsa of
      Empty             -> Empty
      Union vsa1 vsa2   -> prunePureVSA all_cs vsa1 `mkUnion` prunePureVSA all_cs vsa2
      Singleton         -> Singleton
      Cons va vsa       -> va `mkCons` prunePureVSA all_cs vsa
      Constraint cs vsa -> case splitConstraints cs of
        (ty_cs, new_tm_cs, new_bot_ct) -> case tmOracle tm_env new_tm_cs of
          Just (new_tm_env@(residual, (expr_eqs, subst))) ->
            let bot = mergeBotCs new_bot_ct bot_ct
                ans = isNothing bot || notNull residual || expr_eqs || notForced (fromJust bot) subst
            in  if ans then cs `mkConstraint` prunePureVSA (new_tm_env, bot) vsa
                       else Empty
          Nothing -> Empty

-- ----------------------------------------------------------------------------
-- ----------------------------------------------------------------------------

-- It checks whether a set of type constraints is satisfiable.
tyOracle :: Bag EvVar -> PmM Bool
tyOracle evs
  = do { ((_warns, errs), res) <- initTcDsForSolver $ tcCheckSatisfiability evs
       ; case res of
            Just sat -> return sat
            Nothing  -> pprPanic "tyOracle" (vcat $ pprErrMsgBagWithLoc errs) }

{-
Note [Pattern match check give up]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We don't give up anymore. Check our behaviour on these cases.

A simple example is trac #322:
\begin{verbatim}
  f :: Maybe Int -> Int
  f 1 = 1
  f Nothing = 2
  f _ = 3
\end{verbatim}
-}

{-
%************************************************************************
%*                                                                      *
\subsection{Sanity Checks}
%*                                                                      *
%************************************************************************
-}

-- ADD ASSERTS EVERYWHERE, THEY COME *FOR FREE* (ACTIVATED ONLY WHEN DEBUGISON)
type PmArity = Int

patVecArity :: PatVec -> PmArity
patVecArity = sum . map patternArity

patternArity :: Pattern -> PmArity
patternArity (PmGuard  {}) = 0
patternArity (NonGuard {}) = 1

-- Should get a default value because an empty set has any arity
-- (We have no value vector abstractions to see)
vsaArity :: PmArity -> ValSetAbs -> PmArity
vsaArity  arity Empty = arity
vsaArity _arity vsa   = ASSERT (allTheSame arities) (head arities)
  where arities = vsaArities vsa

vsaArities :: ValSetAbs -> [PmArity] -- Arity for every path. INVARIANT: All the same
vsaArities Empty              = []
vsaArities (Union vsa1 vsa2)  = vsaArities vsa1 ++ vsaArities vsa2
vsaArities Singleton          = [0]
vsaArities (Constraint _ vsa) = vsaArities vsa
vsaArities (Cons _ vsa)       = [1 + arity | arity <- vsaArities vsa]

allTheSame :: Eq a => [a] -> Bool
allTheSame []     = True
allTheSame (x:xs) = all (==x) xs

sameArity :: PatVec -> ValSetAbs -> Bool
sameArity pv vsa = vsaArity pv_a vsa == pv_a
  where pv_a = patVecArity pv

{-
%************************************************************************
%*                                                                      *
\subsection{Heart of the algorithm: Function patVectProc}
%*                                                                      *
%************************************************************************
-}

patVectProc :: (PatVec, [PatVec]) -> ValSetAbs -> PmM (Bool, Bool, ValSetAbs) -- Covers? Forces? U(n+1)?
patVectProc (vec,gvs) vsa = do
  us <- getUniqueSupplyM
  let (c_def, u_def, d_def) = process_guards us gvs -- default (the continuation)
  (usC, usU, usD) <- getUniqueSupplyM3
  mb_c <- anySatValSetAbs $ prunePure (covered   usC c_def vec vsa)
  mb_d <- anySatValSetAbs $ prunePure (divergent usD d_def vec vsa)
  let vsa' = prunePure $ uncovered usU u_def vec vsa
  return (mb_c, mb_d, vsa')

-- | Covered, Uncovered, Divergent
covered, uncovered, divergent :: UniqSupply -> ValSetAbs -> PatVec -> ValSetAbs -> ValSetAbs
covered   us gvsa vec vsa = pmTraverse us gvsa cMatcher vec vsa
uncovered us gvsa vec vsa = pmTraverse us gvsa uMatcher vec vsa
divergent us gvsa vec vsa = pmTraverse us gvsa dMatcher vec vsa

-- ----------------------------------------------------------------------------
-- | Generic traversal function
--
-- | Because we represent Value Set Abstractions as a different datatype, more
-- cases than the ones described in the paper appear. Since they are the same
-- for all three functions (covered, uncovered, divergent), function
-- `pmTraverse' handles these cases (`pmTraverse' also takes care of the
-- Guard-Case since it is common for all). The actual work is done by functions
-- `cMatcher', `uMatcher' and `dMatcher' below.

pmTraverse :: UniqSupply
           -> ValSetAbs -- gvsa
           -> PmMatcher -- what to do
           -> PatVec
           -> ValSetAbs
           -> ValSetAbs
pmTraverse _us _gvsa _rec _vec Empty      = Empty
pmTraverse _us  gvsa _rec []   Singleton  = gvsa
pmTraverse _us _gvsa _rec []   (Cons _ _) = panic "pmTraverse: cons"
pmTraverse  us  gvsa  rec vec  (Union vsa1 vsa2)
  = mkUnion (pmTraverse us1 gvsa rec vec vsa1)
            (pmTraverse us2 gvsa rec vec vsa2)
  where (us1, us2) = splitUniqSupply us
pmTraverse us gvsa rec vec (Constraint cs vsa)
  = mkConstraint cs (pmTraverse us gvsa rec vec vsa)
pmTraverse us gvsa rec (p:ps) vsa =
  case p of
    -- Guard Case
    PmGuard pv e ->
      let (us1, us2) = splitUniqSupply us
          y  = mkPmId us1 (patternType p)
          cs = [TmConstraint y e]
      in  mkConstraint cs $ tailValSetAbs $
            pmTraverse us2 gvsa rec (pv++ps) (VA (PmVar y) `mkCons` vsa)

    -- Constructor/Variable/Literal Case
    NonGuard pat
      | Cons (VA va) vsa <- vsa -> rec us gvsa pat ps va vsa
      | otherwise               -> panic "pmTraverse: singleton" -- can't be anything else

type PmMatcher =  UniqSupply
               -> ValSetAbs
               -> PmPat Pattern -> PatVec -- pattern vector head and tail
               -> PmPat ValAbs  -> ValSetAbs -- value set abstraction head and tail
               -> ValSetAbs

cMatcher, uMatcher, dMatcher :: PmMatcher

-- | cMatcher
-- ----------------------------------------------------------------------------

-- CVar
cMatcher us gvsa (PmVar x) ps va vsa
  = VA va `mkCons` (cs `mkConstraint` covered us gvsa ps vsa)
  where cs = [TmConstraint x (pmPatToPmExpr va)]

-- CConCon
cMatcher us gvsa (p@(PmCon { pm_con_con = c1, pm_con_args = args1 })) ps
                    (PmCon { pm_con_con = c2, pm_con_args = args2 }) vsa
  | c1 /= c2  = Empty
  | otherwise = wrapK c1 (pm_con_arg_tys p)
                         (pm_con_tvs     p)
                         (pm_con_dicts   p)
                         (covered us gvsa (args1 ++ ps) (foldr mkCons vsa args2))

-- CConVar
cMatcher us gvsa (p@(PmCon { pm_con_con = con })) ps (PmVar x) vsa
  = cMatcher us2 gvsa p ps con_abs (mkConstraint all_cs vsa)
  where
    (us1, us2)        = splitUniqSupply us
    (con_abs, all_cs) = mkOneConFull x us1 con

-- | uMatcher
-- ----------------------------------------------------------------------------

-- UVar
uMatcher us gvsa (PmVar x) ps va vsa
  = VA va `mkCons` (cs `mkConstraint` uncovered us gvsa ps vsa)
  where cs = [TmConstraint x (pmPatToPmExpr va)]

-- UConCon
uMatcher us gvsa ( p@(PmCon { pm_con_con = c1, pm_con_args = args1 })) ps
                 (va@(PmCon { pm_con_con = c2, pm_con_args = args2 })) vsa
  | c1 /= c2  = VA va `mkCons` vsa
  | otherwise = wrapK c1 (pm_con_arg_tys p)
                         (pm_con_tvs     p)
                         (pm_con_dicts   p)
                         (uncovered us gvsa (args1 ++ ps) (foldr mkCons vsa args2))

-- UConVar
uMatcher us gvsa (p@(PmCon { pm_con_con = con })) ps (PmVar x) vsa
  = uncovered us2 gvsa (NonGuard p : ps) inst_vsa -- instantiated vsa [x \mapsto K_j ys]
  where
    -- Some more uniqSupplies
    (us1, us2) = splitUniqSupply us

    -- Unfold the variable to all possible constructor patterns
    cons_cs    = zipWith (mkOneConFull x) (listSplitUniqSupply us1) (allConstructors con)
    add_one (va,cs) valset = valset `mkUnion` (VA va `mkCons` (cs `mkConstraint` vsa))
    inst_vsa   = foldr add_one Empty cons_cs

-- | dMatcher
-- ----------------------------------------------------------------------------

-- DVar
dMatcher us gvsa (PmVar x) ps va vsa
  = VA va `mkCons` (cs `mkConstraint` divergent us gvsa ps vsa)
  where cs = [TmConstraint x (pmPatToPmExpr va)]

-- DConCon
dMatcher us gvsa (p@(PmCon { pm_con_con = c1, pm_con_args = args1 })) ps
                    (PmCon { pm_con_con = c2, pm_con_args = args2 }) vsa
  | c1 /= c2  = Empty
  | otherwise = wrapK c1 (pm_con_arg_tys p)
                         (pm_con_tvs     p)
                         (pm_con_dicts   p)
                         (divergent us gvsa (args1 ++ ps) (foldr mkCons vsa args2))

-- DConVar
dMatcher us gvsa (p@(PmCon { pm_con_con = con })) ps (PmVar x) vsa
  = mkUnion (VA (PmVar x) `mkCons` mkConstraint [BtConstraint x] vsa)
            (dMatcher us2 gvsa p ps con_abs (mkConstraint all_cs vsa))
  where
    (us1, us2)        = splitUniqSupply us
    (con_abs, all_cs) = mkOneConFull x us1 con

{-
%************************************************************************
%*                                                                      *
\subsection{Pretty Printing}
%*                                                                      *
%************************************************************************
-}

-- instance Outputable PmConstraint where
--   ppr (TmConstraint x e)   = ptext (sLit "{|") <> ppr x <+> ptext (sLit "=:=") <+> ppr e <> ptext (sLit "|}")
--   ppr (TyConstraint ty_cs) | null ty_cs = empty
--                            | otherwise  = braces $ interpp'SP $ map idType ty_cs
--   ppr (BtConstraint x)     = ptext (sLit "{|") <> ppr x <+> ptext (sLit "~ _|_") <> ptext (sLit "|}")

instance Outputable ValAbs where
  ppr = ppr . valAbsToPmExpr

pprUncovered :: [(ValVecAbs,([ComplexEq], PmVarEnv))] -> [SDoc]
pprUncovered missing = map pprOne missing

ppr_constraint :: (SDoc,[PmLit]) -> SDoc
ppr_constraint (var, lits) = var <+> ptext (sLit "is not one of") <+> ppr lits

pprOne :: (ValVecAbs,([ComplexEq], PmVarEnv)) -> SDoc
pprOne (vs,(complex, subst)) =
  let expr_vec = map (exprDeepLookup subst . valAbsToPmExpr) vs -- vec as a list of expressions (apply the subst returned by the solver,  ValAbs <: PmExpr)
      sdoc_vec = mapM pprPmExprWithParens expr_vec
      (vec,cs) = runPmPprM sdoc_vec (filterComplex complex)
  in  if null cs
        then fsep vec -- there are no literal constraints
        else hang (fsep vec) 4 $ ptext (sLit "where") <+> vcat (map ppr_constraint cs)


-- ----------------------------------------------------------------------------
-- | Propagation of term constraints inwards when checking nested matches

{-
NOTE [Type and Term Equality Propagation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When checking a match it would be great to have all type and term information
available so we can get more precise results. For this reason we have functions
`addDictsDs' and `addTmCsDs' in DsMonad that store in the environment type and
term constraints (respectively) as we go deeper.

The type constraints we propagate inwards are collected by `collectEvVarsPats'
in HsPat.hs. This handles bug #4139 ( see example
  https://ghc.haskell.org/trac/ghc/attachment/ticket/4139/GADTbug.hs )
where this is needed.

For term equalities we do less, we just generate equalities for HsCase. For
example we accurately give 2 redundancy warnings for the marked cases:

f :: [a] -> Bool
f x = case x of

  []    -> case x of        -- brings (x ~ []) in scope
             []    -> True
             (_:_) -> False -- can't happen

  (_:_) -> case x of        -- brings (x ~ (_:_)) in scope
             (_:_) -> True
             []    -> False -- can't happen

Functions `genCaseTmCs1' and `genCaseTmCs2' are responsible for generating
these constraints.
-}

-- | Generate equalities when checking a case expression:
--     case x of { p1 -> e1; ... pn -> en }
-- When we go deeper to check e.g. e1 we record two equalities:
-- (x ~ y), where y is the initial uncovered when checking (p1; .. ; pn)
-- and (x ~ p1).
genCaseTmCs2 :: Maybe (LHsExpr Id) -- Scrutinee
             -> [Pat Id]           -- LHS       (should have length 1)
             -> [Id]               -- MatchVars (should have length 1)
             -> DsM (Bag SimpleEq)
genCaseTmCs2 Nothing _ _ = return emptyBag
genCaseTmCs2 (Just scr) [p] [var] = liftUs $ do
  [e] <- map valAbsToPmExpr . coercePatVec <$> translatePat p
  let scr_e = lhsExprToPmExpr scr
  return $ listToBag [(var, e), (var, scr_e)]
genCaseTmCs2 _ _ _ = panic "genCaseTmCs2: HsCase"

-- | Generate a simple equality when checking a case expression:
--     case x of { matches }
-- When checking matches we record that (x ~ y) where y is the initial
-- uncovered. All matches will have to satisfy this equality.
genCaseTmCs1 :: Maybe (LHsExpr Id) -> [Id] -> Bag SimpleEq
genCaseTmCs1 Nothing     _    = emptyBag
genCaseTmCs1 (Just scr) [var] = unitBag (var, lhsExprToPmExpr scr)
genCaseTmCs1 _ _              = panic "genCaseTmCs1: HsCase"

{-
NOTE [Literals in PmPat]
~~~~~~~~~~~~~~~~~~~~~~~~
Instead of translating a literal to a variable accompanied with a guard, we
treat them like constructor patterns. The following example from
"./libraries/base/GHC/IO/Encoding.hs" shows why:

mkTextEncoding' :: CodingFailureMode -> String -> IO TextEncoding
mkTextEncoding' cfm enc = case [toUpper c | c <- enc, c /= '-'] of
    "UTF8"    -> return $ UTF8.mkUTF8 cfm
    "UTF16"   -> return $ UTF16.mkUTF16 cfm
    "UTF16LE" -> return $ UTF16.mkUTF16le cfm
    ...

Each clause gets translated to a list of variables with an equal number of
guards. For every guard we generate two cases (equals True/equals False) which
means that we generate 2^n cases to feed the oracle with, where n is the sum of
the length of all strings that appear in the patterns. For this particular
example this means over 2^40 cases. Instead, by representing them like with
constructor we get the following:
  1. We exploit the common prefix with our representation of Value Set Abstractions
  2. We prune immediately non-reachable cases
     (e.g. False == (x == "U"), True == (x == "U"))
-}


{-
NOTE [Translating As Patterns]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Instead of translating x@p as:  x (p <- x)
we instead translate it as:     p (x <- coercePattern p)
for performance reasons. For example:

  f x@True  = 1
  f y@False = 2

Gives the following with the first translation:

  x |> {x == False, x == y, y == True}

If we use the second translation we get an empty set, independently of the
oracle. Since the pattern `p' may contain guard patterns though, it cannot be
used as an expression. That's why we call `coercePatVec' to drop the guard and
`valAbsToPmExpr' to transform the value abstraction to an expression in the
guard pattern (value abstractions are a subset of expressions). We keep the
guards in the first pattern `p' though.
-}
