{-# LANGUAGE OverloadedStrings #-}

module Check where

import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class (lift)
import Control.Monad.Error.Class (throwError)
import Control.Monad (unless, when)

import qualified Data.Set as Set
import Data.Set (Set)
import Data.List (find)
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Text as Text

import Types
import Utils
import Dot

runTyCheck :: Ctx -> Expr -> Ty -> Result Ctx
runTyCheck ctx term ty =
  flip evalStateT initMetaData $ tyCheck ctx term ty

runTyInfer :: Ctx -> Expr -> Result (Ty, Ctx)
runTyInfer ctx =
  flip evalStateT initMetaData . tyInfer ctx

constructJudgmentGraph :: Ctx -> Expr -> Maybe Ty -> Result JudgmentGraph
constructJudgmentGraph ctx e mTy = case mTy of
  Nothing -> fmap (constructGraph . judgmentBuilder) $
    flip execStateT initMetaData $ tyInfer ctx e
  Just checkTy -> fmap (constructGraph . judgmentBuilder) $
    flip execStateT initMetaData $ tyCheck ctx e checkTy
  where
    constructGraph gBuilder = G.mkGraph (nodes gBuilder) (edges gBuilder)

dotJudgmentGraph :: Ctx -> Expr -> Maybe Ty -> String -> IO ()
dotJudgmentGraph ctx e mTy s =
  let graphRes = constructJudgmentGraph ctx e mTy
  in case graphRes of
    Left err -> print err
    Right g -> dotToFile s g

freeVars :: Ty -> Set Ty
freeVars UnitTy               = Set.empty
freeVars (TyVar varName)      = Set.singleton (TyVar varName)
freeVars (TyVarHat varName)   = Set.singleton (TyVarHat varName)
freeVars (TyArrow tyA tyB)    = Set.union (freeVars tyA) (freeVars tyB)
freeVars (Forall varName ty)  = Set.delete (TyVar varName) $ freeVars ty

isMonotype :: Ty -> Bool
isMonotype (Forall _ _) = False
isMonotype (TyArrow tyA tyB) = isMonotype tyA && isMonotype tyB
isMonotype _ = True

-- NOTE: We follow the first notation
-- 1. [alpha := alphaHat]
-- 2. in the paper, it's [alphaHat / alpha]
tySubst :: Ty -> Ty -> Ty -> Ty
tySubst alpha alphaHat UnitTy = UnitTy
tySubst alpha alphaHat (TyVar alphaName) = 
  if TyVar alphaName == alpha then alphaHat else TyVar alphaName
tySubst alpha alphaHat (TyVarHat alphaName) = TyVarHat alphaName
tySubst alpha alphaHat (TyArrow tyA tyB) = TyArrow (tySubst alpha alphaHat tyA) (tySubst alpha alphaHat tyB) 
tySubst alpha alphaHat (Forall alphaName tyA) = Forall alphaName (tySubst alpha alphaHat tyA)


ctxSubst :: Ctx -> Ty -> Ty
ctxSubst ctx (TyVar alphaName) = TyVar alphaName
ctxSubst ctx UnitTy = UnitTy
ctxSubst ctx (TyVarHat alphaName) 
  | any hasEq ctx =
    ctxSubst ctx tau
  where
    hasEq (CtxEquality alphaName' _) = alphaName == alphaName'
    hasEq _ = False
    (Just (CtxEquality _ tau)) = find hasEq ctx
ctxSubst ctx (TyVarHat alphaName) = TyVarHat alphaName
ctxSubst ctx (TyArrow tyA tyB) = TyArrow (ctxSubst ctx tyA) (ctxSubst ctx tyB)
ctxSubst ctx (Forall alphaName tyA) = Forall alphaName (ctxSubst ctx tyA)

subTypeOf :: Ctx -> Ty -> Ty -> TyStateT Ctx
subTypeOf ctx tv0@(TyVar alpha0) tv1@(TyVar alpha1) = do
  -- throw error if they're not the same
  unless (alpha0 == alpha1) $ 
    throwError  $ Text.concat ["Type variable ", alpha0, " does not equal ", alpha1]
  createJudgmentTrace (SubtypeTrace "<:Var" (ctx, tv0, tv1)) []
  pure ctx

subTypeOf ctx UnitTy UnitTy = do
  createJudgmentTrace (SubtypeTrace "<:Unit" (ctx, UnitTy, UnitTy)) []
  pure ctx

subTypeOf ctx a1@(TyVarHat alpha0) a2@(TyVarHat alpha1) = do
  -- throw error if they're not the same
  unless (alpha0 == alpha1) $ 
    throwError $ Text.concat ["Type variable ", alpha0, "Hat does not equal ", alpha1, "Hat"]
  createJudgmentTrace (SubtypeTrace "<:Exvar" (ctx, a1, a2)) []
  pure ctx

subTypeOf ctx a1@(TyArrow tyA1 tyA2) a2@(TyArrow tyB1 tyB2) = do
  ctxOmega <- subTypeOf ctx tyB1 tyA1
  n1 <- getNode
  ctxDelta <- subTypeOf ctxOmega (ctxSubst ctxOmega tyA2) (ctxSubst ctxOmega tyB2)
  n2 <- getNode
  createJudgmentTrace (SubtypeTrace "<:->" (ctx, a1, a2)) [(n1, SubtypeOf), (n2, SubtypeOf)]
  pure ctxDelta

subTypeOf ctx forTy@(Forall alphaName tyA) tyB = do
  let ctxExtended = ctx <: CtxMarker alphaName <: CtxItemHat alphaName
  ctxDeltaMarkerOmega <- subTypeOf ctxExtended (tySubst (TyVar alphaName) (TyVarHat alphaName) tyA) tyB
  n <- getNode
  createJudgmentTrace (SubtypeTrace "<:Forall-L" (ctx, forTy, tyB)) [(n, SubtypeOf)]
  pure $ takeUntilVar (CtxMarker alphaName) ctxDeltaMarkerOmega

subTypeOf ctx tyA forTy@(Forall alphaName tyB) = do
  let ctxExtended = ctx <: CtxItem alphaName
  ctxDeltaAlphaOmega <- subTypeOf ctxExtended tyA tyB
  n <- getNode
  createJudgmentTrace (SubtypeTrace "<:Forall-R" (ctx, tyA, forTy)) [(n, SubtypeOf)]
  pure $ takeUntilVar (CtxItem alphaName) ctxDeltaAlphaOmega

subTypeOf ctx aHat@(TyVarHat alphaName) tyA = do
  when (Set.member (TyVarHat alphaName) $ freeVars tyA) $
    throwError $ Text.concat["Type variable ", alphaName, "Hat exists as a free variable in the given type."]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]
  ctxDelta <- instL ctx (TyVarHat alphaName) tyA
  n <- getNode
  createJudgmentTrace (SubtypeTrace "<:InstantiateL" (ctx, aHat, tyA)) [(n, InstL)]
  pure ctxDelta

subTypeOf ctx tyA aHat@(TyVarHat alphaName) = do
  when (Set.member (TyVarHat alphaName) $ freeVars tyA) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat exists as a free variable in the given type."]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]
  ctxDelta <- instR ctx tyA (TyVarHat alphaName)
  n <- getNode
  createJudgmentTrace (SubtypeTrace "<:InstantiateR" (ctx, tyA, aHat)) [(n, InstR)]
  pure ctxDelta

instL :: Ctx -> Ty -> Ty -> TyStateT Ctx
instL ctx tvHat@(TyVarHat alphaName) tau = do
  unless (isMonotype tau) $
    throwError $ Text.concat ["Type ", Text.pack $ show tau, " is not a monotype"]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]
  let newItem = CtxEquality alphaName tau
      gammaAlphaTauGamma' = replaceItem (CtxItemHat alphaName) [newItem] ctx
  createJudgmentTrace (InstLTrace "InstLSolve" (ctx, tvHat, tau)) []
  pure gammaAlphaTauGamma'
instL ctx tvAlpha@(TyVarHat alphaName) tvBeta@(TyVarHat betaName) = do
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let (ctxL, ctxR) = splitOnItem (CtxItemHat alphaName) ctx
  unless ((CtxItemHat betaName) `elem` ctxR) $
    throwError $ Text.concat ["Type variable ", betaName, "Hat does not exist after ", alphaName, "Hat in the context."]

  createJudgmentTrace (InstLTrace "InstLReach" (ctx, tvAlpha, tvBeta)) []
  pure $ ctx |> replaceItem (CtxItemHat betaName) [CtxEquality betaName (TyVarHat alphaName)]
instL ctx tvHat@(TyVarHat alphaName) tArr@(TyArrow tyA1 tyA2) = do
  alphaHat1 <- getNewVar alphaName
  alphaHat2 <- getNewVar alphaName
  let alphaArrow = TyArrow (TyVarHat alphaHat1) (TyVarHat alphaHat2)
      newItems = [CtxItem alphaHat2, CtxItem alphaHat1, CtxEquality alphaName alphaArrow]
      replacedCtx = replaceItem (CtxItemHat alphaName) newItems ctx
  ctxOmega <- instR replacedCtx tyA1 (TyVarHat alphaHat1)
  n1 <- getNode
  ctxDelta <- instL ctxOmega (TyVarHat alphaHat2) (ctxSubst ctxOmega tyA2)
  n2 <- getNode
  createJudgmentTrace (InstLTrace "InstLArr" (ctx, tvHat, tArr)) [(n1, InstR), (n2, InstL)]
  pure ctxDelta 
instL ctx tyVarAlphaHat@(TyVarHat alphaName) forTy@(Forall betaName tyB) = do
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let ctxExtended = ctx <: (CtxItem betaName)

  ctxDeltaBetaDelta' <- instL ctxExtended tyVarAlphaHat tyB
  n <- getNode
  let ctxDelta = takeUntilVar (CtxItem betaName) ctxDeltaBetaDelta'
  createJudgmentTrace (InstLTrace "InstLAIIR" (ctx, tyVarAlphaHat, forTy)) [(n, InstL)]
  pure ctxDelta 

instR :: Ctx -> Ty -> Ty -> TyStateT Ctx
instR ctx tau tvHat@(TyVarHat alphaName) = do
  unless (isMonotype tau) $
    throwError $ Text.concat ["Type ", Text.pack $ show tau, " is not a monotype"]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]
  let newItem = CtxEquality alphaName tau
      gammaAlphaTauGamma' = replaceItem (CtxItemHat alphaName) [newItem] ctx
  createJudgmentTrace (InstRTrace "InstRSolve" (ctx, tvHat, tau)) []
  pure gammaAlphaTauGamma'
instR ctx tvBeta@(TyVarHat betaName) tvAlpha@(TyVarHat alphaName) = do
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let (ctxL, ctxR) = splitOnItem (CtxItemHat alphaName) ctx
  unless ((CtxItemHat betaName) `elem` ctxR) $
    throwError $ Text.concat ["Type variable ", betaName, "Hat does not exist after ", alphaName, "Hat in the context."]

  createJudgmentTrace (InstRTrace "InstRReach" (ctx, tvBeta, tvAlpha)) []
  pure $ ctx |> replaceItem (CtxItemHat betaName) [CtxEquality betaName (TyVarHat alphaName)]
instR ctx tArr@(TyArrow tyA1 tyA2) tvHat@(TyVarHat alphaName) = do
  alphaHat1 <- getNewVar alphaName
  alphaHat2 <- getNewVar alphaName
  let alphaArrow = TyArrow (TyVarHat alphaHat1) (TyVarHat alphaHat2)
      newItems = [CtxItem alphaHat2, CtxItem alphaHat1, CtxEquality alphaName alphaArrow]
      replacedCtx = replaceItem (CtxItemHat alphaName) newItems ctx
  ctxOmega <- instL replacedCtx (TyVarHat alphaHat1) tyA1
  n1 <- getNode
  ctxDelta <- instR ctxOmega (ctxSubst ctxOmega tyA2) (TyVarHat alphaHat2) 
  n2 <- getNode
  createJudgmentTrace (InstRTrace "InstRArr" (ctx, tArr, tvHat)) [(n1, InstL), (n2, InstR)]
  pure ctxDelta 
instR ctx forTy@(Forall betaName tyB)  tyVarAlphaHat@(TyVarHat alphaName) = do
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let ctxExtended = ctx <: CtxMarker betaName <: CtxItemHat betaName
      tyBSubst = tySubst (TyVar betaName) (TyVarHat betaName) tyB

  ctxDeltaMarkerDelta' <- instR ctxExtended tyBSubst tyVarAlphaHat
  n <- getNode
  
  let ctxDelta = takeUntilVar (CtxMarker betaName) ctxDeltaMarkerDelta'
  
  createJudgmentTrace (InstRTrace "InstRAIIL" (ctx, forTy, tyVarAlphaHat)) [(n, InstR)]
  pure ctxDelta 


tyCheck :: Ctx -> Expr -> Ty -> TyStateT Ctx
tyCheck ctx UnitTerm UnitTy = do
  createJudgmentTrace (AlgTypingTrace "1I" (ctx, UnitTerm, UnitTy)) []
  return ctx
tyCheck ctx (Lam x e) (TyArrow tyA tyB) = do
  ctxDeltaXAlphaOmega <- tyCheck ctxExtended e tyB
  let ctxDelta = takeUntilVar (CtxMapping x tyA) ctxDeltaXAlphaOmega
  n <- getNode
  createJudgmentTrace (AlgTypingTrace "->I" (ctx, Lam x e, TyArrow tyA tyB)) [(n, TyCheck)]
  return ctxDelta
  where
    ctxExtended = ctx <: CtxMapping x tyA
tyCheck ctx e (Forall alpha tyA) = do
  ctxDeltaAlphaOmega <- tyCheck (ctx <: CtxItem alpha) e tyA
  n <- getNode
  let ctxDelta = takeUntilVar (CtxItem alpha) ctxDeltaAlphaOmega
  createJudgmentTrace (AlgTypingTrace "Forall-I" (ctx, e, Forall alpha tyA)) [(n, TyCheck)]
  return ctxDelta
tyCheck ctx e tyB = do
  (tyA, ctxTheta) <- tyInfer ctx e
  n1 <- getNode

  ctxDelta <- ctxSubst ctxTheta tyA `subTypeOfCtx` ctxSubst ctxTheta tyB
  n2 <- getNode

  createJudgmentTrace (AlgTypingTrace "Sub" (ctx, e, tyB)) [(n1, TyInfer), (n2, SubtypeOf)]
  pure ctxDelta
  where
    subTypeOfCtx = subTypeOf ctx

tyInfer :: Ctx -> Expr -> TyStateT (Ty, Ctx)
tyInfer ctx (Var x) = do
  varFromCtx <- lift $ lookupVar lookupPred ctx errMsg
  createJudgmentTrace (AlgTypingTrace "Var" (ctx, Var x, tyItem varFromCtx)) []
  return (tyItem varFromCtx, ctx)
  where
    lookupPred :: CtxItem -> Bool
    lookupPred (CtxMapping term ty)
      | term == x = True
      | otherwise = False
    lookupPred _ = False

    errMsg = Text.concat ["Error in tyInfer for Var: variable ", Text.pack $ show x, " not in scope"]
tyInfer ctx UnitTerm = do
  createJudgmentTrace (AlgTypingTrace "1I=>" (ctx, UnitTerm, UnitTy)) []
  pure (UnitTy, ctx)
tyInfer ctx (Ann e ty) = do
  ctx' <- tyCheck ctx e ty
  n <- getNode
  createJudgmentTrace (AlgTypingTrace "Anno" (ctx, Ann e ty, ty)) [(n, TyCheck)]
  return (ty, ctx')
tyInfer ctx (Lam x e) = do
  alphaHat <- getNewVar "alpha"
  betaHat <- getNewVar "beta"
  let
    alphaHatItem = CtxItemHat alphaHat
    betaHatItem = CtxItemHat betaHat
    xTyAlphaHatItem = CtxMapping x (TyVarHat alphaHat)
    ctxExtended = ctx <: alphaHatItem <: betaHatItem <: xTyAlphaHatItem
    alphaHatTyVar = TyVarHat alphaHat
    betaHatTyVar = TyVarHat betaHat
  ctxDeltaXAlphaHatOmega <- tyCheck ctxExtended e betaHatTyVar
  let ctxDelta = takeUntilVar xTyAlphaHatItem ctxDeltaXAlphaHatOmega
  n <- getNode
  createJudgmentTrace (AlgTypingTrace "->I=>" (ctx, Lam x e, betaHatTyVar)) [(n, TyCheck)]
  return (TyArrow alphaHatTyVar betaHatTyVar, ctxDelta)
tyInfer ctx (App e1 e2) = do
  (tyA, ctxOmega) <- tyInfer ctx e1
  n1 <- getNode
  (tyC, ctxDelta) <- tyAppInfer ctxOmega (ctxSubst ctxOmega tyA) e2
  n2 <- getNode
  createJudgmentTrace (AlgTypingTrace "->E" (ctx, App e1 e2, tyC))
    [(n1, TyInfer), (n2, TyAppInfer)]
  pure (tyC, ctxDelta)

tyAppInfer :: Ctx -> Ty -> Expr -> TyStateT (Ty, Ctx)
tyAppInfer ctx (Forall alphaName tyA) e = do
  ret <- tyAppInfer ctxExtended (tySubst alpha alphaHat tyA) e
  n <- getNode
  createJudgmentTrace (AlgTypingTrace "Forall-App" (ctx, e, Forall alphaName tyA))
    [(n, TyAppInfer)]
  pure ret
  where
    alpha = TyVar alphaName
    alphaHat = TyVarHat alphaName
    itemAlphaHat = CtxItemHat alphaName
    ctxExtended = ctx <: itemAlphaHat
tyAppInfer ctx (TyArrow tyA tyC) e = do
  ctxDelta <- tyCheck ctx e tyA
  n <- getNode
  createJudgmentTrace (AlgTypingTrace "->App" (ctx, e, TyArrow tyA tyC)) [(n, TyCheck)]
  return (tyC, ctxDelta)
tyAppInfer ctx (TyVarHat alphaName) e = do
  alphaHat1 <- getNewVar alphaName
  alphaHat2 <- getNewVar alphaName
  let alphaArrow = TyArrow (TyVarHat alphaHat1) (TyVarHat alphaHat2)
      newItems = [CtxItem alphaHat2, CtxItem alphaHat1, CtxEquality alphaName alphaArrow]
      replacedCtx = replaceItem (CtxItemHat alphaName) newItems ctx
  ctxDelta <- tyCheck replacedCtx e (TyVarHat alphaHat1)
  n <- getNode
  createJudgmentTrace (AlgTypingTrace "alphaHatApp" (ctx, e, TyVarHat alphaName))
    [(n, TyCheck)]
  return (TyVarHat alphaHat2, ctxDelta)
-- Gamma[alpha] == CtxLeft, alpha, CtxRight
-- Gamma[alpha] -> Gamma[a2Hat, a1Hat, a = a1Hat -> a2Hat]
--               == CtxLeft, a2Hat, a1Hat, a = a1Hat -> a2Hat, CtxRight
