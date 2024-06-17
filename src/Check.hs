module Check where

import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class (lift)

import Types
import Utils

-- NOTE: We follow the first notation
-- 1. [alpha := alphaHat]
-- 2. in the paper, it's [alphaHat / alpha]
tySubst :: Ty -> Ty -> Ty -> Ty
tySubst alpha alphaHat tyA = undefined

ctxSubst :: Ctx -> Ty -> Ty
ctxSubst ctx ty = undefined

subTypeOf :: Ctx -> Ty -> Ty -> TyStateT Ctx
subTypeOf ctx tyA tyB = undefined

tyCheck :: Ctx -> Term -> Ty -> TyStateT Ctx
tyCheck ctx UnitTerm UnitTy = return ctx
tyCheck ctx (Lam x e) (TyArrow tyA tyB) = do
  ctxDeltaXAlphaOmega <- tyCheck ctxExtended e tyB
  let ctxDelta = takeUntilVar (CtxMapping x tyA) ctxDeltaXAlphaOmega
  return ctxDelta
  where
    ctxExtended = ctx <: CtxMapping x tyA
tyCheck ctx e (Forall alpha tyA) = do
  ctxDeltaAlphaOmega <- tyCheck (ctx <: CtxItem alpha) e tyA
  let ctxDelta = takeUntilVar (CtxItem alpha) ctxDeltaAlphaOmega
  return ctxDelta
tyCheck ctx e tyB = do
  (tyA, ctxTheta) <- tyInfer ctx e
  ctxSubst ctxTheta tyA `subTypeOfCtx` ctxSubst ctxTheta tyB
  where
    subTypeOfCtx = subTypeOf ctx

tyInfer :: Ctx -> Term -> TyStateT (Ty, Ctx)
tyInfer ctx (Var x) = do
  varFromCtx <- lift $ lookupVar lookupPred ctx errMsg
  return (tyItem varFromCtx, ctx)
  where
    lookupPred :: CtxItem -> Bool
    lookupPred (CtxItem _) = False
    lookupPred (CtxMapping term ty)
      | term == x = True
      | otherwise = False

    errMsg = "Error in tyInfer for Var: variable " ++ show x ++ " not in scope"
tyInfer ctx UnitTerm = return (UnitTy, ctx)
tyInfer ctx (Ann e ty) = do
  ctx' <- tyCheck ctx e ty
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
  return (TyArrow alphaHatTyVar betaHatTyVar, ctxDelta)

tyAppInfer :: Ctx -> Ty -> Term -> TyStateT (Ty, Ctx)
tyAppInfer ctx (Forall alphaName tyA) e = do
  tyAppInfer ctxExtended (tySubst alpha alphaHat tyA) e
  where
    alpha = TyVar alphaName
    alphaHat = TyVarHat alphaName
    itemAlphaHat = CtxItemHat alphaName
    ctxExtended = ctx <: itemAlphaHat
-- Gamma[alpha] == CtxLeft, alpha, CtxRight
-- Gamma[alpha] -> Gamma[a2Hat, a1Hat, a = a1Hat -> a2Hat]
--               == CtxLeft, a2Hat, a1Hat, a = a1Hat -> a2Hat, CtxRight
