module Check where

import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class (lift)
import Control.Monad.Error.Class (throwError)
import Control.Monad (unless, when)

import qualified Data.Set as Set
import Data.Set (Set)

import Types
import Utils

freeVars :: Ty -> Set Ty
freeVars UnitTy               = Set.empty
freeVars (TyVar varName)      = Set.singleton (TyVar varName)
freeVars (TyVarHat varName)   = Set.singleton (TyVarHat varName)
freeVars (TyArrow tyA tyB)    = Set.union (freeVars tyA) (freeVars tyB)
freeVars (Forall varName ty)  = Set.delete (TyVar varName) $ freeVars ty



-- NOTE: We follow the first notation
-- 1. [alpha := alphaHat]
-- 2. in the paper, it's [alphaHat / alpha]
tySubst :: Ty -> Ty -> Ty -> Ty
tySubst alpha alphaHat tyA = undefined

ctxSubst :: Ctx -> Ty -> Ty
ctxSubst ctx ty = undefined

subTypeOf :: Ctx -> Ty -> Ty -> TyStateT Ctx
subTypeOf ctx (TyVar alpha0) (TyVar alpha1) = do
  -- throw error if they're not the same
  unless (alpha0 == alpha1) $ 
    throwError $ "Type variable " ++ alpha0 ++ " does not equal " ++ alpha1
  
  pure ctx
subTypeOf ctx UnitTy UnitTy = pure ctx

subTypeOf ctx (TyVarHat alpha0) (TyVarHat alpha1) = do
  -- throw error if they're not the same
  unless (alpha0 == alpha1) $ 
    throwError $ "Type variable " ++ alpha0 ++ "Hat does not equal " ++ alpha1 ++ "Hat"
  
  pure ctx

subTypeOf ctx (TyArrow tyA1 tyA2) (TyArrow tyB1 tyB2) = do
  ctxOmega <- subTypeOf ctx tyB1 tyA1
  subTypeOf ctxOmega (ctxSubst ctxOmega tyA2) (ctxSubst ctxOmega tyB2)

subTypeOf ctx (Forall alphaName tyA) tyB = do
  let ctxExtended = ctx <: CtxMarker alphaName <: CtxItemHat alphaName
  ctxDeltaMarkerOmega <- subTypeOf ctxExtended (tySubst (TyVar alphaName) (TyVarHat alphaName) tyA) tyB
  pure $ takeUntilVar (CtxMarker alphaName) ctxDeltaMarkerOmega

subTypeOf ctx tyA (Forall alphaName tyB) = do
  let ctxExtended = ctx <: CtxItem alphaName
  ctxDeltaAlphaOmega <- subTypeOf ctxExtended tyA tyB
  pure $ takeUntilVar (CtxItem alphaName) ctxDeltaAlphaOmega

subTypeOf ctx (TyVarHat alphaName) tyA = do
  when (Set.member (TyVarHat alphaName) $ freeVars tyA) $
    throwError $ "Type variable " ++ alphaName ++ "Hat exists as a free variable in the given type."
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ "Type variable " ++ alphaName ++ "Hat does not exist in the context."
  instL ctx (TyVarHat alphaName) tyA

subTypeOf ctx tyA (TyVarHat alphaName) = do
  when (Set.member (TyVarHat alphaName) $ freeVars tyA) $
    throwError $ "Type variable " ++ alphaName ++ "Hat exists as a free variable in the given type."
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ "Type variable " ++ alphaName ++ "Hat does not exist in the context."
  instR ctx tyA (TyVarHat alphaName)


instL :: Ctx -> Ty -> Ty -> TyStateT Ctx
instL ctx varHat tyA = undefined

instR :: Ctx -> Ty -> Ty -> TyStateT Ctx
instR ctx tyA varHat = undefined


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
tyInfer ctx (App e1 e2) = do
  (tyA, ctxOmega) <- tyInfer ctx e1
  tyAppInfer ctxOmega (ctxSubst ctxOmega tyA) e2
  


tyAppInfer :: Ctx -> Ty -> Term -> TyStateT (Ty, Ctx)
tyAppInfer ctx (Forall alphaName tyA) e = do
  tyAppInfer ctxExtended (tySubst alpha alphaHat tyA) e
  where
    alpha = TyVar alphaName
    alphaHat = TyVarHat alphaName
    itemAlphaHat = CtxItemHat alphaName
    ctxExtended = ctx <: itemAlphaHat
tyAppInfer ctx (TyArrow tyA tyC) e = do
  ctxDelta <- tyCheck ctx e tyA
  return (tyC, ctxDelta)
tyAppInfer ctx (TyVarHat alphaName) e = do
  alphaHat1 <- getNewVar alphaName
  alphaHat2 <- getNewVar alphaName
  let alphaArrow = TyArrow (TyVarHat alphaHat1) (TyVarHat alphaHat2)
      newItems = [CtxItem alphaHat2, CtxItem alphaHat1, CtxEquality alphaName alphaArrow]
      replacedCtx = replaceItem (CtxItemHat alphaName) newItems ctx
  ctxDelta <- tyCheck replacedCtx e (TyVarHat alphaHat1)
  return (TyVarHat alphaHat2, ctxDelta)
-- Gamma[alpha] == CtxLeft, alpha, CtxRight
-- Gamma[alpha] -> Gamma[a2Hat, a1Hat, a = a1Hat -> a2Hat]
--               == CtxLeft, a2Hat, a1Hat, a = a1Hat -> a2Hat, CtxRight
