{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE InstanceSigs #-}

module Check where

import Prelude hiding (LT, GT)

import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class (lift)
import Control.Monad.Error.Class (throwError)
import Control.Monad (unless, when, zipWithM_)

import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Data.List (find)
import qualified Data.Text as Text

import Types
import Utils

runTyCheck :: Ctx -> Expr -> Ty -> Result Ctx
runTyCheck ctx term ty =
  flip evalStateT initMetaData $ tyCheck ctx term ty

runTyInfer :: Ctx -> Expr -> Result (Ty, Ctx)
runTyInfer ctx =
  flip evalStateT initMetaData . tyInfer ctx

freeVars :: Ty -> Set Ty
freeVars x
  | x `elem` [UnitTy, BooleanTy, IntegerTy] = Set.empty
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
tySubst alpha alphaHat BooleanTy = BooleanTy
tySubst alpha alphaHat IntegerTy = IntegerTy
tySubst alpha alphaHat (TupleTy exprs) = TupleTy $ map (tySubst alpha alphaHat) exprs
tySubst alpha alphaHat (TyVar alphaName) = 
  if TyVar alphaName == alpha then alphaHat else TyVar alphaName
tySubst alpha alphaHat (TyVarHat alphaName) = TyVarHat alphaName
tySubst alpha alphaHat (TyArrow tyA tyB) = TyArrow (tySubst alpha alphaHat tyA) (tySubst alpha alphaHat tyB) 
tySubst alpha alphaHat (Forall alphaName tyA) =
  Forall alphaName (tySubst alpha alphaHat tyA)

ctxSubst :: Ctx -> Ty -> Ty
ctxSubst ctx (TyVar alphaName) = TyVar alphaName
ctxSubst ctx UnitTy = UnitTy
ctxSubst ctx BooleanTy = BooleanTy
ctxSubst ctx IntegerTy = IntegerTy
ctxSubst ctx (TupleTy exprs) = TupleTy $ map (ctxSubst ctx) exprs
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

instance TyJudge MetaData where
  completedRule _ ctx = pure ctx
  completedRuleWithTyRet _ ret = pure ret
  getNewVar varName = do
    v <- gets varCounter
    modify $ \s -> s { varCounter = v + 1 }
    return $ Text.concat [varName, Text.pack $ show v]
  subTypeOf = subTypeOf'
  instL = instL'
  instR = instR'
  tyCheck = tyCheck'
  tyInfer = tyInfer'
  tyAppInfer = tyAppInfer'

subTypeOf' :: TyJudge metadata => Ctx -> Ty -> Ty -> TyStateT metadata Ctx
subTypeOf' ctx tv0@(TyVar alpha0) tv1@(TyVar alpha1) = do
  -- throw error if they're not the same
  unless (alpha0 == alpha1) $ 
    throwError  $ Text.concat ["Type variable ", alpha0, " does not equal ", alpha1]
  completedRule (SubtypeOf "<:Var") ctx

subTypeOf' ctx UnitTy UnitTy = do
  completedRule (SubtypeOf "<:Unit") ctx

subTypeOf' ctx BooleanTy BooleanTy = do
  completedRule (SubtypeOf "<:BooleanTy") ctx

subTypeOf' ctx IntegerTy IntegerTy = do
  completedRule (SubtypeOf "<:IntegerTy") ctx

subTypeOf' ctx (TupleTy exprs1) (TupleTy exprs2) = do
  unless (length exprs1 == length exprs2) $
    throwError $ Text.concat
      [ "Tuple lengths are not the same: "
      , Text.pack $ show (length exprs1), " and "
      , Text.pack $ show (length exprs2)
      ]
  zipWithM_ (subTypeOf ctx) exprs1 exprs2
  completedRule (SubtypeOf $ "<:TupleTy" <> (Text.pack $ show n)) ctx
  where
    n = length exprs1
  
subTypeOf' ctx a1@(TyVarHat alpha0) a2@(TyVarHat alpha1) = do
  -- throw error if they're not the same
  unless (alpha0 == alpha1) $ 
    throwError $ Text.concat ["Type variable ", alpha0, "Hat does not equal ", alpha1, "Hat", " with context: ", Text.pack $ show ctx]
  completedRule (SubtypeOf "<:Exvar") ctx

subTypeOf' ctx a1@(TyArrow tyA1 tyA2) a2@(TyArrow tyB1 tyB2) = do
  ctxOmega <- subTypeOf ctx tyB1 tyA1
  ctxDelta <- subTypeOf ctxOmega (ctxSubst ctxOmega tyA2) (ctxSubst ctxOmega tyB2)
  completedRule (SubtypeOf "<:->") ctxDelta

subTypeOf' ctx forTy@(Forall alphaName tyA) tyB = do
  let ctxExtended = ctx <: CtxMarker alphaName <: CtxItemHat alphaName
  ctxDeltaMarkerOmega <- subTypeOf ctxExtended (tySubst (TyVar alphaName) (TyVarHat alphaName) tyA) tyB
  completedRule (SubtypeOf "<:Forall-L") $
    takeUntilVar (CtxMarker alphaName) ctxDeltaMarkerOmega

subTypeOf' ctx tyA forTy@(Forall alphaName tyB) = do
  let ctxExtended = ctx <: CtxItem alphaName
  ctxDeltaAlphaOmega <- subTypeOf ctxExtended tyA tyB
  completedRule (SubtypeOf "<:Forall-R") $
    takeUntilVar (CtxItem alphaName) ctxDeltaAlphaOmega

subTypeOf' ctx aHat@(TyVarHat alphaName) tyA = do
  when (Set.member (TyVarHat alphaName) $ freeVars tyA) $
    throwError $ Text.concat["Type variable ", alphaName, "Hat exists as a free variable in the given type."]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]
  ctxDelta <- instL ctx (TyVarHat alphaName) tyA
  completedRule (SubtypeOf "<:InstantiateL") ctxDelta

subTypeOf' ctx tyA aHat@(TyVarHat alphaName) = do
  when (Set.member (TyVarHat alphaName) $ freeVars tyA) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat exists as a free variable in the given type."]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]
  ctxDelta <- instR ctx tyA (TyVarHat alphaName)
  completedRule (SubtypeOf "<:InstantiateR") ctxDelta

subTypeOf' _ tyA tyB = error $ "No subtype instance of " ++ show tyA ++ " " ++ show tyB

instL' :: TyJudge metadata => Ctx -> Ty -> Ty -> TyStateT metadata Ctx
instL' ctx tvHat@(TyVarHat alphaName) tau = do
  unless (isMonotype tau) $
    throwError $ Text.concat ["Type ", Text.pack $ show tau, " is not a monotype"]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]
  let newItem = CtxEquality alphaName tau
      gammaAlphaTauGamma' = replaceItem (CtxItemHat alphaName) [newItem] ctx
  completedRule (InstL "InstLSolve") gammaAlphaTauGamma'
instL' ctx tvAlpha@(TyVarHat alphaName) tvBeta@(TyVarHat betaName) = do
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let (ctxL, ctxR) = splitOnItem (CtxItemHat alphaName) ctx
  unless ((CtxItemHat betaName) `elem` ctxR) $
    throwError $ Text.concat ["Type variable ", betaName, "Hat does not exist after ", alphaName, "Hat in the context."]

  completedRule (InstL "InstLReach") $ ctx |> replaceItem (CtxItemHat betaName) [CtxEquality betaName (TyVarHat alphaName)]

instL' ctx tvHat@(TyVarHat alphaName) tArr@(TyArrow tyA1 tyA2) = do
  alphaHat1 <- getNewVar alphaName
  alphaHat2 <- getNewVar alphaName
  let alphaArrow = TyArrow (TyVarHat alphaHat1) (TyVarHat alphaHat2)
      newItems = [CtxItem alphaHat2, CtxItem alphaHat1, CtxEquality alphaName alphaArrow]
      replacedCtx = replaceItem (CtxItemHat alphaName) newItems ctx
  ctxOmega <- instR replacedCtx tyA1 (TyVarHat alphaHat1)
  ctxDelta <- instL ctxOmega (TyVarHat alphaHat2) (ctxSubst ctxOmega tyA2)
  completedRule (InstL "InstLArr") ctxDelta 
instL' ctx tyVarAlphaHat@(TyVarHat alphaName) forTy@(Forall betaName tyB) = do
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let ctxExtended = ctx <: (CtxItem betaName)

  ctxDeltaBetaDelta' <- instL ctxExtended tyVarAlphaHat tyB
  let ctxDelta = takeUntilVar (CtxItem betaName) ctxDeltaBetaDelta'
  completedRule (InstL "InstLAIIR") ctxDelta 

instR' :: TyJudge metadata => Ctx -> Ty -> Ty -> TyStateT metadata Ctx
instR' ctx tau tvHat@(TyVarHat alphaName) = do
  unless (isMonotype tau) $
    throwError $ Text.concat ["Type ", Text.pack $ show tau, " is not a monotype"]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]
  let newItem = CtxEquality alphaName tau
      gammaAlphaTauGamma' = replaceItem (CtxItemHat alphaName) [newItem] ctx
  completedRule (InstR "InstRSolve") gammaAlphaTauGamma'
instR' ctx tvBeta@(TyVarHat betaName) tvAlpha@(TyVarHat alphaName) = do
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let (ctxL, ctxR) = splitOnItem (CtxItemHat alphaName) ctx
  unless ((CtxItemHat betaName) `elem` ctxR) $
    throwError $ Text.concat ["Type variable ", betaName, "Hat does not exist after ", alphaName, "Hat in the context."]

  completedRule (InstR "InstRReach") $ ctx |> replaceItem (CtxItemHat betaName) [CtxEquality betaName (TyVarHat alphaName)]
instR' ctx tArr@(TyArrow tyA1 tyA2) tvHat@(TyVarHat alphaName) = do
  alphaHat1 <- getNewVar alphaName
  alphaHat2 <- getNewVar alphaName
  let alphaArrow = TyArrow (TyVarHat alphaHat1) (TyVarHat alphaHat2)
      newItems = [CtxItem alphaHat2, CtxItem alphaHat1, CtxEquality alphaName alphaArrow]
      replacedCtx = replaceItem (CtxItemHat alphaName) newItems ctx
  ctxOmega <- instL replacedCtx (TyVarHat alphaHat1) tyA1
  ctxDelta <- instR ctxOmega (ctxSubst ctxOmega tyA2) (TyVarHat alphaHat2) 
  completedRule (InstR "InstRArr")ctxDelta 
instR' ctx forTy@(Forall betaName tyB)  tyVarAlphaHat@(TyVarHat alphaName) = do
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwError $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let ctxExtended = ctx <: CtxMarker betaName <: CtxItemHat betaName
      tyBSubst = tySubst (TyVar betaName) (TyVarHat betaName) tyB

  ctxDeltaMarkerDelta' <- instR ctxExtended tyBSubst tyVarAlphaHat

  let ctxDelta = takeUntilVar (CtxMarker betaName) ctxDeltaMarkerDelta'

  completedRule (InstR "InstRAIIL")ctxDelta 


tyCheck' :: TyJudge metadata => Ctx -> Expr -> Ty -> TyStateT metadata Ctx
tyCheck' ctx (LiteralExpr UnitTerm) UnitTy = do
  completedRule (TyCheck "1I") ctx
tyCheck' ctx ifExpr@(If p e1 e2) ty = do
  _ <- tyCheck ctx p BooleanTy
  _ <- tyCheck ctx e1 ty
  _ <- tyCheck ctx e2 ty

  completedRule (TyCheck "If") ctx
tyCheck' ctx (Lam x e) (TyArrow tyA tyB) = do
  ctxDeltaXAlphaOmega <- tyCheck ctxExtended e tyB
  let ctxDelta = takeUntilVar (CtxMapping x tyA) ctxDeltaXAlphaOmega
  completedRule (TyCheck "->I") ctxDelta
  where
    ctxExtended = ctx <: CtxMapping x tyA
tyCheck' ctx e (Forall alpha tyA) = do
  ctxDeltaAlphaOmega <- tyCheck (ctx <: CtxItem alpha) e tyA
  let ctxDelta = takeUntilVar (CtxItem alpha) ctxDeltaAlphaOmega
  completedRule (TyCheck "Forall-I") ctxDelta
  
tyCheck' ctx e tyB = do
  (tyA, ctxTheta) <- tyInfer ctx e

  ctxDelta <- ctxSubst ctxTheta tyA `subTypeOfCtx` ctxSubst ctxTheta tyB

  completedRule (TyCheck "Sub") ctxDelta
  where
    subTypeOfCtx = subTypeOf ctx

tyInfer' :: TyJudge metadata => Ctx -> Expr -> TyStateT metadata (Ty, Ctx)
tyInfer' ctx (Var x) = do
  varFromCtx <- lift $ lookupVar lookupPred ctx errMsg
  completedRuleWithTyRet (TyInfer "Var") (tyItem varFromCtx, ctx)
  where
    lookupPred :: CtxItem -> Bool
    lookupPred (CtxMapping term ty)
      | term == x = True
      | otherwise = False
    lookupPred _ = False

    errMsg = Text.concat ["Error in tyInfer for Var: variable ", Text.pack $ show x, " not in scope"]
tyInfer' ctx (LiteralExpr UnitTerm) = do
  completedRuleWithTyRet (TyInfer "1I=>") (UnitTy, ctx)
tyInfer' ctx (LiteralExpr (BooleanTerm _)) = do
  completedRuleWithTyRet (TyInfer "BoolI=>") (BooleanTy, ctx)
tyInfer' ctx (LiteralExpr (IntegerTerm _)) = do
  completedRuleWithTyRet (TyInfer "IntI=>") (IntegerTy, ctx)
tyInfer' ctx (Tuple exprs) = do
  retTyCtxList <- mapM (tyInfer ctx) exprs -- [TyStateT metadata (Ty, Ctx)] -- TyStateT metadata [(Ty, Ctx)]
  let
    retTyList = map fst retTyCtxList
    n = length exprs
  completedRuleWithTyRet (TyInfer $ "Tuple=>" <> (Text.pack $ show n)) (TupleTy retTyList, ctx)
tyInfer' ctx (BinOpExpr op e1 e2) =
  let
    tyOp =
      if op `elem` [Plus, Minus, Mult, Divide]
      then IntegerTy
      else error "unimplemented ty op in tyInfer"
  in do
    _ <- tyCheck ctx e1 tyOp
    _ <- tyCheck ctx e2 tyOp

    completedRuleWithTyRet (TyInfer "BinOpExpr=>") (tyOp, ctx)
tyInfer' ctx (PredOpExpr op e1 e2) =
  let
    tyOp =
      if op `elem` [LT, GT, LTE, GTE]
      then IntegerTy
      -- TODO: Make Eq polymorphic
      else if op `elem` [And, Or, Eq]
      then BooleanTy
      else error "unimplemented ty op in tyInfer for PredOp"
  in do
    _ <- tyCheck ctx e1 tyOp
    _ <- tyCheck ctx e2 tyOp

    completedRuleWithTyRet (TyInfer "PredOp=>") (BooleanTy, ctx)
tyInfer' ctx (Let (VarPat x) e1 e2) = do
  -- tyCheck ctx (App (Lam x e2) e1) tyC
  -- (tyA, ctxOmega) <- tyInfer ctx (Lam x e2)
  -- (tyC, ctxDelta) <- tyAppInfer' ctxOmega (ctxSubst ctxOmega tyA) e1
  (tyA, ctxOmega) <- tyInfer ctx e1
  let
    e1TyMapping = CtxMapping x tyA
    ctxExtended = ctxOmega <: e1TyMapping
  (tyC, ctxDelta) <- tyInfer ctxExtended e2
  -- We need to substitute over the polymorphic return variable here
  let tyCSpecialize = ctxSubst ctxDelta tyC
  completedRuleWithTyRet (TyInfer "Let=>") (tyCSpecialize, ctxDelta)

tyInfer' ctx (Let (TuplePat pats) e1@(Tuple exprs) e2) = do
  (tye1, ctxOmega) <- tyInfer ctx e1
  case tye1 of
    TupleTy tyExprs -> do
      let
        e1TyMapping = concat $ zipWith assocPat pats tyExprs
        ctxExtended = ctxOmega ++ e1TyMapping
      (tyC, ctxDelta) <- tyInfer ctxExtended e2
      -- We need to substitute over the polymorphic return variable here
      let tyCSpecialize = ctxSubst ctxDelta tyC
      completedRuleWithTyRet (TyInfer "Let=>") (tyCSpecialize, ctxDelta)
    _ -> throwError "let-binding tuple is not a tuple type"
  where
    assocPat :: Pat -> Ty -> [CtxItem]
    assocPat WildCardPat _ = []
    assocPat (VarPat patVar) ty = [CtxMapping patVar ty]
    assocPat (TuplePat patList) (TupleTy tyList) =
      concat $ zipWith assocPat patList tyList -- [Maybe CtxItem]

tyInfer' ctx (Ann e ty) = do
  ctx' <- tyCheck ctx e ty
  completedRuleWithTyRet (TyInfer "Anno") (ty, ctx')
tyInfer' ctx (Lam x e) = do
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
  completedRuleWithTyRet (TyInfer "->I=>") (TyArrow alphaHatTyVar betaHatTyVar, ctxDelta)
tyInfer' ctx (App e1 e2) = do
  (tyA, ctxOmega) <- tyInfer ctx e1
  (tyC, ctxDelta) <- tyAppInfer ctxOmega (ctxSubst ctxOmega tyA) e2
  completedRuleWithTyRet (TyInfer "->E") (tyC, ctxDelta)

tyAppInfer' :: TyJudge metadata => Ctx -> Ty -> Expr -> TyStateT metadata (Ty, Ctx)
tyAppInfer' ctx (Forall alphaName tyA) e = do
  ret <- tyAppInfer ctxExtended (tySubst alpha alphaHat tyA) e
  completedRuleWithTyRet (TyAppInfer "Forall-App") ret
  where
    alpha = TyVar alphaName
    alphaHat = TyVarHat alphaName
    itemAlphaHat = CtxItemHat alphaName
    ctxExtended = ctx <: itemAlphaHat
tyAppInfer' ctx (TyArrow tyA tyC) e = do
  ctxDelta <- tyCheck ctx e tyA
  completedRuleWithTyRet (TyAppInfer "->App") (tyC, ctxDelta)
tyAppInfer' ctx (TyVarHat alphaName) e = do
  alphaHat1 <- getNewVar alphaName
  alphaHat2 <- getNewVar alphaName
  let alphaArrow = TyArrow (TyVarHat alphaHat1) (TyVarHat alphaHat2)
      newItems = [CtxItem alphaHat2, CtxItem alphaHat1, CtxEquality alphaName alphaArrow]
      replacedCtx = replaceItem (CtxItemHat alphaName) newItems ctx
  ctxDelta <- tyCheck replacedCtx e (TyVarHat alphaHat1)
  completedRuleWithTyRet (TyAppInfer "alphaHatApp") (TyVarHat alphaHat2, ctxDelta)
-- Gamma[alpha] == CtxLeft, alpha, CtxRight
-- Gamma[alpha] -> Gamma[a2Hat, a1Hat, a = a1Hat -> a2Hat]
--               == CtxLeft, a2Hat, a1Hat, a = a1Hat -> a2Hat, CtxRight
