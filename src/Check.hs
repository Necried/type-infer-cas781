{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE InstanceSigs #-}

module Check where

import Prelude hiding (LT, GT)

import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class (lift)
import Control.Monad (unless, when, zipWithM_, replicateM)

import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Data.List (find)
import qualified Data.Text as Text
import Debug.Pretty.Simple (pTraceShowM)

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
freeVars (TupleTy tys)        = foldr Set.union Set.empty $ map freeVars tys

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
  completedRule r ctx = pure ctx
  completedRuleWithTyRet r ret = pure ret
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
    throwErrorWithContext ctx  $ Text.concat ["Type variable ", alpha0, " does not equal ", alpha1]
  completedRule (SubtypeOf "<:Var") ctx

subTypeOf' ctx UnitTy UnitTy = do
  completedRule (SubtypeOf "<:Unit") ctx

subTypeOf' ctx BooleanTy BooleanTy = do
  completedRule (SubtypeOf "<:BooleanTy") ctx

subTypeOf' ctx IntegerTy IntegerTy = do
  completedRule (SubtypeOf "<:IntegerTy") ctx

subTypeOf' ctx (TupleTy exprs1) (TupleTy exprs2) = do
  unless (length exprs1 == length exprs2) $
    throwErrorWithContext ctx $ Text.concat
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
    throwErrorWithContext ctx $ Text.concat ["Type variable ", alpha0, "Hat does not equal ", alpha1, "Hat"]
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
    throwErrorWithContext ctx $ Text.concat["<:InstantiateL: Type variable ", alphaName, "Hat exists as a free variable in the given type."]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwErrorWithContext ctx $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context: ", Text.pack $ show $ filter filterItemHats ctx]
  ctxDelta <- instL ctx (TyVarHat alphaName) tyA
  completedRule (SubtypeOf "<:InstantiateL") ctxDelta
  where
    filterItemHats (CtxItemHat _) = True
    filterItemHats _ = False
subTypeOf' ctx tyA aHat@(TyVarHat alphaName) = do
  when (Set.member (TyVarHat alphaName) $ freeVars tyA) $
    throwErrorWithContext ctx $ Text.concat ["Type variable ", alphaName, "Hat exists as a free variable in the given type."]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwErrorWithContext ctx $ Text.concat ["<:InstantiateR: Type variable ", alphaName, "Hat does not exist in the context when deducing LHS tyA: ", Text.pack $ show tyA, ": ", Text.pack $ show ctx]
  ctxDelta <- instR ctx tyA (TyVarHat alphaName)
  completedRule (SubtypeOf "<:InstantiateR") ctxDelta

subTypeOf' ctx tyA tyB = -- error $ "No subtype instance of " ++ show tyA ++ " " ++ show tyB ++ " with context " ++ show ctx
  throwErrorWithContext ctx $
    Text.concat [ "No subtype instance of "
                , Text.pack $ show tyA
                , " <: "
                , Text.pack $ show tyB]

instL' :: TyJudge metadata => Ctx -> Ty -> Ty -> TyStateT metadata Ctx
instL' ctx tvHat@(TyVarHat alphaName) tau = do
  unless (isMonotype tau) $
    throwErrorWithContext ctx $ Text.concat ["Type ", Text.pack $ show tau, " is not a monotype"]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwErrorWithContext ctx $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]
  let newItem = CtxEquality alphaName tau
      gammaAlphaTauGamma' = replaceItem (CtxItemHat alphaName) [newItem] ctx
  completedRule (InstL "InstLSolve") gammaAlphaTauGamma'
instL' ctx tvAlpha@(TyVarHat alphaName) tvBeta@(TyVarHat betaName) = do
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwErrorWithContext ctx $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let (ctxL, ctxR) = splitOnItem (CtxItemHat alphaName) ctx
  unless ((CtxItemHat betaName) `elem` ctxR) $
    throwErrorWithContext ctx $ Text.concat ["Type variable ", betaName, "Hat does not exist after ", alphaName, "Hat in the context."]

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
    throwErrorWithContext ctx $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let ctxExtended = ctx <: (CtxItem betaName)

  ctxDeltaBetaDelta' <- instL ctxExtended tyVarAlphaHat tyB
  let ctxDelta = takeUntilVar (CtxItem betaName) ctxDeltaBetaDelta'
  completedRule (InstL "InstLAIIR") ctxDelta 

instR' :: TyJudge metadata => Ctx -> Ty -> Ty -> TyStateT metadata Ctx
instR' ctx tau tvHat@(TyVarHat alphaName) = do
  unless (isMonotype tau) $
    throwErrorWithContext ctx $ Text.concat ["Type ", Text.pack $ show tau, " is not a monotype"]
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwErrorWithContext ctx $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]
  let newItem = CtxEquality alphaName tau
      gammaAlphaTauGamma' = replaceItem (CtxItemHat alphaName) [newItem] ctx
  completedRule (InstR "InstRSolve") gammaAlphaTauGamma'
instR' ctx tvBeta@(TyVarHat betaName) tvAlpha@(TyVarHat alphaName) = do
  unless ((CtxItemHat alphaName) `elem` ctx) $
    throwErrorWithContext ctx $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let (ctxL, ctxR) = splitOnItem (CtxItemHat alphaName) ctx
  unless ((CtxItemHat betaName) `elem` ctxR) $
    throwErrorWithContext ctx $ Text.concat ["Type variable ", betaName, "Hat does not exist after ", alphaName, "Hat in the context."]

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
    throwErrorWithContext ctx $ Text.concat ["Type variable ", alphaName, "Hat does not exist in the context."]

  let ctxExtended = ctx <: CtxMarker betaName <: CtxItemHat betaName
      tyBSubst = tySubst (TyVar betaName) (TyVarHat betaName) tyB

  ctxDeltaMarkerDelta' <- instR ctxExtended tyBSubst tyVarAlphaHat

  let ctxDelta = takeUntilVar (CtxMarker betaName) ctxDeltaMarkerDelta'

  completedRule (InstR "InstRAIIL")ctxDelta 


tyCheck' :: TyJudge metadata => Ctx -> Expr -> Ty -> TyStateT metadata Ctx
tyCheck' ctx (LiteralExpr UnitTerm) UnitTy = do
  completedRule (TyCheck "1I") ctx
tyCheck' ctx ifExpr@(If p e1 e2) ty = do
  
  ctxAfterIf <- tyCheck ctx p BooleanTy

  ctxAfterThen <- tyCheck ctxAfterIf e1 ty

  ctxAfterElse <- tyCheck ctxAfterThen e2 ty

  completedRule (TyCheck "If") ctxAfterElse
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

    -- NOTE: We have to use ctxTheta here!!
  let subTypeOfCtx = subTypeOf ctxTheta
  ctxDelta <- ctxSubst ctxTheta tyA `subTypeOfCtx` ctxSubst ctxTheta tyB

  completedRule (TyCheck "Sub") ctxDelta

tyInfer' :: TyJudge metadata => Ctx -> Expr -> TyStateT metadata (Ty, Ctx)
tyInfer' ctx (Var x) = do
  varFromCtx <- lift $ lookupVar lookupPred ctx (ctx, errMsg)
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
    ctxLHS <- tyCheck ctx e1 tyOp
    ctxRHS <- tyCheck ctxLHS e2 tyOp

    completedRuleWithTyRet (TyInfer "BinOpExpr=>") (tyOp, ctxRHS)
tyInfer' ctx (PredOpExpr op e1 e2) =
  let
    tyOp =
      if op `elem` [LT, GT, LTE, GTE, Eq]
      then IntegerTy
      -- TODO: Make Eq polymorphic
      else if op `elem` [And, Or]
      then BooleanTy
      else error "unimplemented ty op in tyInfer for PredOp"
  in do
    ctxAfterLHS <- tyCheck ctx e1 tyOp
    ctxAfterRHS <- tyCheck ctxAfterLHS e2 tyOp

    completedRuleWithTyRet (TyInfer "PredOp=>") (BooleanTy, ctxAfterRHS)

{-
tyInfer' ctx (Let (VarPat x) e1@(Lam arg body) e2) = do
  -- tyCheck ctx (App (Lam x e2) e1) tyC
  -- (tyA, ctxOmega) <- tyInfer ctx (Lam x e2)
  -- (tyC, ctxDelta) <- tyAppInfer' ctxOmega (ctxSubst ctxOmega tyA) e1
  alphaHat <- getNewVar "alpha"
  betaHat <- getNewVar "beta"
  let
    alphaHatItem = CtxItemHat alphaHat
    alphaHatTyVar = TyVarHat alphaHat
    betaHatItem = CtxItemHat betaHat
    betaHatTyVar = TyVarHat betaHat
    xTyMapping = CtxMapping x (TyArrow alphaHatTyVar betaHatTyVar)
    ctxExtended = ctx <: alphaHatItem <:betaHatItem <: xTyMapping
  (tyA, ctxOmega) <- tyInfer ctxExtended e1
  let
    e1TyMapping = CtxMapping x $ ctxSubst ctxOmega tyA
    ctxExtended = ctxOmega <: e1TyMapping
  (tyC, ctxDelta) <- tyInfer ctxExtended e2
  -- We need to substitute over the polymorphic return variable here
  -- let tyCSpecialize = ctxSubst ctxDelta tyC
  completedRuleWithTyRet (TyInfer "Let=>") (tyC, ctxDelta)
-}
tyInfer' ctx (Let (VarPat x) e1 e2) = do
  alphaHat <- getNewVar "alpha"
  let
    alphaHatItem = CtxItemHat alphaHat
    alphaHatTyVar = TyVarHat alphaHat
    xTyMapping = CtxMapping x alphaHatTyVar
    ctxWithXMapping = ctx <: CtxMarker alphaHat <: alphaHatItem <: xTyMapping
  (tyA, ctxOmega) <- tyInfer ctxWithXMapping e1
  -- pTraceShowM (tyA, ctxOmega)
  let
    ctxAfterMarker = takeAfterVar (CtxMarker alphaHat) ctxOmega
    tyASpecialize = ctxSubst ctxAfterMarker tyA
    e1TyMapping = CtxMapping x tyASpecialize
    ctxExtended = ctx <: e1TyMapping
  -- pTraceShowM tyASpecialize
  when (notSpecialized tyASpecialize) $ throwErrorWithContext ctxExtended $ Text.concat
    [ "let-binding for expression "
    , Text.pack $ show e1
    , " did not specialize, and has type "
    , Text.pack $ show tyA
    ]
  -- let ctxOmega' = removeOldOccurence xTyMapping ctxExtended
  -- pTraceShowM (tyA, tyASpecialize, ctxOmega', ctxExtended)
  (tyC, ctxDelta) <- tyInfer ctxExtended e2
  -- We need to substitute over the polymorphic return variable here
  completedRuleWithTyRet (TyInfer "Let=>") (tyC, ctxDelta)
  where
    notSpecialized (TyVarHat _) = True
    notSpecialized _ = False
{-
tyInfer' ctx (Let (VarPat x) e1 e2) = do
  -- tyCheck ctx (App (Lam x e2) e1) tyC
  -- (tyA, ctxOmega) <- tyInfer ctx (Lam x e2)
  -- (tyC, ctxDelta) <- tyAppInfer' ctxOmega (ctxSubst ctxOmega tyA) e1
  (tyA, ctxOmega) <- tyInfer ctx e1
  let
    tyASpecialize = ctxSubst ctxOmega tyA
    e1TyMapping = CtxMapping x tyASpecialize
    ctxExtended = ctxOmega <: e1TyMapping
  (tyC, ctxDelta) <- tyInfer ctxExtended e2
  -- We need to substitute over the polymorphic return variable here
  let tyCSpecialize = ctxSubst ctxDelta tyC
  completedRuleWithTyRet (TyInfer "Let=>") (tyC, ctxDelta)
-}
tyInfer' ctx (Let (TuplePat pats) e1 e2) = do
  (tye1, ctxOmega) <- tyInfer ctx e1
  case tye1 of
    TupleTy tyExprs -> do
      let
        e1TyMapping = concat $ zipWith assocPat pats tyExprs
        ctxExtended = ctxOmega ++ e1TyMapping
      (tyC, ctxDelta) <- tyInfer ctxExtended e2
      -- We need to substitute over the polymorphic return variable here
      let tyCSpecialize = ctxSubst ctxDelta tyC
      completedRuleWithTyRet (TyInfer "Let=>TupleTy") (tyCSpecialize, ctxDelta)
  {-
    ty@(Forall _ _) -> do
      let
        tyExprs = unwrapForalls ty Set.empty
        e1TyMapping = concat $ zipWith assocPat pats tyExprs
        ctxExtended = ctxOmega ++ e1TyMapping
      (tyC, ctxDelta) <- tyInfer ctxExtended e2
      -- We need to substitute over the polymorphic return variable here
      let tyCSpecialize = ctxSubst ctxDelta tyC
      completedRuleWithTyRet (TyInfer "Let=>ForallTupleTy") (tyCSpecialize, ctxDelta)
    TyVarHat alphaHat -> do
      varHats <- replicateM (length pats) (getNewVar "alphaTuple") 
      let
        e1TyMapping = concat $ zipWith assocPat pats (map TyVarHat varHats)
        ctxExtended = ctxOmega ++ e1TyMapping
      (tyC, ctxDelta) <- tyInfer ctxExtended e2
      -- We need to substitute over the polymorphic return variable here
      let tyCSpecialize = ctxSubst ctxDelta tyC
      completedRuleWithTyRet (TyInfer "Let=>TyVarHatTupleTy") (tyCSpecialize, ctxDelta)
  -}
    _ -> throwErrorWithContext ctx "let-binding tuple is not a tuple type"
  where
    assocPat :: Pat -> Ty -> [CtxItem]
    assocPat WildCardPat _ = []
    assocPat (VarPat patVar) ty = [CtxMapping patVar ty]
    assocPat (TuplePat patList) (TupleTy tyList) =
      concat $ zipWith assocPat patList tyList -- [Maybe CtxItem]

    unwrapForalls :: Ty -> Set Ty -> [Ty]
    unwrapForalls ty@(Forall varName tyBody) seenVars
      | not $ (TyVar varName) `Set.member` seenVars = unwrapForalls tyBody (Set.insert (TyVar varName) seenVars)
      | otherwise = error $ "Malformed forall when checking for tuple type: " ++ show ty
    unwrapForalls ty@(TupleTy tyExprs) seenVars
      | freeVars ty == seenVars = tyExprs
      | otherwise = error $ "Free variables in tuple expression: " ++ show ty

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
  alphaHat1 <- getNewVar "alpha"
  alphaHat2 <- getNewVar "alpha"
  let alphaArrow = TyArrow (TyVarHat alphaHat1) (TyVarHat alphaHat2)
      newItems = [CtxItemHat alphaHat2, CtxItemHat alphaHat1, CtxEquality alphaName alphaArrow]
      replacedCtx = replaceItem (CtxItemHat alphaName) newItems ctx
  ctxDelta <- tyCheck replacedCtx e (TyVarHat alphaHat1)
  completedRuleWithTyRet (TyAppInfer "alphaHatApp") (TyVarHat alphaHat2, ctxDelta)
-- Gamma[alpha] == CtxLeft, alpha, CtxRight
-- Gamma[alpha] -> Gamma[a2Hat, a1Hat, a = a1Hat -> a2Hat]
--               == CtxLeft, a2Hat, a1Hat, a = a1Hat -> a2Hat, CtxRight
