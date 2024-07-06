{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}

module BuildGraph where

import Types
import Dot
import Check

import qualified Data.Graph.Inductive.Graph as G
import Control.Monad.Trans.State.Strict

instance TyJudge MetaDataGBuilder where

  completedRule (SubtypeOf "<:->") retCtx = do
    n1 <- popNode
    n2 <- popNode
    n' <- createJudgmentTrace
      [(n1, SubtypeOf "<:->"), (n2, SubtypeOf "<:->")]
    pure retCtx

  completedRuleWithTyRet _ retTy = do
    pure retTy

  subTypeOfJudge ctx t1 t2 = do
    pushTraceFrame (SubtypeTrace (ctx, t1, t2))
    subTypeOf ctx t1 t2
    -- add current context to a stack
    -- call subTypeOf on normal args


{-
  subTypeOf ctx tv0@(TyVar alpha0) tv1@(TyVar alpha1) = do
    n <- createEmptyTrace
    n' <- createJudgmentTrace (SubtypeTrace (ctx, tv0, tv1)) [(n, SubtypeOf "<:Var")]
    pure (ctx, n')

  subTypeOf ctx UnitTy UnitTy = do
    n <- createEmptyTrace
    n' <- createJudgmentTrace (SubtypeTrace (ctx, UnitTy, UnitTy)) [(n, SubtypeOf "<:Unit")]
    pure (ctx, n')

  subTypeOf ctx BooleanTy BooleanTy = do
    n <- createEmptyTrace
    n' <- createJudgmentTrace (SubtypeTrace (ctx, BooleanTy, BooleanTy))
      [(n, SubtypeOf "<:BooleanTy")]
    pure (ctx, n')

  subTypeOf ctx IntegerTy IntegerTy = do
    n <- createEmptyTrace
    n' <- createJudgmentTrace (SubtypeTrace (ctx, IntegerTy, IntegerTy)) []
      [(n, SubtypeOf "<:IntegerTy")]
    pure (ctx, n')

  subTypeOf ctx a1@(TyVarHat alpha0) a2@(TyVarHat alpha1) = do
    n <- createEmptyTrace
    n' <- createJudgmentTrace (SubtypeTrace (ctx, a1, a2)) []
      [(n, SubtypeOf "<:Exvar")]
    pure (ctx, n')

  subTypeOf ctx a1@(TyArrow tyA1 tyA2) a2@(TyArrow tyB1 tyB2) = do
    (ctxOmega, n1) <- subTypeOf ctx tyB1 tyA1
    (ctxDelta, n2) <- subTypeOf ctxOmega (ctxSubst ctxOmega tyA2) (ctxSubst ctxOmega tyB2)
    n' <- createJudgmentTrace (SubtypeTrace (ctx, a1, a2))
      [(n1, SubtypeOf "<:->"), (n2, SubtypeOf "<:->")]
    pure ctxDelta

  subTypeOf ctx forTy@(Forall alphaName tyA) tyB = do
    let ctxExtended = ctx <: CtxMarker alphaName <: CtxItemHat alphaName
    ctxDeltaMarkerOmega <- subTypeOf ctxExtended (tySubst (TyVar alphaName) (TyVarHat alphaName) tyA) tyB
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

  subTypeOf _ tyA tyB = error $ "No subtype instance of " ++ show tyA ++ " " ++ show tyB

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
  tyCheck ctx ifExpr@(If p e1 e2) ty = do
    _ <- tyCheck ctx p BooleanTy
    n1 <- getNode
    _ <- tyCheck ctx e1 ty
    n2 <- getNode
    _ <- tyCheck ctx e2 ty
    n3 <- getNode

    createJudgmentTrace (AlgTypingTrace "If" (ctx, ifExpr, ty))
      [(n1, TyCheck), (n2, TyCheck), (n3, TyCheck)]

    pure ctx
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
  tyInfer ctx b@(BooleanTerm _) = do
    createJudgmentTrace (AlgTypingTrace "BoolI=>" (ctx, b, BooleanTy)) []
    pure (BooleanTy, ctx)
  tyInfer ctx i@(IntegerTerm _) = do
    createJudgmentTrace (AlgTypingTrace "IntI=>" (ctx, i, IntegerTy)) []
    pure (IntegerTy, ctx)
  tyInfer ctx bop@(BinOpExpr op e1 e2) =
    let
      tyOp =
        if op `elem` [Plus, Minus, Mult, Divide]
        then IntegerTy
        else error "unimplemented ty op in tyInfer"
    in do
      _ <- tyCheck ctx e1 tyOp
      n1 <- getNode
      _ <- tyCheck ctx e2 tyOp
      n2 <- getNode

      createJudgmentTrace
        (AlgTypingTrace "BinOpExpr" (ctx, bop, tyOp)) [(n1, TyCheck), (n2, TyCheck)]
      pure (tyOp, ctx)
  tyInfer ctx predOp@(PredOpExpr op e1 e2) =
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
      n1 <- getNode
      _ <- tyCheck ctx e2 tyOp
      n2 <- getNode

      createJudgmentTrace
        (AlgTypingTrace "PredOp" (ctx, predOp, BooleanTy)) []
      pure (BooleanTy, ctx)

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
  tyInfer ctx letExpr@(Let x e1 e2) = do
    -- tyCheck ctx (App (Lam x e2) e1) tyC
    (tyA, ctxOmega) <- tyInfer ctx (Lam x e2)
    n1 <- getNode
    (tyC, ctxDelta) <- tyAppInfer ctxOmega (ctxSubst ctxOmega tyA) e1
    n2 <- getNode

    createJudgmentTrace (AlgTypingTrace "Let" (ctx, letExpr, tyC))
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
  -}

{-
-- NOTE: This assumes a call to `createJudgmentTrace` after the
-- child node is fully constructed!
getNode :: TyStateT MetaDataGBuilder Int
getNode = pred <$> gets (nodeCounter . judgmentBuilder)
-}

-- `createJudgmentTrace src tgts` takes a src node,
-- and a list of (tgtNode, edge) pair, and connects
-- src --edge--> tgtNode
createJudgmentTrace ::
  [(Int, JudgmentRule)]->
  TyStateT MetaDataGBuilder ()
createJudgmentTrace [] = do
  srcLNode <- popTraceFrame
  builder <- gets judgmentBuilder
  let curNodes = nodes builder
      srcNode = nodeCounter builder
  modify $ \s -> s
    { judgmentBuilder = builder
      { nodes = srcLNode : curNodes
      , nodeCounter = srcNode + 1
      }
    }
createJudgmentTrace ((tgtNode, edgeLabel):rest) = do
  builder <- gets judgmentBuilder
  let curEdges = edges builder
      srcNode = nodeCounter builder
  modify $ \s -> s
    { judgmentBuilder = builder
      { edges = (srcNode, tgtNode, edgeLabel):curEdges }
    }
  createJudgmentTrace rest

createEmptyTrace :: TyStateT MetaDataGBuilder Int
createEmptyTrace = do
  builder <- gets judgmentBuilder
  let curNodes = nodes builder
      srcNode = nodeCounter builder
  modify $ \s -> s
    {
      judgmentBuilder = builder
        { nodes = (srcNode, EmptyTrace) : curNodes
        , nodeCounter = srcNode + 1
        }
    }
  pure srcNode

popTraceFrame :: TyStateT MetaDataGBuilder (G.LNode JudgmentTrace)
popTraceFrame = do
  builder <- gets judgmentBuilder
  let curTraceStack = traceStack builder
  modify $ \s -> s
    {
      judgmentBuilder = builder
        { traceStack = tail curTraceStack }
    }
  pure $ head curTraceStack

popNode :: TyStateT MetaDataGBuilder Int
popNode = do
  builder <- gets judgmentBuilder
  let curNodeStack = nodeStack builder
  modify $ \s -> s
    {
      judgmentBuilder = builder
        { nodeStack = tail curNodeStack }
    }
  pure $ head curNodeStack

pushTraceFrame :: JudgmentTrace -> TyStateT MetaDataGBuilder ()
pushTraceFrame tr = do
  builder <- gets judgmentBuilder
  let curTraceStack = traceStack builder
      curNodeStack = nodeStack builder
      srcNode = nodeCounter builder
  modify $ \s -> s
    {
      judgmentBuilder = builder
        { nodeCounter = srcNode + 1
        , traceStack = (srcNode, tr) : curTraceStack
        , nodeStack = srcNode : curNodeStack
        }
    }
  pure ()


constructJudgmentGraph :: Ctx -> Expr -> Maybe Ty -> Result JudgmentGraph
constructJudgmentGraph ctx e mTy = case mTy of
  Nothing -> fmap (constructGraph . judgmentBuilder) $
    flip execStateT initMetaDataGBuilder $ tyInfer ctx e
  Just checkTy -> fmap (constructGraph . judgmentBuilder) $
    flip execStateT initMetaDataGBuilder $ tyCheck ctx e checkTy
  where
    constructGraph gBuilder = G.mkGraph (nodes gBuilder) (edges gBuilder)

dotJudgmentGraph :: Ctx -> Expr -> Maybe Ty -> String -> IO ()
dotJudgmentGraph ctx e mTy s =
  let graphRes = constructJudgmentGraph ctx e mTy
  in case graphRes of
    Left err -> print err
    Right g -> dotToFile s g

