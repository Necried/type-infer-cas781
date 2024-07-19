{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}

module BuildGraph where

import Types
import Dot
import Check

import qualified Data.Graph.Inductive.Graph as G
import Control.Monad
import Control.Monad.Trans.State.Strict
import qualified Data.Text as Text
import Data.Text.Read (decimal)

instance TyJudge MetaDataGBuilder where

  completedRule stRule@(SubtypeOf r) retCtx
    | r `elem` ["<:Var", "<:Unit", "<:BooleanTy", "<:IntegerTy", "<:Exvar"] =
      mkGraphNode stRule 0 retCtx
    | r `elem` ["<:Forall-L", "<:Forall-R", "<:InstantiateL", "<:InstantiateR"] =
      mkGraphNode stRule 1 retCtx
    | r `elem` ["<:->"] =
      mkGraphNode stRule 2 retCtx
    | "<:TupleTy" `Text.isPrefixOf` r =
        case decimal (Text.drop (Text.length "<:TupleTy") $ r) of
          Left err -> error err
          Right (n, _) -> mkGraphNode stRule n retCtx

  completedRule iLRule@(InstL r) retCtx
    | r `elem` ["InstLSolve", "InstLReach"] = mkGraphNode iLRule 0 retCtx
    | r `elem` ["InstLAIIR"] = mkGraphNode iLRule 1 retCtx
    | r `elem` ["InstLArr"] = mkGraphNode iLRule 2 retCtx
  completedRule iRRule@(InstR r) retCtx
    | r `elem` ["InstRSolve", "InstRReach"] = mkGraphNode iRRule 0 retCtx
    | r `elem` ["InstRAIIL"] = mkGraphNode iRRule 1 retCtx
    | r `elem` ["InstRArr"] = mkGraphNode iRRule 2 retCtx
  completedRule tcRule@(TyCheck r) retCtx
    | r `elem` ["1I"] = mkGraphNode tcRule 0 retCtx
    | r `elem` ["->I", "Forall-I"] = mkGraphNode tcRule 1 retCtx
    | r `elem` ["Sub"] = mkGraphNode tcRule 2 retCtx
    | r `elem` ["If"] = mkGraphNode tcRule 3 retCtx
  completedRule r retCtx =
    error $ "Unhandled case: " ++ show r

  completedRuleWithTyRet r retCtx
    | getRule r `elem` ["Var", "1I=>", "BoolI=>", "IntI=>"] = mkGraphNode r 0 retCtx
    | getRule r `elem` ["Anno", "->I=>", "Forall-App", "->App", "alphaHatApp"] =
        mkGraphNode r 1 retCtx
    | getRule r `elem` ["BinOpExpr=>",
                        "Let=>", "Let=>TupleTy", "Let=>ForallTupleTy", "Let=>TyVarHatTupleTy",
                        "PredOp=>", "->E"]
        = mkGraphNode r 2 retCtx
    | "Tuple=>" `Text.isPrefixOf` getRule r =
        case decimal (Text.drop (Text.length "Tuple=>") $ getRule r) of
          Left err -> error err
          Right (n, _) -> mkGraphNode r n retCtx
    | otherwise = error $ "Case unhandled: " ++ show (getRule r)

  getNewVar varName = do
    v <- gets (varCounter . metaData)
    m <- gets metaData
    modify $ \s -> s { metaData = m { varCounter = v + 1 } }
    return $ Text.concat [varName, Text.pack $ show v]

  subTypeOf ctx t1 t2 = do
    pushTraceFrame (SubtypeTrace (ctx, t1, t2))
    subTypeOf' ctx t1 t2

  instL ctx t1 t2 = do
    pushTraceFrame (InstLTrace (ctx, t1, t2))
    instL' ctx t1 t2

  instR ctx t1 t2 = do
    pushTraceFrame (InstRTrace (ctx, t1, t2))
    instR' ctx t1 t2

  tyCheck ctx e ty = do
    pushTraceFrame (TyCheckTrace (ctx, e, ty))
    tyCheck' ctx e ty

  tyInfer ctx e = do
    pushTraceFrame (TyInferTrace (ctx, e))
    tyInfer' ctx e

  tyAppInfer ctx ty e = do
    pushTraceFrame (TyAppInferTrace (ctx, ty, e))
    tyAppInfer' ctx ty e

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
  modify $ \s -> s
    { judgmentBuilder = builder
      { nodes = srcLNode : curNodes
      }
    }
createJudgmentTrace ((tgtNode, edgeLabel):rest) = do
  builder <- gets judgmentBuilder
  let curEdges = edges builder
      (srcNode, _) = head $ traceStack builder
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

fetchNodes :: JudgmentRule -> Int -> TyStateT MetaDataGBuilder [(Int, JudgmentRule)]
fetchNodes r i = do
  ns <- replicateM i popNode
  pure $ (, r) <$> ns

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

mkGraphNode :: JudgmentRule -> Int -> a -> TyStateT MetaDataGBuilder a
mkGraphNode r 0 ret = do
  n <- createEmptyTrace
  createJudgmentTrace [(n, r)]
  pure ret
mkGraphNode r n ret = do
  ns <- fetchNodes r n
  createJudgmentTrace ns
  pure ret

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

getRule :: JudgmentRule -> RuleName
getRule (TyCheck r) = r
getRule (TyInfer r) = r
getRule (TyAppInfer r) = r
getRule (InstL r) = r
getRule (InstR r) = r
getRule (SubtypeOf r) = r
