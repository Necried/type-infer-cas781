module Types where

import Utils

import Control.Monad.Trans.State.Strict

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.PatriciaTree as PT

type Result a = Either Text a

type TyStateT a = StateT MetaData (Either Text) a

data JudgmentTrace =
    AlgTypingTrace (Ctx, Expr, Ty)
  | SubtypeTrace (Ctx, Ty, Ty)
  | InstLTrace (Ctx, Ty, Ty)
  | InstRTrace (Ctx, Ty, Ty)
  deriving Show

type JudgmentGraph = PT.Gr JudgmentTrace FunctionCall

data FunctionCall =
    TyCheck
  | TyInfer
  | TyAppInfer
  -- TODO: Unimplemented in Check.hs
  | InstL
  | InstR
  | SubtypeOf
  deriving (Show)

data GBuilder = GBuilder
  { nodeCounter :: Int
  , nodes :: [G.LNode JudgmentTrace]
  , edges :: [G.LEdge FunctionCall]
  }

data MetaData = MetaData
  { varCounter :: Int
  , judgmentBuilder :: GBuilder
  }

initMetaData :: MetaData
initMetaData = MetaData 0 initGBuilder
  where
    initGBuilder = GBuilder 0 [] []

getNewVar :: Text -> TyStateT Text
getNewVar varName = do
  v <- gets varCounter
  modify $ \s -> s { varCounter = v + 1 }
  return $ Text.concat [varName, Text.pack $ show v]

-- NOTE: This assumes a call to `createJudgmentTrace` after the
-- child node is fully constructed!
getNode :: TyStateT Int
getNode = pred <$> gets (nodeCounter . judgmentBuilder)

-- `createJudgmentTrace src tgts` takes a src node,
-- and a list of (tgtNode, edge) pair, and connects
-- src --edge--> tgtNode
createJudgmentTrace ::
  JudgmentTrace ->
  [(G.Node, FunctionCall)] ->
  TyStateT ()
createJudgmentTrace srcLabel [] = do
  builder <- gets judgmentBuilder
  let curNodes = nodes builder
      srcNode = nodeCounter builder
  modify $ \s -> s
    { judgmentBuilder = builder
      { nodes = (srcNode, srcLabel) : curNodes
      , nodeCounter = srcNode + 1
      }
    }
createJudgmentTrace srcLabel ((tgtNode, edgeLabel):rest) = do
  builder <- gets judgmentBuilder
  let curEdges = edges builder
      srcNode = nodeCounter builder
  modify $ \s -> s
    { judgmentBuilder = builder
      { edges = (srcNode, tgtNode, edgeLabel):curEdges }
    }
  createJudgmentTrace srcLabel rest

data Expr =
    Var Text
  | UnitTerm
  | Lam Text Expr
  | App Expr Expr
  | Ann Expr Ty
  deriving (Eq, Show)

type Name = Text

data Decl = 
  Decl Name Expr (Maybe Ty)

data Ty =
    UnitTy
  | TyVar Text
  | TyVarHat Text
  | TyArrow Ty Ty
  | Forall Text Ty
  deriving (Eq, Ord, Show)

data CtxItem =
    CtxItem Text
  | CtxMapping { termVar :: Text, tyItem :: Ty }
  | CtxItemHat Text
  | CtxEquality { tyVarHat :: Text, tyEqTo :: Ty }
  | CtxMarker Text
  deriving (Eq, Show)

type Ctx = [CtxItem]

