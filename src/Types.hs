{-# LANGUAGE TypeFamilies #-}

module Types where

import Utils

import Control.Monad.Trans.State.Strict

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.PatriciaTree as PT

type Result a = Either Text a

type TyStateT metadata a = StateT metadata (Either Text) a

type RuleName = Text

data JudgmentTrace =
    TyCheckTrace (Ctx, Expr, Ty)
  | TyInferTrace (Ctx, Expr)
  | TyAppInferTrace (Ctx, Ty, Expr)
  | SubtypeTrace (Ctx, Ty, Ty)
  | InstLTrace (Ctx, Ty, Ty)
  | InstRTrace (Ctx, Ty, Ty)
  | EmptyTrace
  deriving Show

type JudgmentGraph = PT.Gr JudgmentTrace JudgmentRule

data JudgmentRule =
    TyCheck RuleName
  | TyInfer RuleName
  | TyAppInfer RuleName
  | InstL RuleName
  | InstR RuleName
  | SubtypeOf RuleName
  deriving (Show)

data GBuilder = GBuilder
  { nodeCounter :: Int
  , nodes :: [G.LNode JudgmentTrace]
  , edges :: [G.LEdge JudgmentRule]
  , traceStack :: [G.LNode JudgmentTrace]
  , nodeStack :: [Int]
  } deriving Show

data MetaData = MetaData
  { varCounter :: Int
  } deriving Show

data MetaDataGBuilder = MetaDataGBuilder
  { judgmentBuilder :: GBuilder
  , metaData :: MetaData
  } deriving Show

initMetaData :: MetaData
initMetaData = MetaData 0

initMetaDataGBuilder :: MetaDataGBuilder
initMetaDataGBuilder = MetaDataGBuilder initBuilder initMetaData
  where initBuilder = GBuilder 0 [] [] [] []


data Expr =
    Var Text
  | LiteralExpr Literal
  | Tuple [Expr]
  | BinOpExpr Op Expr Expr
  | PredOpExpr PredOp Expr Expr
  | If Expr {-condition-} Expr {-then-} Expr {-else-}
  | Let Pat Expr Expr -- let x = e in e'
  | Lam Text Expr
  | App Expr Expr
  | Ann Expr Ty
  deriving (Eq, Show)

data Literal =
    UnitTerm
  | BooleanTerm Bool
  | IntegerTerm Int
  deriving (Eq, Show)

data Pat =
    VarPat Text
  | TuplePat [Pat]
  | WildCardPat
  deriving (Eq, Show)

data Op
  = Plus
  | Minus
  | Mult
  | Divide
  deriving (Eq, Show)

data PredOp
  = LT
  | GT
  | LTE
  | GTE
  | Eq
  | And
  | Or
  deriving (Eq, Show)

type Name = Text

data Decl =
  Decl Name Expr (Maybe Ty)

data Ty =
    UnitTy
  | BooleanTy
  | IntegerTy
  | TupleTy [Ty]
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


class TyJudge metadata where
  completedRule :: JudgmentRule -> Ctx -> TyStateT metadata Ctx
  completedRuleWithTyRet ::
    JudgmentRule -> (Ty, Ctx) -> TyStateT metadata (Ty, Ctx)
  getNewVar :: Text -> TyStateT metadata Text
  subTypeOf :: Ctx -> Ty -> Ty -> TyStateT metadata Ctx
  instL, instR :: Ctx -> Ty -> Ty -> TyStateT metadata Ctx
  tyCheck :: Ctx -> Expr -> Ty -> TyStateT metadata Ctx
  tyInfer :: Ctx -> Expr -> TyStateT metadata (Ty, Ctx)
  tyAppInfer :: Ctx -> Ty -> Expr -> TyStateT metadata (Ty, Ctx)
