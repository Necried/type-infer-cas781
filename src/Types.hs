module Types where

import Utils

import Control.Monad.Trans.State.Strict

import Data.Text (Text)
import qualified Data.Text as Text

type Result a = Either Text a

type TyStateT a = StateT MetaData (Either Text) a

data MetaData = MetaData
  { varCounter :: Int
  } deriving Show

initMetaData = MetaData 0

getNewVar :: Text -> TyStateT Text
getNewVar varName = do
  v <- gets varCounter
  modify $ \s -> s { varCounter = v + 1 }
  return $ Text.concat [varName, Text.pack $ show v]

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

