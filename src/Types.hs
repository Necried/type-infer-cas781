module Types where

import Utils

import Control.Monad.Trans.State.Strict

type Result a = Either String a

type TyStateT a = StateT MetaData (Either String) a

data MetaData = MetaData
  { varCounter :: Int
  }

initMetaData = MetaData 0

getNewVar :: String -> TyStateT String
getNewVar varName = do
  v <- gets varCounter
  modify $ \s -> s { varCounter = v + 1 }
  return $ varName ++ show v

data Term =
    Var String
  | UnitTerm
  | Lam String Term
  | App Term Term
  | Ann Term Ty
  deriving (Eq, Show)

data Ty =
    UnitTy
  | TyVar String
  | TyVarHat String
  | TyArrow Ty Ty
  | Forall String Ty
  deriving (Eq, Ord, Show)

data CtxItem =
    CtxItem String
  | CtxMapping { termVar :: String, tyItem :: Ty }
  | CtxItemHat String
  | CtxEquality { tyVarHat :: String, tyEqTo :: Ty }
  | CtxMarker String
  deriving (Eq, Show)

type Ctx = [CtxItem]

