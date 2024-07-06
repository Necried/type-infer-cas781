{-# LANGUAGE OverloadedStrings #-}

module Eval where

import Types

import Prelude hiding (LT, GT)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Text (Text)

-- NOTE: Currently unused: The environment performs the
-- substitution now.
-- termSubst [x := t]E
termSubst :: Text -> Expr -> Expr -> Expr
termSubst _ _ UnitTerm = UnitTerm
termSubst x t (Var y)
  | x == y = t
  | otherwise = Var y
-- Assuming no variable clashes here.
-- Precondition: y != x, otherwise, name capturing will happen
termSubst x t (Lam y e) =
  Lam y $ termSubst x t e
termSubst x t (App e1 e2) =
  App (termSubst x t e1) (termSubst x t e2)
termSubst x t (Ann e _) =
  termSubst x t e

data Value =
    UnitValue
  | IntegerValue Int
  | BooleanValue Bool
  | LamValue Text (Value -> Value)
  | NValue NeutralValue
  
data NeutralValue =
    NFree Text
  | NApp NeutralValue Value
  deriving (Show)

instance Show Value where
  show UnitValue = "UnitValue"
  show (LamValue x f) = "\\" ++ show x ++ ". " ++ show (f (NValue $ NFree x))
  show (NValue nv) = show nv
  show (IntegerValue i) = show i
  show (BooleanValue b) = show b

type Env = Map Text Value

empty :: Env
empty = Map.empty

eval :: Env -> Expr -> Value
eval _ UnitTerm = UnitValue
eval _ (BooleanTerm b) = BooleanValue b
eval _ (IntegerTerm i) = IntegerValue i
eval env e@(BinOpExpr op e1 e2) =
  case (eval env e1, eval env e2) of
    (IntegerValue i1, IntegerValue i2) -> IntegerValue $ applyOp i1 i2
    _ -> error $ "eval: binOp: " ++ show e
  where
    applyOp = case op of
      Plus -> (+)
      Minus -> (-)
      Mult -> (*)
      Divide -> div
eval env e@(PredOpExpr op e1 e2) =
  case (eval env e1, eval env e2) of
    (IntegerValue i1, IntegerValue i2) -> BooleanValue $ applyIOp i1 i2
    (BooleanValue b1, BooleanValue b2) -> BooleanValue $ applyBOp b1 b2
    _ -> error $ "eval: predOp: " ++ show e
  where
    -- NOTE: Both pattern matches are non-exhaustive, but we assume that
    -- expressions are already typechecked
    applyIOp = case op of
      LT -> (<)
      GT -> (>)
      LTE -> (<=)
      GTE -> (>=)
    applyBOp = case op of
      Eq -> (==)
      And -> (&&)
      Or -> (||)
eval env e@(If p e1 e2) = case eval env p of
  (BooleanValue True) -> eval env e1
  (BooleanValue False) -> eval env e2
  _ -> error $ "eval: if expression: " ++ show e
eval env (Var x) =
  case M.lookup x env of
    Nothing -> error $ "eval: variable " ++ show x ++ " not in scope"
    Just v -> v
eval env (Lam x t) =
  LamValue x $ \v -> eval (M.insert x v env) t
eval env (App e1 e2) = vapp (eval env e1) (eval env e2)
eval env (Ann e _) = eval env e

vapp :: Value -> Value -> Value
vapp (LamValue _ f) v = f v
vapp (NValue n)     v = NValue (NApp n v)
vapp v' _ = error $ "Couldn't apply value " ++ show v'
