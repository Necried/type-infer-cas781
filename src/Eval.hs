{-# LANGUAGE OverloadedStrings #-}

module Eval where

import Types

import Prelude hiding (LT, GT)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Text (Text)

import Debug.Pretty.Simple
-- NOTE: Currently unused: The environment performs the
-- substitution now.
-- termSubst [x := t]E
-- termSubst :: Text -> Expr -> Expr -> Expr
-- termSubst _ _ UnitTerm = UnitTerm
-- termSubst x t (Var y)
--   | x == y = t
--  | otherwise = Var y

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
  | TupleValue [Value]
  | LamValue Text Expr
  | NValue NeutralValue
  deriving (Show)

data NeutralValue =
    NFree Text
  | NApp NeutralValue Value
  deriving (Show)

{-
instance Show Value where
  show UnitValue = "UnitValue"
  show (LamValue x f) = "\\" ++ show x ++ ". " ++ show f
  show (NValue nv) = show nv
  show (IntegerValue i) = show i
  show (BooleanValue b) = show b
-}

type Env = Map Text Value

eval :: Env -> Expr -> Value
eval _ (LiteralExpr UnitTerm) = UnitValue
eval _ (LiteralExpr (BooleanTerm b)) = BooleanValue b
eval _ (LiteralExpr (IntegerTerm i)) = IntegerValue i
eval env (Tuple exprs) = TupleValue $ map (eval env) exprs
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
    _ -> error $ "eval: predOp: " ++ show e ++ " with env " ++ show env
  where
    -- NOTE: Both pattern matches are non-exhaustive, but we assume that
    -- expressions are already typechecked
    applyIOp = case op of
      LT -> (<)
      GT -> (>)
      LTE -> (<=)
      GTE -> (>=)
      Eq -> (==)
    applyBOp = case op of
      Eq -> (==)
      And -> (&&)
      Or -> (||)
eval env e@(If p e1 e2) = case eval env p of
  (BooleanValue True) -> eval env e1
  (BooleanValue False) -> eval env e2
  _ -> error $ "eval: if expression: " ++ show e
-- eval env (Let (VarPat x) e1 e2) =
--  eval env (App (Lam x e2) e1)
eval env (Let pat e1 e2) =
  let v1 = pTraceShowId $ eval env e1
      envExtended = pTraceShowId $ assocPatEval env pat v1
  in eval envExtended e2
eval env (Var x) =
  case M.lookup x env of
    Nothing -> error $ "eval: variable " ++ show x ++ " not in scope, in env: " ++ show env
    Just v -> v
eval env (Lam x t) =
  LamValue x t
eval env (App e1 e2) =
  vapp (pTraceShowId env) (eval env e1) (eval env e2)
eval env (Ann e _) = eval env e

vapp :: Env -> Value -> Value -> Value
vapp env (LamValue x f) v = (\vParam -> eval (M.insert x vParam env) f) v
vapp env (NValue n)     v = NValue (NApp n v)
vapp env v' _ = error $ "Couldn't apply value " ++ show v'

assocPatEval :: Env -> Pat -> Value -> Env
assocPatEval env WildCardPat e = env
assocPatEval env (VarPat x) v = M.insert x v env
assocPatEval env (TuplePat pats) (TupleValue values) =
  M.unions $ zipWith (assocPatEval env) pats values
assocPatEval env pat expr =
  error $ "assocPatEval: No case found for pat:" ++ show pat ++ ", expr:" ++ show expr
-- let x = e1 in e2 => vapp (\x . e2) e1
