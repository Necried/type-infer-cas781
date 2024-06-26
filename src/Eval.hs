module Eval where

import Types

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

-- termSubst [x := t]E
termSubst :: String -> Term -> Term -> Term
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
  | LamValue String (Value -> Value)
  | NValue NeutralValue
  
data NeutralValue =
    NFree String
  | NApp NeutralValue Value
  deriving (Show)

instance Show Value where
  show UnitValue = "UnitValue"
  show (LamValue x f) = "\\" ++ x ++ ". " ++ show (f (NValue $ NFree x))
  show (NValue nv) = show nv
 
type Env = Map String Value

eval :: Env -> Term -> Value
eval env UnitTerm = UnitValue
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
