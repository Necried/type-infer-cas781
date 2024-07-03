{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}

module Test where

import Types
import Check
import Eval
import Dot

import qualified Data.Map.Strict as M

import Control.Applicative

-----------------
-- Check Tests --
-----------------

-- Helpers

infixr 1 -->
(-->) :: Ty -> Ty -> Ty
a --> b = TyArrow a b

tv = TyVar

-- Basic polymorphic functions

-- id a = a
idType = Forall "a" $ tv "a" --> tv "a"
idBody = Lam "x" $ Var "x"

-- const a b = a
constType = Forall "a" $ Forall "b" $ tv "a" --> tv "b" --> tv "a"
wrongConstType = Forall "a" $ Forall "b" $ tv "a" --> tv "b" --> tv "b"
constBody = Lam "x" $ Lam "y" $ Var "x"

-- flip f a b = f b a
flipType = Forall "a" $ Forall "b" $ Forall "c" $
  (tv "a" --> tv "b" --> tv "c") --> tv "b" --> tv "a" --> tv "c"
wrongFlipType = Forall "a" $ Forall "b" $ Forall "c" $
  (tv "a" --> tv "b" --> tv "c") --> tv "c" --> tv "a" --> tv "a"
flipBody = Lam "f" $ Lam "a" $ Lam "b" $ Var "f" `App` Var "b" `App` Var "a"

-- Church-encoded Booleans
-- Note that this uses RankN quantification!
-- In the body of cAnd, if we expand the bodies of the type defs, we get:
--   cAnd :: (forall a. a -> a -> a) -> (forall a. a -> a -> a) -> (forall a. a -> a -> a) 
type ChurchBool = forall a. a -> a -> a

cTrue :: ChurchBool
cTrue = \t f -> t

cFalse :: ChurchBool
cFalse = \t f -> f

cAnd :: ChurchBool -> ChurchBool -> ChurchBool
cAnd p q = \t f -> p (q t f) f

cOr :: ChurchBool -> ChurchBool -> ChurchBool
cOr p q = \t f -> p t (q t f)

-- cNot is isomorphic to `flip`
cNot :: ChurchBool -> ChurchBool
cNot p = \t f -> p f t 

cAndTFeqT :: ChurchBool
cAndTFeqT = cAnd cTrue cFalse

printCAndTFeqT = cAndTFeqT "t" "f" -- prints "f""

-- Now let's encode Church Booleans in our syntax
cBoolType = Forall "a" $ tv "a" --> tv "a" --> tv "a"
  
cTrueBody = Lam "t" $ Lam "f" $ Var "t"
cFalseBody = Lam "t" $ Lam "f" $ Var "f"

cAndType = cBoolType --> cBoolType --> cBoolType
cAndBody = Lam "p" $ Lam "q" $ Lam "t" $ Lam "f" $
  Var "p" `App` (Var "q" `App` Var "t" `App` Var "f") `App` Var "f"

cOrType = cAndType
cOrBody = Lam "p" $ Lam "q" $ Lam "t" $ Lam "f" $
  Var "p" `App` Var "t" `App` (Var "q" `App` Var "t" `App` Var "f")

-- NOTE: Without the annotation, this will not type check!
cAndTFeqTBody = Ann cAndBody cAndType `App` cTrueBody `App` cFalseBody

-- Let test
letBody = Let "x" (IntegerTerm 2) (BinOpExpr Plus (Var "x") (IntegerTerm 3))
letTy = IntegerTy

-- Test harness
runPassingTests = do
  runTyCheck [] idBody idType
  runTyCheck [] constBody constType
  runTyCheck [] flipBody flipType

  runTyCheck [] cTrueBody cBoolType
  runTyCheck [] cFalseBody cBoolType
  runTyCheck [] cAndBody cAndType
  runTyCheck [] cOrBody cOrType
  runTyCheck [] cAndTFeqTBody cBoolType

runFailingTests = getZipList $ fmap (runTyCheck []) bodies <*> tys
  where
    bodies = ZipList [constBody, flipBody]
    tys = ZipList [wrongConstType, wrongFlipType]

runMkGraphs = do
  dotJudgmentGraph [] idBody (Just idType) "id"
  dotJudgmentGraph [] constBody (Just constType) "const"
  dotJudgmentGraph [] flipBody (Just flipType) "flip"
  
----------------
-- Eval Tests --
----------------

-- function application has highest precedence, and associates left
-- NOTE: do not confuse this with the ($) operator!
infixl 9 |@| -- 9 is the maximum precedence

(|@|) :: Expr -> Expr -> Expr
(|@|) = App

appId = idBody |@| UnitTerm
appFlipPartial = flipBody |@| constBody |@| UnitTerm
appFlip = appFlipPartial |@| UnitTerm 

evalTests = mapM (print . eval M.empty)
  [ appId
  , appFlipPartial
  , appFlip
  ]
