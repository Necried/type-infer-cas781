{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module WholeTest where

import Data.Text (Text)
import Data.String.QQ

import Parser
import Lexer
import Check
import Types

import Parser.Prelude
import Text.Parsec

import Test.Hspec ( hspec, describe, it, shouldBe, Expectation )
import Test.Tasty.HUnit ( assertFailure )

-- Test utils
data TestBidirectionalMode = TestCheck | TestInfer

assertCheckCorrect :: Expr -> Ty -> Bool
assertCheckCorrect expr ty =
  case runTyCheck [] expr ty of
    Left _ -> False
    Right _ -> True

assertInferCorrect :: Expr -> Ty -> Bool
assertInferCorrect expr ty =
  case runTyInfer [] expr of
    Left _ -> False
    Right (resTy, _) -> resTy == ty

passingTestCase :: TestBidirectionalMode -> Text -> Text -> Expectation
passingTestCase testMode prog ty =
  let
    runLexParserTy t = runLex t >>= runParser type' (ParserState $ DeclMap []) ""
  in case (runLexParseExpr prog, runLexParserTy ty) of
    (Right exprProg, Right exprTy) -> 
      case testMode of
        TestCheck -> assertCheckCorrect exprProg exprTy `shouldBe` True
        TestInfer -> assertInferCorrect exprProg exprTy `shouldBe` True
    (Left err, _) ->
      assertFailure $ show err
    (_, Left err) ->
      assertFailure $ show err 

mkPairFunction :: Text
mkPairFunction = [s|
  \a -> \b -> (a, b)
|]

mkPairType :: Text
mkPairType = [s| forall a. forall b. a -> b -> (a, b) |]

facFunction :: Text
facFunction = [s| 
  let fac = \n -> if n == 0 then 1 else n * (fac (n - 1))
  in fac 5
|]

runTest :: IO ()
runTest = hspec $ do
  describe "Basic tests" $ do
    describe "Binary operations" $ do
      do it "Addition and multiplication" (passingTestCase TestInfer "3 + 4 * 5" " Int")
      do it "With parenthesis" (passingTestCase TestInfer "(3 / 4) * 5 - 6" "Int")
      do it "Less than" (passingTestCase TestInfer "-5 < -10" "Bool")
    describe "If-then-else" $ do
      do it "If-then-else top-level case #1" (passingTestCase TestCheck "if True then 2 else 1" "Int")
  describe "Advanced Tests" $ do
    describe "Tuples" $ do
      do it "Make pair" $ passingTestCase TestCheck mkPairFunction mkPairType
    describe  "Recursive let-declarations" $ do
          do it "Factorial function" (passingTestCase TestInfer facFunction "Int")