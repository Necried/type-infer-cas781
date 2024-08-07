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

import Test.Hspec ( hspec, describe, it, shouldBe, shouldSatisfy, Expectation )
import Test.Tasty.HUnit ( assertFailure )
import Data.Either ( isRight, isLeft )

-- Test utils
data TestBidirectionalMode = TestCheck | TestInfer

assertCheckCorrect :: Expr -> Ty -> Expectation
assertCheckCorrect e ty =
  runTyCheck [] e ty `shouldSatisfy` isRight

assertInferCorrect :: Expr -> Ty -> Expectation
assertInferCorrect e ty =
  case runTyInfer [] e of
    Left err -> assertFailure $ show err
    Right (resTy, _) -> resTy `shouldBe` ty

assertInferFails :: Expr -> Expectation
assertInferFails e =
  runTyInfer [] e `shouldSatisfy` isLeft

passingTestCase :: TestBidirectionalMode -> Text -> Text -> Expectation
passingTestCase testMode prog ty =
  let
    runLexParserTy t = runLex t >>= runParser type' (ParserState $ DeclMap []) ""
  in case (runLexParseExpr prog, runLexParserTy ty) of
    (Right exprProg, Right exprTy) -> 
      case testMode of
        TestCheck -> assertCheckCorrect exprProg exprTy
        TestInfer -> assertInferCorrect exprProg exprTy
    (Left err, _) ->
      assertFailure $ show err
    (_, Left err) ->
      assertFailure $ show err 

failingTestCase :: Text -> Expectation
failingTestCase prog = 
  case runLexParseExpr prog of
    Right exprProg -> assertInferFails exprProg
    Left err -> assertFailure $ show err

-----------------------------
---- TEST CASES -------------
-----------------------------

polyAnn :: Text
polyAnn = [s| (\x -> \y -> x) : forall a. forall b. a -> b -> a |]

polyAnnType :: Text
polyAnnType = [s| forall a. forall b. a -> b -> a |]

mkPairFunction :: Text
mkPairFunction = [s|
  \a -> \b -> (a, b)
|]

mkPairType :: Text
mkPairType = [s| forall a. forall b. a -> b -> (a, b) |]

fstFunction :: Text
fstFunction = [s|
  \p -> let (a, _) = p in a
|]

fstType :: Text
fstType = [s| forall a. forall b. (a, b) -> a |]

sndFunction :: Text
sndFunction = [s|
  \p -> let (_, b) = p in b
|]

sndType :: Text
sndType = [s| forall a. forall b. (a, b) -> b |]

nestedTuple1 :: Text
nestedTuple1 = [s|
  \p -> let ((a, b), c) = p in (a, (b, c))
|]

nestedTuple1Type :: Text
nestedTuple1Type = [s| forall a. forall b. forall c. ((a, b), c) -> (a, (b, c)) |]

nestedTuple2 :: Text
nestedTuple2 = [s|
  \p -> let ((a, (b, c)), d) = p in (d, (b, c), a)
|]

nestedTuple2Type :: Text
nestedTuple2Type = [s| forall a. forall b. forall c. forall d. ((a, (b, c)), d) -> (d, (b, c), a) |]

polyTupleId :: Text
polyTupleId = [s| let id x : (forall a. a -> a) = x in (id 3, id True) |]

polyTupleIdType :: Text
polyTupleIdType = [s| (Int, Bool) |]

facFunction :: Text
facFunction = [s| 
  let fac = \n -> if n == 0 then 1 else n * (fac (n - 1))
  in fac 5
|]

fibFunction :: Text
fibFunction = [s|
  let fib = \n ->
    if n == 0 then 0
    else if n == 1 then 1
    else fib (n - 1) + fib (n - 2)
  in
    fib
|]

runTest :: IO ()
runTest = hspec $ do
  describe "Basic tests" $ do
    describe "Annotations" $ do
      do it "Annotate const" (passingTestCase TestInfer polyAnn polyAnnType)
    describe "Binary operations" $ do
      do it "Addition and multiplication" (passingTestCase TestInfer "3 + 4 * 5" " Int")
      do it "With parenthesis" (passingTestCase TestInfer "(3 / 4) * 5 - 6" "Int")
      do it "Less than" (passingTestCase TestInfer "-5 < -10" "Bool")
      do it "Less than unary parenthesis" (passingTestCase TestInfer "(-5) < (-10)" "Bool")
    describe "If-then-else" $ do
      do it "If-then-else top-level case #1" (passingTestCase TestCheck "if True then 2 else 1" "Int")
  describe "Advanced Tests" $ do
    describe "Tuples" $ do
      do it "Make pair" $ passingTestCase TestCheck mkPairFunction mkPairType
      do it "fst function" $ passingTestCase TestCheck fstFunction fstType
      do it "snd function" $ passingTestCase TestCheck sndFunction sndType
      do it "Nested #1" $ passingTestCase TestCheck nestedTuple1 nestedTuple1Type
      do it "Nested #2" $ passingTestCase TestCheck nestedTuple2 nestedTuple2Type
    describe "Let-in" $ do
      do it "Polymorphic let declaration" $ passingTestCase TestInfer polyTupleId polyTupleIdType
    describe  "Recursive let-declarations" $ do
      do it "Factorial function" (passingTestCase TestInfer facFunction "Int")
      do it "Fibonacci function" (passingTestCase TestInfer fibFunction "Int -> Int")