{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Text.Parsec
import Types
import Parser.Prelude
import Lexer (lexMain, runLex)

import qualified Data.Text.IO as TIO
import qualified Data.Text as Text
import Data.Text (Text)

import qualified Data.Map as Map

import Data.Text.Prettyprint.Doc
import Pretty


declarations :: Parser DeclMap
declarations = do
    many $ do 
        (n, e, mT) <- declaration
        modifyState (\(ParserState map) -> ParserState $ Map.insert n (e, mT) map)
    run <$> getState

declaration :: Parser (Name, Expr, Maybe Ty)
declaration = do
    mNT <- optionMaybe $ try $ do
            v <- var
            myToken HasTypeA
            t <- type'
            myToken BlockEndA
            pure (v, t)
    v <- var
    myToken EqA
    e <- expr
    myToken BlockEndA

    case mNT of
        Just (v', t) ->
            if v == v' then pure (v', e, Just t)
            else fail $ Text.unpack $ Text.concat ["Type signature for `", v', "` is accompanied by a binding for `", v, "`"]
        Nothing ->
            pure (v, e, Nothing)

expr :: Parser Expr
expr = do
    e <- choice
        [
            lambda
        ,   term
        ]
    do
        e <- choice
            [ try $ do
                myToken HasTypeA
                t <- type'
                pure $ Ann e t
            , pure e
            ]
        pure e


term :: Parser Expr
term = do
    f <- choice
        [
            factor
        ]
    choice 
        [
            try $ do
                f' <- factor
                pure $ App f f'
        ,   pure f
        ]

factor :: Parser Expr
factor = do
    choice
        [
            try $ do
                myToken LParenA
                e <- expr
                myToken RParenA
                pure e
        ,   Var <$> var
        ,   unit
        ]


lambda :: Parser Expr
lambda = do
    myToken LambdaA
    v <- var
    myToken ArrowA
    e <- expr
    pure $ Lam v e

ann :: Parser Expr
ann = do
    e <- expr
    myToken HasTypeA
    t <- type'
    pure $ Ann e t

var :: Parser Name
var = try $ do
    (nextToken, _) <- anyToken 
    case nextToken of
        LowerNameA name -> pure name
        _ -> fail "Expected a variable name starting with a lowercase letter"

unit :: Parser Expr
unit = do
    myToken UnitA
    pure UnitTerm

type' :: Parser Ty
type' = do
    t <- choice
        [
            unitTy
        ,   tyVar
        ,   tyForall
        ,   do
                myToken LParenA
                t <- type'
                myToken RParenA
                pure t
        ]

    mT' <- optionMaybe $ do
        myToken ArrowA
        type'
    
    pure $ case mT' of
        Just t' -> TyArrow t t'
        Nothing -> t

    -- ts <- many $ do
    --         myToken ArrowA
    --         type'
    -- pure $ foldr (\a b -> TyArrow b a) t ts

unitTy :: Parser Ty 
unitTy = do
    myToken UnitA
    pure UnitTy

tyVar :: Parser Ty
tyVar = do
    v <- var
    pure $ TyVar v

tyArrow :: Parser Ty
tyArrow = do
    ty0 <- type'
    myToken ArrowA
    ty1 <- type'
    pure $ TyArrow ty0 ty1

tyForall :: Parser Ty
tyForall = do
    myToken ForallA
    v <- var
    myToken PeriodA
    t <- type'
    pure $ Forall v t

runParse :: [Token] -> Either ParseError DeclMap
runParse tokens =
    runParser declarations (ParserState Map.empty) "" tokens

runExprTest :: Text -> IO ()
runExprTest text = do
    let lexResult = runLex text
    case lexResult of
        Left err -> print err
        Right tokens -> do
            putStrLn "==== Lexing Results ===="
            print tokens
            let parseResult = runParse tokens
            putStrLn "\n==== Parsing Results ===="
            case parseResult of
                Left err -> print err
                Right val -> do
                    print val
    pure ()

runTest :: Text -> IO ()
runTest text = do
    let lexResult = runLex text
    case lexResult of
        Left err -> print err
        Right tokens -> do
            putStrLn "==== Lexing Results ===="
            print tokens
            let parseResult = runParse tokens
            putStrLn "\n==== Parsing Results ===="
            case parseResult of
                Left err -> print err
                Right val -> do
                    print $ pretty val
    pure ()

runTestFile :: FilePath -> IO ()
runTestFile filepath = do
    text <- TIO.readFile filepath
    runTest text