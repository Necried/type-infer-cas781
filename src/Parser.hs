{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

module Parser where

import Prelude hiding(LT,GT,LTE,GTE)

import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Token as Tok (reservedOp, integer, makeTokenParser)
import Text.Parsec.Language (haskellDef)

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

exprOrDecl :: Parser (Either Expr (Name, Expr, Maybe Ty))
exprOrDecl =
    choice
        [
            try $ Right <$> declaration
        ,   Left <$> expr
        ]

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
    e <- buildExpressionParser table term
    choice
        [ try $ do
            myToken HasTypeA
            t <- type'
            pure $ Ann e t
        , pure e
        ]
        <?> "expression"

term = do
    t <- choice 
        [
            paren expr
        ,   try number
        ,   try boolean
        ,   if'
        ,   let'
        ,   lambda
        ,   unit
        ,   Var <$> var
        ]
    choice 
        [
            try $ do
                t' <- term
                pure $ App t t'
        ,   pure t
        ]
        <?> "simple expression"

table   = 
        [ --[prefix MinusA negate, prefix "+" id ]
          [binary TimesA (BinOpExpr Mult) AssocLeft, binary DivideA (BinOpExpr Divide) AssocLeft ]
        , [binary PlusA (BinOpExpr Plus) AssocLeft, binary MinusA (BinOpExpr Minus) AssocLeft ]
        , [binary LTA (PredOpExpr LT) AssocLeft, binary LTEA (PredOpExpr LTE) AssocLeft]
        , [binary EqRA (PredOpExpr Eq) AssocLeft]
        , [binary AndA (PredOpExpr And) AssocLeft]
        , [binary OrA (PredOpExpr Or) AssocLeft]
        ]

binary  token fun assoc = Infix (do{ myToken token; return fun }) assoc
prefix  token fun       = Prefix (do{ myToken token; return fun })
postfix token fun       = Postfix (do{ myToken token; return fun })

number :: Parser Expr
number = do
    (nextToken, _) <- anyToken 
    case nextToken of
        IntegerA n -> pure $ IntegerTerm n
        DoubleA d -> undefined
        _ -> fail "Expected a number"

boolean :: Parser Expr
boolean = do
    (nextToken, _) <- anyToken 
    case nextToken of
        BooleanA b -> pure $ BooleanTerm b
        _ -> fail "Expected True or False"

paren p = do
    myToken LParenA
    r <- p
    myToken RParenA
    pure r

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

if' :: Parser Expr
if' = do
    myToken IfA
    p <- expr
    myToken ThenA
    thn <- expr
    myToken ElseA
    els <- expr
    pure $ If p thn els

let' :: Parser Expr
let' = do
    myToken LetA
    v <- var
    myToken EqA
    e <- expr
    myToken InA
    e' <- expr
    pure $ Let v e e'

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

tyInteger :: Parser Ty
tyInteger = do
    upperName "Int"
    pure IntegerTy

tyBoolean :: Parser Ty
tyBoolean = do
    upperName "Bool"
    pure BooleanTy

upperName :: Text -> Parser ()
upperName n = do
    (nextToken, _) <- anyToken 
    case nextToken of
        UpperNameA n -> pure ()
        _ -> fail $ Text.unpack $ Text.concat ["Expected ", n]


type' :: Parser Ty
type' = do
    t <- choice
        [
            unitTy
        ,   tyVar
        ,   tyForall
        ,   tyInteger
        ,   tyBoolean
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

runLexParseExpr :: Text -> Either ParseError Expr
runLexParseExpr text = do 
    let lexResult = runLex text
    case lexResult of
        Left err -> Left err
        Right tokens ->
            runExprParse tokens

runLexParse :: Text -> Either ParseError (Either Expr (Name, Expr, Maybe Ty))
runLexParse text = do 
    let lexResult = runLex text
    case lexResult of
        Left err -> Left err
        Right tokens ->
            runExprOrDeclParse tokens

runExprParse :: [Token] -> Either ParseError Expr
runExprParse tokens =
    runParser expr (ParserState Map.empty) "" tokens

runExprOrDeclParse :: [Token] -> Either ParseError (Either Expr (Name, Expr, Maybe Ty))
runExprOrDeclParse tokens =
    runParser exprOrDecl (ParserState Map.empty) "" tokens

runExprTest :: Text -> IO ()
runExprTest text = do
    let lexResult = runLex text
    case lexResult of
        Left err -> print err
        Right tokens -> do
            putStrLn "==== Lexing Results ===="
            print tokens
            let parseResult = runExprParse tokens
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