{-# LANGUAGE OverloadedStrings #-}

module Lexer where

import Data.Text (Text)
import Text.Read (readMaybe)
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import Text.Parsec
import Types
import Data.Map (Map)
import qualified Data.Map as Map

import Parser.Prelude

spaces1 :: Lexer ()
spaces1 = skipMany1 space

lexMain :: Lexer [Token]
lexMain = do
    spaces
    tokens <- concat <$> sepEndBy lexToken spaces
    spaces
    eof
    pos <- getPosition
    return $ tokens ++ [(BlockEndA, pos)]

lexToken :: Lexer [Token]
lexToken = do
    currentInput <- getInput
    pos <- getPosition
    let newBlockToken = 
            if sourceColumn pos == 1 &&
                sourceLine pos /= 1 &&
                currentInput /= "" && 
                Text.head currentInput /= ' ' then
                [(BlockEndA, pos)]
            else
                []
    token <- choice
        [
            try lexComment,
            try lexTypeA,
            try lexAliasA,
            try lexPipeA,
            try lexUnitA,
            try lexLBrackA,
            try lexRBrackA,
            try lexLParenA,
            try lexRParenA,
            try lexCommaA,
            try lexPeriodA,
            try lexHasTypeA,
            try lexColonA,
            try lexUnderscoreA,
            try lexArrowA,
            try lexForallA,
            try lexDoubleA,
            try lexIntegerA,
            try lexBooleanA,
            try lexIfA,
            try lexThenA,
            try lexElseA,
            try lexLetA,
            try lexInA,
            try lexBinOpA,
            try lexPredOpA,
            try lexEqA,
            try lexLambdaA,
            try lexUpperNameA,
            try lexLowerNameA,
            otherToken
        ]
    pos <- getPosition
    return $ 
        case token of
            Comment _ -> []
            _ ->         newBlockToken ++ [(token, pos)]

lexTypeA :: Lexer RawToken
lexTypeA = do
    string "type"
    return TypeA

lexAliasA :: Lexer RawToken
lexAliasA = do
    string "alias"
    return AliasA

lexEqA :: Lexer RawToken
lexEqA = do
    char '='
    return EqA

lexPipeA :: Lexer RawToken
lexPipeA = do
    char '|'
    return PipeA

lexLBrackA :: Lexer RawToken
lexLBrackA = do
    char '{'
    return LBrackA

lexRBrackA :: Lexer RawToken
lexRBrackA = do
    char '}'
    return RBrackA

lexLParenA :: Lexer RawToken
lexLParenA = do
    char '('
    return LParenA

lexRParenA :: Lexer RawToken
lexRParenA = do
    char ')'
    return RParenA

lexCommaA :: Lexer RawToken
lexCommaA = do
    char ','
    return CommaA

lexPeriodA :: Lexer RawToken
lexPeriodA = do
    char '.'
    return PeriodA

lexHasTypeA :: Lexer RawToken
lexHasTypeA = do
    string "::"
    return HasTypeA

lexColonA :: Lexer RawToken
lexColonA = do
    char ':'
    return ColonA

lexUnderscoreA :: Lexer RawToken
lexUnderscoreA = do
    char '_'
    return UnderscoreA

lexArrowA :: Lexer RawToken
lexArrowA = do
    string "->"
    return ArrowA

lexForallA :: Lexer RawToken
lexForallA = do
    string "forall"
    return ForallA

lexDoubleA :: Lexer RawToken
lexDoubleA = do
    digits <- many digit
    char '.'
    decimals <- many digit
    let mDub = readMaybe $ digits ++ ['.'] ++ decimals
    
    case mDub of
        Just d -> 
            return $ DoubleA d
        Nothing ->
            fail "Expected an double"

lexIntegerA :: Lexer RawToken
lexIntegerA = do
    digits <- many digit
    let mInt = readMaybe digits
    
    case mInt of
        Just i -> 
            return $ IntegerA i
        Nothing ->
            fail "Expected an integer"

lexBooleanA :: Lexer RawToken
lexBooleanA = choice
    [
        string "True"  >> pure (BooleanA True)
    ,   string "False" >> pure (BooleanA False)
    ]

lexIfA :: Lexer RawToken
lexIfA = do
    string "if"
    return IfA

lexThenA :: Lexer RawToken
lexThenA = do
    string "then"
    return ThenA

lexElseA :: Lexer RawToken
lexElseA = do
    string "else"
    return ElseA

lexLetA :: Lexer RawToken
lexLetA = do
    string "let"
    return LetA

lexInA :: Lexer RawToken
lexInA = do
    string "in"
    return InA

lexBinOpA :: Lexer RawToken
lexBinOpA = 
    choice
        [
            lexPlusA
        ,   lexMinusA
        ,   lexTimesA
        ,   lexDivideA
        ]

lexPlusA :: Lexer RawToken
lexPlusA = do
    string "+"
    return PlusA

lexMinusA :: Lexer RawToken
lexMinusA = do
    string "-"
    return MinusA

lexTimesA :: Lexer RawToken
lexTimesA = do
    string "*"
    return TimesA

lexDivideA :: Lexer RawToken
lexDivideA = do
    string "/"
    return DivideA

lexPredOpA :: Lexer RawToken
lexPredOpA = 
    choice
        [
            lexLTA
        ,   lexLTEA
        ,   lexGTA
        ,   lexGTEA
        ,   lexEqRA
        ,   lexAndA
        ,   lexOrA
        ]

lexLTA :: Lexer RawToken
lexLTA = do
    string "<"
    return LTA

lexLTEA :: Lexer RawToken
lexLTEA = do
    string "<="
    return LTEA

lexGTA :: Lexer RawToken
lexGTA = do
    string ">"
    return GTA

lexGTEA :: Lexer RawToken
lexGTEA = do
    string ">="
    return GTEA

lexEqRA :: Lexer RawToken
lexEqRA = do
    string "=="
    return EqRA

lexAndA :: Lexer RawToken
lexAndA = do
    string "&&"
    return AndA

lexOrA :: Lexer RawToken
lexOrA = do
    string "||"
    return OrA

lexUnitA :: Lexer RawToken
lexUnitA = do
    string "()"
    return UnitA

lexUpperNameA :: Lexer RawToken
lexUpperNameA = do
    name <- upperName
    return $ UpperNameA name

lexLowerNameA :: Lexer RawToken
lexLowerNameA = do
    name <- lowerName
    return $ LowerNameA name

lexLambdaA :: Lexer RawToken
lexLambdaA = do
    string "\\"
    return LambdaA

upperName :: Lexer Text
upperName = do
    first <- upper
    rest <- many alphaNum
    return $ Text.pack $ first : rest

lowerName :: Lexer Text
lowerName = do
    first <- lower
    rest <- many alphaNum
    return $ Text.pack $ first : rest

lexComment :: Lexer RawToken
lexComment = do
    choice [lexSingleLineComment, lexMultilineComment]

lexSingleLineComment :: Lexer RawToken
lexSingleLineComment = do
    lexSLCommentA
    comment <- many (noneOf "\n")
    char '\n'
    pure $ Comment $ Text.pack comment

lexMultilineComment :: Lexer RawToken
lexMultilineComment = do
    lexMLCommentOpenA
    comment <- manyTill anyChar (try lexMLCommentCloseA)
    pure $ Comment $ Text.pack comment

lexSLCommentA :: Lexer ()
lexSLCommentA = do
    string "--"
    pure ()

lexMLCommentOpenA :: Lexer ()
lexMLCommentOpenA = do
    string "{-"
    pure ()

lexMLCommentCloseA :: Lexer ()
lexMLCommentCloseA = do
    string "-}"
    pure ()

otherToken :: Lexer RawToken
otherToken = do
    txt <- manyTill anyChar spaces1
    return $ OtherA $ Text.pack txt

runLex :: Text -> Either ParseError [Token]
runLex text =
    runParser lexMain () "" text

runTest :: Text -> IO ()
runTest text = do
    let result = runParser lexMain () "" text
    case result of
        Left err -> print err
        Right val -> print val
    pure ()

runTestGeneric :: Lexer RawToken -> Text -> IO ()
runTestGeneric lexer text = do
    let result = runParser lexer () "" text
    case result of
        Left err -> print err
        Right val -> print val
    pure ()

runTestFile :: FilePath -> IO ()
runTestFile filepath = do
    text <- TIO.readFile filepath
    runTest text