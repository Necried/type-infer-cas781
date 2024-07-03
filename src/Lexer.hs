{-# LANGUAGE OverloadedStrings #-}

module Lexer where

import Data.Text (Text)
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
            try lexEqA,
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

runTestFile :: FilePath -> IO ()
runTestFile filepath = do
    text <- TIO.readFile filepath
    runTest text