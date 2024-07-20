{-# LANGUAGE FlexibleContexts #-}

module Parser.Prelude where

import Text.Parsec
import Data.Map.Strict
import Types
import Data.Text (Text)
import qualified Data.Text as Text


data ParserState = 
    ParserState { run :: DeclMap }
    deriving (Eq, Show)

data DeclMap = DeclMap [(Name,(Expr, Maybe Ty))]
    deriving (Eq, Show)

type Parser a = Parsec [Token] ParserState a

type Lexer a = Parsec Text () a

type Symbol = Text

type Token = (RawToken, SourcePos)

data RawToken 
    = TypeA
    | AliasA
    | EqA
    | PipeA
    | LBrackA
    | RBrackA
    | LParenA
    | RParenA
    | CommaA
    | PeriodA
    | HasTypeA
    | ColonA
    | UnderscoreA
    | ArrowA
    | ForallA
    | UnitA
    | IfA
    | ThenA
    | ElseA
    | LetA
    | InA
    | PlusA
    | MinusA
    | TimesA
    | DivideA
    | LTA
    | LTEA
    | GTA
    | GTEA
    | EqRA
    | AndA
    | OrA
    | UpperNameA Name
    | LowerNameA Name
    | Comment Text
    | IntegerA Int
    | DoubleA Double
    | BooleanA Bool
    | LambdaA
    | BlockEndA         --end of a "block", happens when there is a new definition
    | OtherA Text
    deriving (Eq, Show)

anyExcept :: RawToken -> Parser RawToken
anyExcept x = token showTok posFromTok testTok
    where
        showTok (t, pos) = show t
        posFromTok (t, pos) = pos
        testTok (t, pos) = if x /= t then Just t else Nothing

myToken x
   = token showTok posFromTok testTok
   where
        showTok (t,pos)     = show t
        posFromTok (t, pos) = pos
        testTok (t, pos)    = if x == t then Just t else Nothing