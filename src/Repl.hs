module Repl where

import System.Console.Haskeline
import Parser
import Eval
import Check
import Lexer
import qualified Data.Text as Text
import Data.List (intercalate)
import Types

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

type ExprEnv = Map Name (Value, Expr)

main :: IO ()
main = runInputT defaultSettings (loop Map.empty)
    where
        loop :: ExprEnv -> InputT IO ()
        loop env = do
            minput <- getInputLine "λ "
            newEnv <- case minput of
                Nothing -> pure env
                Just ":q" -> pure env
                Just (':':'t':rest) -> 
                    let 
                        txt = Text.pack rest
                    in do
                        case runLexParseExpr txt of
                            Right expr ->
                                case runTyInfer [] expr of
                                    Right (ty, ctx) ->
                                        outputStrLn $ show ty
                                    Left err -> outputStrLn $ Text.unpack err
                            Left err ->
                                outputStrLn $ show err
                        pure env
                Just (':':'l':rest) -> 
                    let 
                        txt = Text.pack rest
                    in do
                        case runLex txt of
                            Right tokens ->
                                outputStrLn $
                                    showToks tokens
                            Left err ->
                                outputStrLn $ show err
                        pure env
                Just str ->
                    let 
                        txt = Text.pack str
                    in
                        case runLexParse txt of
                            Right (Left expr) -> do
                                outputStrLn $ show $ eval (toEnv env) expr
                                pure env
                            Right (Right (name, expr, _)) ->
                                let
                                    val = eval (toEnv env) expr
                                in do
                                    outputStrLn $ show val
                                    pure $ Map.insert name (val, expr) env
                            Left err -> do
                                outputStrLn $ show err
                                pure env
            loop newEnv
        
        toEnv :: ExprEnv -> Env
        toEnv = Map.map fst

        showToks =
            intercalate ", " .
                map (\(tok, pos) -> show tok ++ " " ++ show pos)