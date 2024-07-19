module Repl where

import System.Console.Haskeline
import Parser
import Eval
import Check
import Lexer
import qualified Data.Text as Text
import Data.List (intercalate)
import Types
import Utils ((<:))

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

type ExprEnv = [(Name, (Value, Expr))]

data ReplState = 
    ReplState { env :: ExprEnv }

initState = ReplState []

main :: IO ()
main = runInputT defaultSettings (loop initState)
    where
        loop :: ReplState -> InputT IO ()
        loop state = do
            let 
                ins :: Expr -> Expr
                ins expr = 
                    foldr (\(name,(_, expr)) e -> Let (VarPat name) expr e) expr (env state)
            minput <- getInputLine "λ "
            newEnv <- case minput of
                Nothing -> pure state
                Just ":q" -> pure state
                Just (':':'t':rest) -> 
                    let 
                        txt = Text.pack rest
                    in do
                        case runLexParseExpr txt of
                            Right expr -> do
                                outputStrLn $ show (ins expr)
                                case runTyInfer [] (ins expr) of
                                    Right (ty, ctx) ->
                                        outputStrLn $ show ty
                                    Left err -> outputStrLn $ show err
                            Left err ->
                                outputStrLn $ show err
                        pure state
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
                        pure state
                Just (':':'v':rest) -> 
                    let 
                        txt = Text.pack rest
                    in do
                        case runLex txt of
                            Right tokens -> do
                                outputStrLn $ showToks tokens
                                case runLexParse txt of
                                    Right (Left expr) -> do
                                        outputStrLn $ show expr
                                        outputStrLn $ show $ eval (toEnv $ env state) (ins expr)
                                        pure state
                                    Right res@(Right (name, expr, _)) -> do
                                        outputStrLn $ show res
                                        case runTyInfer [] (ins expr) of
                                            Right (ty, ctx) -> 
                                                let
                                                    val = eval (toEnv $ env state) (ins expr)
                                                in do
                                                    outputStrLn $ show ctx
                                                    outputStrLn $ show val
                                                    pure $ state 
                                                        { env = env state ++ [(name, (val, expr))]
                                                        }
                                            Left err -> do
                                                outputStrLn $ show err
                                                pure state
                                    Left err -> do
                                        outputStrLn $ show err
                                        pure state
                            Left err -> do
                                outputStrLn $ show err
                                pure state
                        pure state
                Just str ->
                    let 
                        txt = Text.pack str
                    in
                        case runLexParse txt of
                            Right (Left expr) -> do
                                outputStrLn $ show $ eval (toEnv $ env state) (ins expr)
                                pure state
                            Right (Right (name, expr, _)) ->
                                case runTyInfer [] (ins expr) of
                                    Right (ty, ctx) -> 
                                        let
                                            val = eval (toEnv $ env state) (ins expr)
                                        in do
                                            outputStrLn $ show ctx
                                            outputStrLn $ show val
                                            pure $ state 
                                                { env = env state ++ [(name, (val, expr))]
                                                }
                                    Left err -> do
                                        outputStrLn $ show err
                                        pure state
                            Left err -> do
                                outputStrLn $ show err
                                pure state
            loop newEnv
        
        toEnv :: ExprEnv -> Env
        toEnv = Map.map fst . Map.fromList

        showToks =
            intercalate ", " .
                map (\(tok, pos) -> show tok ++ " " ++ show pos)