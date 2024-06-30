{-# LANGUAGE OverloadedStrings #-}

module Dot where

import qualified Data.Graph.Inductive as FGL

import Utils.Dot

import Types

fglToDotGeneric ::
     (FGL.Graph gr, Show b)
  => gr a b
  -> (Int -> String)
  -> (b -> String)
  -> (Int -> a -> [(String,String)])
  -> (b -> [(String,String)])
  -> Dot ()
fglToDotGeneric gr nodeConv edgeConv attrNodesConv attrEdgesConv = do
  let es = FGL.labEdges gr -- :: [(Int, Int, b)]
      ns = FGL.labNodes gr -- :: [(Int, a)]
  mapM_ (\(n,p) -> userNode (userNodeId n) (attrNodesConv n p ++ [("label", nodeConv n)])) ns
  mapM_ (\(a,b,p) -> edge (userNodeId a) (userNodeId b) (attrEdgesConv p ++ [("label", edgeConv p)])) es

graphToDot :: FGL.Graph gr => gr JudgmentTrace FunctionCall -> Dot ()
graphToDot cfg = fglToDotGeneric cfg show show
  (\_ p -> [("xlabel", show p)])
  (const [])

dotToFile :: FGL.Graph gr => String -> gr JudgmentTrace FunctionCall -> IO ()
dotToFile s =
  writeFile (s <> "_callgraph.dot") . showDot . graphToDot
