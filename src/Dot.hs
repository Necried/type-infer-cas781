{-# LANGUAGE OverloadedStrings #-}

module Dot where

import qualified Data.Graph.Inductive as FGL
import Prettyprinter.Render.String
import Prettyprinter

import Utils.Dot

import Types
import Pretty

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
  mapM_ (\(n,p) -> userNode (userNodeId n) (attrNodesConv n p)) ns
  mapM_ (\(a,b,p) -> edge (userNodeId a) (userNodeId b) (attrEdgesConv p ++ [("label", edgeConv p)])) es

graphToDot :: FGL.Graph gr => gr JudgmentTrace JudgmentRule -> Dot ()
graphToDot cfg = fglToDotGeneric cfg (const "") show
  (\_ p -> [("label", renderTrace p)])
  (const [])
  where
    renderTrace = renderString . layoutPretty defaultLayoutOptions . pretty

dotToFile :: FGL.Graph gr => String -> gr JudgmentTrace JudgmentRule -> IO ()
dotToFile s =
  writeFile (s <> "_callgraph.dot") . showDot . graphToDot
