{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}

module Pretty where

import Prelude hiding(LT,LTE,GT,GTE)

import Data.List
import Data.Text (Text)
import Data.Text.Prettyprint.Doc

import Data.Map (toList)

import Types
import Parser.Prelude

instance Pretty DeclMap where
    pretty (DeclMap declMap) = vsep $ map prettyOne declMap
        where
            prettyOne (name, (e, Just t)) = 
                pretty name <+> "::" <+> pretty t <> hardline <>
                pretty name <+> "="  <+> pretty e <> hardline
            prettyOne (name, (e, Nothing)) = 
                pretty name <+> "="  <+> pretty e <> hardline

instance Pretty Expr where
    pretty (Var v) = pretty v
    pretty (LiteralExpr l) = pretty l
    -- TODO: Should use something more flexible than hsep here
    pretty (Tuple exprs) = parens $ hsep $ punctuate comma $ map pretty exprs
    pretty (If p e1 e2) = "if" <+> pretty p <+> "then" <+> pretty e1 <+> pretty e2
    pretty (BinOpExpr binOp e1 e2) =
      pretty e1 <+> pretty binOp <+> pretty e2
    pretty (PredOpExpr predOp e1 e2) =
      pretty e1 <+> pretty predOp <+> pretty e2
    pretty (Let x e1 e2) =
      align $ vsep
        [ "let"
        , hang 2 $ pretty x <+> "=" <+> pretty e1
        , "in"
        , hang 2 $ pretty e2
        ]
    pretty (Lam x e) = parens $ "\\" <+> pretty x <+> "->" <+> pretty e
    pretty (App e0 e1) = parens (pretty e0) <+> parens (pretty e1)
    pretty (Ann e t) = pretty e <+> "::" <+> pretty t

instance Pretty Literal where
    pretty UnitTerm = "()"
    pretty (BooleanTerm b) = pretty b
    pretty (IntegerTerm i) = pretty i
instance Pretty Pat where
    pretty (VarPat p) = pretty p
    pretty (TuplePat pats) = pretty pats
    pretty WildCardPat = "_"
    
instance Pretty Op where
  pretty Plus = "+"
  pretty Minus = "-"
  pretty Mult = "*"
  pretty Divide = "/"

instance Pretty PredOp where
  pretty LT = "<"
  pretty LTE = "<="
  pretty GT = ">"
  pretty GTE = ">="
  pretty Eq = "=="
  pretty And = "&&"
  pretty Or = "||"

instance Pretty Ty where
    pretty UnitTy = "()"
    pretty BooleanTy = "Bool"
    pretty IntegerTy = "Int"
    pretty (TupleTy tys) = parens $ hsep $ punctuate comma $ map pretty tys
    pretty (TyVar v) = pretty v
    pretty (TyVarHat v) = pretty v <> "Hat"
    pretty (TyArrow t0 t1) = pretty t0 <+> "->" <+> pretty t1
    pretty (Forall x t) = "forall" <+> pretty x <+> "." <+> pretty t

instance Pretty CtxItem where
    pretty (CtxItem item) = pretty item
    pretty (CtxMapping exprVar tyItem) = pretty exprVar <+> ":" <+> pretty tyItem
    pretty (CtxItemHat itemHat) = pretty itemHat <> "Hat"
    pretty (CtxEquality tvHat tyEq) = pretty tvHat <+> "=" <+> pretty tyEq
    pretty (CtxMarker marker) = pretty marker <> "Mark"

instance Pretty JudgmentTrace where
    pretty (TyCheckTrace (ctx, expr, ty)) =
      "TyCheck" <+> hardline <> vcat
        [ "Ctx:" <+> pretty ctx
        , "Expr:" <+> pretty expr
        , "Ty:" <+> pretty ty]
    pretty (TyInferTrace (ctx, expr)) =
      "TyInfer" <+> hardline <> vcat
        [ "Ctx:" <+> pretty ctx
        , "Expr:" <+> pretty expr ]
    pretty (TyAppInferTrace (ctx, ty, expr)) =
      "TyAppInfer" <+> hardline <> vcat
        [ "Ctx:" <+> pretty ctx
        , "Expr:" <+> pretty expr
        , "Ty:" <+> pretty ty]
    pretty (SubtypeTrace (ctx, t1, t2)) =
      "Sub" <+> prettyTraceTemplate ctx t1 t2
    pretty (InstLTrace (ctx, t1, t2)) =
      "InstL" <+> prettyTraceTemplate ctx t1 t2
    pretty (InstRTrace (ctx, t1, t2)) =
      "InstR" <+> prettyTraceTemplate ctx t1 t2
    pretty EmptyTrace = ""

prettyTraceTemplate :: Ctx -> Ty -> Ty -> Doc ann
prettyTraceTemplate ctx t1 t2 =
    hardline <> vcat
      [ "Ctx:" <+> pretty ctx
      , "t1:" <+> pretty t1
      , "t2:" <+> pretty t2]

