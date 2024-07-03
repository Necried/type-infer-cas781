{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}

module Pretty where

import Data.List
import Data.Text (Text)
import Data.Text.Prettyprint.Doc

import Data.Map (toList)

import Types
import Parser.Prelude

instance Pretty DeclMap where
    pretty declMap = vsep $ map prettyOne $ toList declMap
        where
            prettyOne (name, (e, Just t)) = 
                pretty name <+> "::" <+> pretty t <> hardline <>
                pretty name <+> "="  <+> pretty e <> hardline
            prettyOne (name, (e, Nothing)) = 
                pretty name <+> "="  <+> pretty e <> hardline

instance Pretty Expr where
    pretty (Var v) = pretty v
    pretty UnitTerm = "()"
    pretty (Lam x e) = parens $ "\\" <+> pretty x <+> "->" <+> pretty e
    pretty (App e0 e1) = parens (pretty e0) <+> parens (pretty e1)
    pretty (Ann e t) = pretty e <+> "::" <+> pretty t

instance Pretty Ty where
    pretty UnitTy = "()"
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
    pretty (AlgTypingTrace rule (ctx, expr, ty)) =
      "Alg" <+> pretty rule <> hardline <> vcat
        [ "Ctx:" <+> pretty ctx
        , "Expr:" <+> pretty expr
        , "Ty:" <+> pretty ty]
    pretty (SubtypeTrace rule (ctx, t1, t2)) =
      "Sub" <+> prettyTraceTemplate rule ctx t1 t2
    pretty (InstLTrace rule (ctx, t1, t2)) =
      "InstL" <+> prettyTraceTemplate rule ctx t1 t2
    pretty (InstRTrace rule (ctx, t1, t2)) =
      "InstR" <+> prettyTraceTemplate rule ctx t1 t2

prettyTraceTemplate :: Text -> Ctx -> Ty -> Ty -> Doc ann
prettyTraceTemplate rule ctx t1 t2 =
    pretty rule <> hardline <> vcat
      [ "Ctx:" <+> pretty ctx
      , "t1:" <+> pretty t1
      , "t2:" <+> pretty t2]
