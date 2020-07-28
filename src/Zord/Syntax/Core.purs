module Zord.Syntax.Core where

import Prelude

import Zord.Syntax.Common (BinOp, Label, Name, UnOp, parens, (<+>))

-- Types --

data Ty = TyInt
        | TyDouble
        | TyString
        | TyBool
        | TyTop
        | TyBot
        | TyArr Ty Ty Boolean
        | TyAnd Ty Ty
        | TyRcd Label Ty
        | TyVar Name
        | TyForall Name Ty Ty
        | TyApp Ty Ty
        | TyAbs Name Ty

instance showTy :: Show Ty where
  show TyInt    = "Int"
  show TyDouble = "Double"
  show TyString = "String"
  show TyBool   = "Bool"
  show TyTop    = "⊤"
  show TyBot    = "⊥"
  show (TyArr t1 t2 isTrait) = parens $ show t1 <+> "→" <+> show t2
  show (TyAnd t1 t2) = show t1 <+> "&" <+> show t2
  show (TyRcd l t) = "{" <+> l <+> ":" <+> show t <+> "}"
  show (TyVar a) = a
  show (TyForall a td t) = parens $
    "∀" <> a <+> "*" <+> show td <> "." <+> show t
  show (TyApp t1 t2) = parens $ show t1 <+> show t2
  show (TyAbs a t) = parens $ "λ" <> a <> "." <+> show t

derive instance eqTy :: Eq Ty

-- Terms --

data Tm = TmInt Int
        | TmDouble Number
        | TmString String
        | TmBool Boolean
        | TmUnit
        | TmUnary UnOp Tm
        | TmBinary BinOp Tm Tm
        | TmIf Tm Tm Tm
        | TmVar Name
        | TmApp Tm Tm
        | TmAbs Name Tm Ty Ty
        | TmFix Name Tm Ty
        | TmAnno Tm Ty
        | TmMerge Tm Tm
        | TmRcd Label Tm
        | TmPrj Tm Label
        | TmTApp Tm Ty
        | TmTAbs Name Ty Tm Ty

instance showTm :: Show Tm where
  show (TmInt i)    = show i
  show (TmDouble n) = show n
  show (TmString s) = show s
  show (TmBool b)   = show b
  show (TmUnit)     = "()"
  show (TmUnary op e) = show op <> show e
  show (TmBinary op e1 e2) = parens $ show e1 <+> show op <+> show e2
  show (TmIf e1 e2 e3) = parens $
    "if" <+> show e1 <+> "then" <+> show e2 <+> "else" <+> show e3
  show (TmVar x) = x
  show (TmApp e1 e2) = parens $ show e1 <+> show e2
  show (TmAbs x e targ tret) = parens $
    "λ" <> x <> "." <+> show e <+> ":" <+> show targ <+> "→" <+> show tret
  show (TmFix x e t) = parens $ "fix" <+> x <> "." <+> show e <+> ":" <+> show t
  show (TmAnno e t) = parens $ show e <+> ":" <+> show t
  show (TmMerge e1 e2) = parens $ show e1 <+> "," <+> show e2
  show (TmRcd l e) = "{" <+> l <+> "=" <+> show e <+> "}"
  show (TmPrj e l) = show e <> "." <> l
  show (TmTApp e t) = parens $ show e <+> "@" <> show t
  show (TmTAbs a td e t) = parens $ "Λ" <> a <> "." <+> show e <+>
    ":" <+> "∀" <> a <+> "*" <+> show td <> "." <+> show t
