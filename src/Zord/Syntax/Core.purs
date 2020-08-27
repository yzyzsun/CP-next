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
        | TmRcd Label Ty Tm
        | TmPrj Tm Label
        | TmTApp Tm Ty
        | TmTAbs Name Ty Tm Ty
        | TmToString Tm

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
  show (TmRcd l t e) = "{" <+> l <+> ":" <+> show t <+> "=" <+> show e <+> "}"
  show (TmPrj e l) = show e <> "." <> l
  show (TmTApp e t) = parens $ show e <+> "@" <> show t
  show (TmTAbs a td e t) = parens $ "Λ" <> a <> "." <+> show e <+>
    ":" <+> "∀" <> a <+> "*" <+> show td <> "." <+> show t
  show (TmToString e) = parens $ "toString" <+> show e

-- Substitution --

-- TODO: capture-avoiding
tySubst :: Name -> Ty -> Ty -> Ty
tySubst a s (TyArr t1 t2 b) = TyArr (tySubst a s t1) (tySubst a s t2) b
tySubst a s (TyAnd t1 t2) = TyAnd (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyRcd l t) = TyRcd l (tySubst a s t)
tySubst a s (TyVar a') = if a == a' then s else TyVar a'
tySubst a s (TyForall a' td t) =
  TyForall a' (tySubst a s td) (if a == a' then t else tySubst a s t)
tySubst _ _ t = t

tmSubst :: Name -> Tm -> Tm -> Tm
tmSubst x v (TmUnary op e) = TmUnary op (tmSubst x v e)
tmSubst x v (TmBinary op e1 e2) = TmBinary op (tmSubst x v e1) (tmSubst x v e2)
tmSubst x v (TmIf e1 e2 e3) =
  TmIf (tmSubst x v e1) (tmSubst x v e2) (tmSubst x v e3)
tmSubst x v (TmVar x') = if x == x' then v else TmVar x'
tmSubst x v (TmApp e1 e2) = TmApp (tmSubst x v e1) (tmSubst x v e2)
tmSubst x v (TmAbs x' e targ tret) =
  TmAbs x' (if x == x' then e else tmSubst x v e) targ tret
tmSubst x v (TmFix x' e t) = TmFix x' (if x == x' then e else tmSubst x v e) t
tmSubst x v (TmAnno e t) = TmAnno (tmSubst x v e) t
tmSubst x v (TmMerge e1 e2) = TmMerge (tmSubst x v e1) (tmSubst x v e2)
tmSubst x v (TmRcd l t e) = TmRcd l t (tmSubst x v e)
tmSubst x v (TmPrj e l) = TmPrj (tmSubst x v e) l
tmSubst x v (TmTApp e t) = TmTApp (tmSubst x v e) t
tmSubst x v (TmTAbs a td e t) = TmTAbs a td (tmSubst x v e) t
tmSubst x v (TmToString e) = TmToString (tmSubst x v e)
tmSubst _ _ e = e

tmTSubst :: Name -> Ty -> Tm -> Tm
tmTSubst a s (TmUnary op e) = TmUnary op (tmTSubst a s e)
tmTSubst a s (TmBinary op e1 e2) =
  TmBinary op (tmTSubst a s e1) (tmTSubst a s e2)
tmTSubst a s (TmIf e1 e2 e3) =
  TmIf (tmTSubst a s e1) (tmTSubst a s e2) (tmTSubst a s e3)
tmTSubst a s (TmApp e1 e2) = TmApp (tmTSubst a s e1) (tmTSubst a s e2)
tmTSubst a s (TmAbs x e targ tret) =
  TmAbs x (tmTSubst a s e) (tySubst a s targ) (tySubst a s tret)
tmTSubst a s (TmFix x e t) = TmFix x (tmTSubst a s e) (tySubst a s t)
tmTSubst a s (TmAnno e t) = TmAnno (tmTSubst a s e) (tySubst a s t)
tmTSubst a s (TmMerge e1 e2) = TmMerge (tmTSubst a s e1) (tmTSubst a s e2)
tmTSubst a s (TmRcd l t e) = TmRcd l (tySubst a s t) (tmTSubst a s e)
tmTSubst a s (TmPrj e l) = TmPrj (tmTSubst a s e) l
tmTSubst a s (TmTApp e t) = TmTApp (tmTSubst a s e) (tySubst a s t)
tmTSubst a s (TmTAbs a' td e t) = TmTAbs a' (tySubst a s td) (tmTSubst a s e)
                                  (if a == a' then t else tySubst a s t)
tmTSubst a s (TmToString e) = TmToString (tmTSubst a s e)
tmTSubst _ _ e = e
