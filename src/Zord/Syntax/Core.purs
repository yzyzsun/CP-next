module Zord.Syntax.Core where

import Prelude

import Text.Parsing.Parser.Pos (Position)

type Name  = String
type Label = String

-- Kinds --

data Kind = KnStar
          | KnArr Kind Kind

instance showKind :: Show Kind where
  show KnStar = "star"
  show (KnArr k1 k2) = parens $ show k1 <+> "->" <+> show k2

derive instance eqKind :: Eq Kind

-- Types --

data Ty = TyInt
        | TyDouble
        | TyString
        | TyBool
        | TyTop
        | TyBot
        | TyArr Ty Ty
        | TyAnd Ty Ty
        | TyRec Label Ty
        | TyVar Name
        | TyForall Name Ty Ty
        | TyApp Ty Ty
        | TyAbs Name Ty

instance showTy :: Show Ty where
  show TyInt    = "Int"
  show TyDouble = "Double"
  show TyString = "String"
  show TyBool   = "Bool"
  show TyTop    = "Top"
  show TyBot    = "Bot"
  show (TyArr t1 t2) = parens $ show t1 <+> "->" <+> show t2
  show (TyAnd t1 t2) = show t1 <+> "&" <+> show t2
  show (TyRec l t) = "{" <+> l <+> ":" <+> show t <+> "}"
  show (TyVar a) = a
  show (TyForall a td t) = parens $
    "∀" <> a <+> "*" <+> show td <> "." <+> show t
  show (TyApp t1 t2) = parens $ show t1 <+> show t2
  show (TyAbs a t) = parens $ "λ" <> a <> "." <+> show t

derive instance eqTy :: Eq Ty

-- Expressions --

data Expr = TmInt Int
          | TmDouble Number
          | TmString String
          | TmBool Boolean
          | TmUnit
          | TmUnary UnOp Expr
          | TmBinary BinOp Expr Expr
          | TmVar Name
          | TmApp Expr Expr
          | TmAbs Name Expr Ty Ty
          | TmFix Name Expr Ty
          | TmAnno Expr Ty
          | TmMerge Expr Expr
          | TmRec Label Expr
          | TmPrj Expr Label
          | TmTApp Expr Ty
          | TmTAbs Name Ty Expr Ty
          | TmIf Expr Expr Expr
          | TmLet Name Expr Expr
          | TmOpen Expr Expr
          | TmPos Position Expr

instance showExpr :: Show Expr where
  show (TmInt i)    = show i
  show (TmDouble n) = show n
  show (TmString s) = show s
  show (TmBool b)   = show b
  show (TmUnit)     = "()"
  show (TmUnary op e)  = show op <> show e
  show (TmBinary op e1 e2) = parens $ show e1 <+> show op <+> show e2
  show (TmVar x) = x
  show (TmApp e1 e2) = parens $ show e1 <+> show e2
  show (TmAbs x e targ tret) = parens $
    "λ" <> x <> "." <+> show e <+> ":" <+> show targ <+> "->" <+> show tret
  show (TmFix x e t) = parens $ "fix" <+> x <> "." <+> show e <+> ":" <+> show t
  show (TmAnno e t)  = parens $ show e <+> ":" <+> show t
  show (TmMerge e1 e2) = parens $ show e1 <+> "," <+> show e2
  show (TmRec l e) = "{" <+> l <+> "=" <+> show e <+> "}"
  show (TmPrj e l) = show e <> "." <> l
  show (TmTApp e t) = parens $ show e <+> "@" <> show t
  show (TmTAbs a td e t) = parens $
    "Λ" <> a <+> "*" <+> show td <> "." <+> show e <+> ":" <+> show t
  show (TmIf e1 e2 e3) = parens $
    "if" <+> show e1 <+> "then" <+> show e2 <+> "else" <+> show e3
  show (TmLet x e1 e2) = parens $
    "let" <+> x <+> "=" <+> show e1 <+> "in" <+> show e2
  show (TmOpen e1 e2) = parens $ "open" <+> show e1 <+> "in" <+> show e2
  show (TmPos p e) = show e

stripPos :: Expr -> Expr
stripPos (TmUnary op e) = TmUnary op (stripPos e)
stripPos (TmBinary op e1 e2) = TmBinary op (stripPos e1) (stripPos e2)
stripPos (TmApp e1 e2) = TmApp (stripPos e1) (stripPos e2)
stripPos (TmAbs x e targ tret) = TmAbs x (stripPos e) targ tret
stripPos (TmFix x e t) = TmFix x (stripPos e) t
stripPos (TmAnno e t) = TmAnno (stripPos e) t
stripPos (TmMerge e1 e2) = TmMerge (stripPos e1) (stripPos e2)
stripPos (TmRec l e) = TmRec l (stripPos e)
stripPos (TmPrj e l) = TmPrj (stripPos e) l
stripPos (TmTApp e t) = TmTApp (stripPos e) t
stripPos (TmTAbs a td e t) = TmTAbs a td (stripPos e) t
stripPos (TmIf e1 e2 e3) = TmIf (stripPos e1) (stripPos e2) (stripPos e3)
stripPos (TmLet x e1 e2) = TmLet x (stripPos e1) (stripPos e2)
stripPos (TmOpen e1 e2) = TmOpen (stripPos e1) (stripPos e2)
stripPos (TmPos _ e) = stripPos e
stripPos e = e

-- Operators --

data UnOp = Neg | Not

instance showUnOp :: Show UnOp where
  show Neg = "-"
  show Not = "!"

data BinOp = Arith ArithOp
           | Comp  CompOp
           | Logic LogicOp
data ArithOp = Add | Sub | Mul | Div | Mod
data CompOp  = Eql | Neq | Lt | Le | Gt | Ge
data LogicOp = And | Or

instance showBinOp :: Show BinOp where
  show (Arith op) = show op
  show (Comp  op) = show op
  show (Logic op) = show op

instance showArithOp :: Show ArithOp where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
  show Mod = "%"

instance showCompOp :: Show CompOp where
  show Eql = "=="
  show Neq = "!="
  show Lt  = "<"
  show Le  = "<="
  show Gt  = ">"
  show Ge  = ">="

instance showLogicOp :: Show LogicOp where
  show And = "&&"
  show Or  = "||"

-- Helpers --

parens :: String -> String
parens str = "(" <> str <> ")"

beside :: String -> String -> String
beside s1 s2 = s1 <> " " <> s2

infixr 5 beside as <+>
