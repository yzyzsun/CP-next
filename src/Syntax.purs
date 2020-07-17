module Zord.Syntax where

import Prelude

import Data.List (List)
import Data.Tuple (Tuple)

type Name  = String
type Label = String

-- Context --

type Ctx = List (Tuple Name Binding)

data Binding = TermBinding Ty -- typing
             | TypeBinding Ty -- disjointness

-- Types --

data Ty = Integer
        | Double
        | Str
        | Bool
        | Top
        | Bot
        | Arr Ty Ty
        | Intersect Ty Ty
        | Rec Label Ty
        | TyVar Name
        | Forall Name Ty Ty

instance showTy :: Show Ty where
  show Integer = "Int"
  show Double  = "Double"
  show Str     = "String"
  show Bool    = "Bool"
  show Top     = "Top"
  show Bot     = "Bot"
  show (Arr t1 t2) = parens $ show t1 <+> "->" <+> show t2
  show (Intersect t1 t2) = show t1 <+> "&" <+> show t2
  show (Rec l t) = "{" <+> l <+> ":" <+> show t <+> "}"
  show (TyVar a) = a
  show (Forall a td t) = parens $
    "∀" <> a <+> "*" <+> show td <> "." <+> show t

derive instance eqTy :: Eq Ty

-- Expressions --

data Expr = IntLit Int
          | DoubleLit Number
          | StrLit String
          | BoolLit Boolean
          | UnitLit
          | Unary UnOp Expr
          | Binary BinOp Expr Expr
          | Var Name
          | App Expr Expr
          | Abs Name Expr Ty Ty
          | Fix Name Expr Ty
          | Anno Expr Ty
          | Merge Expr Expr
          | RecLit Label Expr
          | RecPrj Expr Label
          | TyApp Expr Ty
          | TyAbs Name Ty Expr Ty
          | If Expr Expr Expr
          | Let Name Expr Expr
          | Open Expr Expr

instance showExpr :: Show Expr where
  show (IntLit i)    = show i
  show (DoubleLit n) = show n
  show (StrLit s)    = show s
  show (BoolLit b)   = show b
  show (UnitLit)     = "()"
  show (Unary op e)  = show op <> show e
  show (Binary op e1 e2) = parens $ show e1 <+> show op <+> show e2
  show (Var x) = x
  show (App e1 e2) = parens $ show e1 <+> show e2
  show (Abs x e targ tret) = parens $
    "λ" <> x <> "." <+> show e <+> ":" <+> show targ <+> "->" <+> show tret
  show (Fix x e t) = parens $ "fix" <+> x <> "." <+> show e <+> ":" <+> show t
  show (Anno e t)  = parens $ show e <+> ":" <+> show t
  show (Merge e1 e2) = parens $ show e1 <+> ",," <+> show e2
  show (RecLit l e) = "{" <+> l <+> "=" <+> show e <+> "}"
  show (RecPrj e l) = show e <> "." <> l
  show (TyApp e t) = parens $ show e <+> "@" <> show t
  show (TyAbs a td e t) = parens $
    "Λ" <> a <+> "*" <+> show td <> "." <+> show e <+> ":" <+> show t
  show (If e1 e2 e3) = parens $
    "if" <+> show e1 <+> "then" <+> show e2 <+> "else" <+> show e3
  show (Let x e1 e2) = parens $
    "let" <+> x <+> "=" <+> show e1 <+> "in" <+> show e2
  show (Open e1 e2) = parens $ "open" <+> show e1 <+> "in" <+> show e2

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
