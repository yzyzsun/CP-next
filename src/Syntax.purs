module Zord.Syntax where

import Prelude

import Data.List (List)
import Data.Tuple (Tuple)

type Name = String

type Ctx = List (Tuple Name Ty)

-- Types --

data Ty = Integer
        | Double
        | Str
        | Bool
        | Top
        | Bot
        | Arr Ty Ty
        | Intersect Ty Ty

instance showTy :: Show Ty where
  show Integer = "Int"
  show Double  = "Double"
  show Str     = "String"
  show Bool    = "Bool"
  show Top     = "Top"
  show Bot     = "Bot"
  show (Arr t1 t2) = parens $ show t1 <+> "->" <+> show t2
  show (Intersect t1 t2) = show t1 <+> "&" <+> show t2

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
    "λ" <> x <> ". " <> show e <+> ":" <+> show targ <+> "->" <+> show tret
  show (Fix x e t) = parens $ "μ" <> x <> ". " <> show e <+> ":" <+> show t
  show (Anno e t)  = parens $ show e <+> ":" <+> show t
  show (Merge e1 e2) = parens $ show e1 <+> ",," <+> show e2

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
