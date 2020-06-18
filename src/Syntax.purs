module Zord.Syntax where

type Name = String

data Expr = IntLit Int
          | DoubleLit Number
          | StrLit String
          | BoolLit Boolean
          | UnitLit
          | Unary UnOp Expr
          | Binary BinOp Expr Expr
          | Var Name
          | Abs Name Ty Expr
          | App Expr Expr
          | Anno Expr Ty

data UnOp = Neg | Not

data BinOp = Add | Sub | Mul | Div | Mod    -- Arithmetic
           | Eql | Neq | Lt | Le | Gt | Ge  -- Comparison
           | And | Or                       -- Logical

data Ty = Integer
        | Double
        | Str
        | Bool
        | Top
        | Bot
        | Arr Ty Ty
