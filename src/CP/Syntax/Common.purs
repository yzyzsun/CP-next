module Language.CP.Syntax.Common where

import Prelude

type Name  = String
type Label = String

-- Kinds --

data Kind = KnStar
          | KnArr Kind Kind

instance Show Kind where
  show KnStar = "*"
  show (KnArr k1 k2) = show k1 <> " → " <> show k2

derive instance Eq Kind

-- Operators --

data UnOp = Neg | Len | Sqrt

instance Show UnOp where
  show Neg  = "-"
  show Len  = "#"
  show Sqrt = "√"

data BinOp = Arith ArithOp
           | Comp  CompOp
           | Logic LogicOp
           | Append
           | Index

data ArithOp = Add | Sub | Mul | Div | Mod
data CompOp  = Eql | Neq | Lt | Le | Gt | Ge
data LogicOp = And | Or

instance Show BinOp where
  show (Arith op) = show op
  show (Comp  op) = show op
  show (Logic op) = show op
  show Append   = "++"
  show Index    = "!!"

instance Show ArithOp where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
  show Mod = "%"

instance Show CompOp where
  show Eql = "=="
  show Neq = "!="
  show Lt  = "<"
  show Le  = "<="
  show Gt  = ">"
  show Ge  = ">="

instance Show LogicOp where
  show And = "&&"
  show Or  = "||"

derive instance Eq ArithOp

-- Helpers --

parens :: String -> String
parens str = "(" <> str <> ")"

braces :: String -> String
braces str = "{ " <> str <> " }"

angles :: String -> String
angles str = "<" <> str <> ">"

brackets :: String -> String
brackets str = "[" <> str <> "]"
