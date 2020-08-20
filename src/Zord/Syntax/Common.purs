module Zord.Syntax.Common where

import Prelude

import Data.List (List(..), foldl)
import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafeCrashWith)

type Name  = String
type Label = String

-- Kinds --

data Kind = KnStar
          | KnArr Kind Kind

instance showKind :: Show Kind where
  show KnStar = "*"
  show (KnArr k1 k2) = show k1 <+> "→" <+> show k2

derive instance eqKind :: Eq Kind

-- Operators --

data UnOp = Neg | Not

instance showUnOp :: Show UnOp where
  show Neg = "-"
  show Not = "!"

data BinOp = Arith ArithOp
           | Comp  CompOp
           | Logic LogicOp
           | Append

data ArithOp = Add | Sub | Mul | Div | Mod
data CompOp  = Eql | Neq | Lt | Le | Gt | Ge
data LogicOp = And | Or

instance showBinOp :: Show BinOp where
  show (Arith op) = show op
  show (Comp  op) = show op
  show (Logic op) = show op
  show Append = "++"

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

beside :: String -> String -> String
beside s1 s2 = s1 <> " " <> s2

infixr 5 beside as <+>

parens :: String -> String
parens str = "(" <> str <> ")"

braces :: String -> String
braces str = "{" <+> str <+> "}"

angles :: String -> String
angles str = "<" <> str <> ">"

brackets :: String -> String
brackets str = "[" <+> str <+> "]"

foldl1 :: forall a. (a -> a -> a) -> List a -> a
foldl1 _ Nil = unsafeCrashWith "foldl1: empty list"
foldl1 f (Cons x xs) = foldl f x xs

fromJust :: forall a. Maybe a -> a
fromJust (Just x) = x
fromJust Nothing = unsafeCrashWith "fromJust: unexpected Nothing"
