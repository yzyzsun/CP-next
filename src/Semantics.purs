module Zord.Semantics where

import Prelude

import Math ((%))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Syntax (ArithOp(..), BinOp(..), CompOp(..), Expr(..), LogicOp(..), Name, UnOp(..))

eval :: Expr -> Expr
eval e | isValue e = e
       | otherwise = eval $ step e

step :: Expr -> Expr
step (Unary Neg (IntLit i))    = IntLit    (negate i)
step (Unary Neg (DoubleLit n)) = DoubleLit (negate n)
step (Unary Not (BoolLit b))   = BoolLit   (not b)
step (Unary op e) = Unary op (step e)
step (Binary (Arith Add) (IntLit i1) (IntLit i2)) = IntLit (i1 + i2)
step (Binary (Arith Sub) (IntLit i1) (IntLit i2)) = IntLit (i1 - i2)
step (Binary (Arith Mul) (IntLit i1) (IntLit i2)) = IntLit (i1 * i2)
step (Binary (Arith Div) (IntLit i1) (IntLit i2)) = IntLit (i1 / i2)
step (Binary (Arith Mod) (IntLit i1) (IntLit i2)) = IntLit (i1 `mod` i2)
step (Binary (Arith Add) (DoubleLit n1) (DoubleLit n2)) = DoubleLit (n1 + n2)
step (Binary (Arith Sub) (DoubleLit n1) (DoubleLit n2)) = DoubleLit (n1 - n2)
step (Binary (Arith Mul) (DoubleLit n1) (DoubleLit n2)) = DoubleLit (n1 * n2)
step (Binary (Arith Div) (DoubleLit n1) (DoubleLit n2)) = DoubleLit (n1 / n2)
step (Binary (Arith Mod) (DoubleLit n1) (DoubleLit n2)) = DoubleLit (n1 % n2)
step (Binary (Comp Eql) (IntLit i1) (IntLit i2)) = BoolLit (i1 == i2)
step (Binary (Comp Neq) (IntLit i1) (IntLit i2)) = BoolLit (i1 /= i2)
step (Binary (Comp Lt ) (IntLit i1) (IntLit i2)) = BoolLit (i1 <  i2)
step (Binary (Comp Le ) (IntLit i1) (IntLit i2)) = BoolLit (i1 <= i2)
step (Binary (Comp Gt ) (IntLit i1) (IntLit i2)) = BoolLit (i1 >  i2)
step (Binary (Comp Ge ) (IntLit i1) (IntLit i2)) = BoolLit (i1 >= i2)
step (Binary (Comp Eql) (DoubleLit n1) (DoubleLit n2)) = BoolLit (n1 == n2)
step (Binary (Comp Neq) (DoubleLit n1) (DoubleLit n2)) = BoolLit (n1 /= n2)
step (Binary (Comp Lt ) (DoubleLit n1) (DoubleLit n2)) = BoolLit (n1 <  n2)
step (Binary (Comp Le ) (DoubleLit n1) (DoubleLit n2)) = BoolLit (n1 <= n2)
step (Binary (Comp Gt ) (DoubleLit n1) (DoubleLit n2)) = BoolLit (n1 >  n2)
step (Binary (Comp Ge ) (DoubleLit n1) (DoubleLit n2)) = BoolLit (n1 >= n2)
step (Binary (Comp Eql) (StrLit s1) (StrLit s2)) = BoolLit (s1 == s2)
step (Binary (Comp Neq) (StrLit s1) (StrLit s2)) = BoolLit (s1 /= s2)
step (Binary (Comp Lt ) (StrLit s1) (StrLit s2)) = BoolLit (s1 <  s2)
step (Binary (Comp Le ) (StrLit s1) (StrLit s2)) = BoolLit (s1 <= s2)
step (Binary (Comp Gt ) (StrLit s1) (StrLit s2)) = BoolLit (s1 >  s2)
step (Binary (Comp Ge ) (StrLit s1) (StrLit s2)) = BoolLit (s1 >= s2)
step (Binary (Comp Eql) (BoolLit b1) (BoolLit b2)) = BoolLit (b1 == b2)
step (Binary (Comp Neq) (BoolLit b1) (BoolLit b2)) = BoolLit (b1 /= b2)
step (Binary (Comp Lt ) (BoolLit b1) (BoolLit b2)) = BoolLit (b1 <  b2)
step (Binary (Comp Le ) (BoolLit b1) (BoolLit b2)) = BoolLit (b1 <= b2)
step (Binary (Comp Gt ) (BoolLit b1) (BoolLit b2)) = BoolLit (b1 >  b2)
step (Binary (Comp Ge ) (BoolLit b1) (BoolLit b2)) = BoolLit (b1 >= b2)
step (Binary (Logic And) (BoolLit b1) (BoolLit b2)) = BoolLit (b1 && b2)
step (Binary (Logic Or ) (BoolLit b1) (BoolLit b2)) = BoolLit (b1 || b2)
step (Binary op e1 e2) | isValue e1 = Binary op e1 (step e2)
                       | otherwise  = Binary op (step e1) e2
step (App (Abs x _ e) v) = subst x v e
step (App e1 e2) | isValue e1 = App e1 (step e2)
                 | otherwise  = App (step e1) e2
step (Anno e t) = e
step e = unsafeCrashWith $
  "Zord.Semantics.step: well-typed programs don't get stuck, but got " <> show e

isValue :: Expr -> Boolean
isValue (IntLit _)    = true
isValue (DoubleLit _) = true
isValue (StrLit _)    = true
isValue (BoolLit _)   = true
isValue (UnitLit)     = true
isValue (Abs _ _ _)   = true
isValue _ = false

subst :: Name -> Expr -> Expr -> Expr
subst x v (Unary op e) = Unary op (subst x v e)
subst x v (Binary op e1 e2) = Binary op (subst x v e1) (subst x v e2)
subst x v (Var x') = if x == x' then v else Var x'
subst x v (Abs x' t e) = Abs x' t (if x == x' then e else subst x v e)
subst x v (App e1 e2) = App (subst x v e1) (subst x v e2)
subst x v (Anno e t) = Anno (subst x v e) t
subst _ _ e = e
