module Zord.Semantics where

import Prelude

import Control.Alt ((<|>))
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (Tuple(..))
import Math ((%))
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Zord.Subtyping (isTopLike, split, (<:))
import Zord.Syntax (ArithOp(..), BinOp(..), CompOp(..), Expr(..), LogicOp(..), Name, Ty(..), UnOp(..))
import Zord.TypeCheck (tsubst)

eval :: Expr -> Expr
eval e | isValue e = e
       | otherwise = eval $ step e

tracedEval :: Expr -> String
tracedEval e | isValue e = show e
             | otherwise = show e <> "\n↓\n" <> tracedEval (step e)

step :: Expr -> Expr
step (Unary op e) | isValue e = unop op e
                  | otherwise = Unary op (step e)
step (Binary op e1 e2) | isValue e1 && isValue e2 = binop op e1 e2
                       | isValue e1 = Binary op e1 (step e2)
                       | otherwise  = Binary op (step e1) e2
step (App e1 e2) | isValue e1 && isValue e2 = paraApp e1 e2
                 | isValue e1 = App e1 (step e2)
                 | otherwise  = App (step e1) e2
step (Fix x e t) = Anno (subst x (Fix x e t) e) t
step (Anno e t) | isValue e = unsafePartial (fromJust (typedReduce e t))
                | otherwise = Anno (step e) t
step (Merge e1 e2) | isValue e1 = Merge e1 (step e2)
                   | isValue e2 = Merge (step e1) e2
                   | otherwise  = Merge (step e1) (step e2)
step (RecLit l e) = RecLit l (step e)
step (RecPrj e l) | isValue e = paraApp' e (Rec l Top)
                  | otherwise = RecPrj (step e) l
step (If (BoolLit true)  e2 e3) = e2
step (If (BoolLit false) e2 e3) = e3
step (If e1 e2 e3) = If (step e1) e2 e3
step (Let x e1 e2) | isValue e1 = subst x e1 e2
                   | otherwise  = Let x (step e1) e2
step (Open e1 e2) | not (isValue e1) = Open (step e1) e2
                  | otherwise = open e1 e2
  where open :: Expr -> Expr -> Expr
        open (RecLit l v) e  = subst l v e
        open (Merge v1 v2) e = open v1 (open v2 e)
        open v e = unsafeCrashWith $
          "Zord.Semantics.step: impossible open " <> show v <> " in " <> show e
step e = unsafeCrashWith $
  "Zord.Semantics.step: well-typed programs don't get stuck, but got " <> show e

typedReduce :: Expr -> Ty -> Maybe Expr
typedReduce e _ | not (isValue e) = unsafeCrashWith $
  "Zord.Semantics.typedReduce: " <> show e <> " is not a value"
typedReduce _ t | isTopLike t = Just $ UnitLit
typedReduce v t | Just (Tuple t1 t2) <- split t = do
  v1 <- typedReduce v t1
  v2 <- typedReduce v t2
  Just $ Merge v1 v2
typedReduce (IntLit i)    Integer = Just $ IntLit i
typedReduce (DoubleLit n) Double  = Just $ DoubleLit n
typedReduce (StrLit s)    Str     = Just $ StrLit s
typedReduce (BoolLit b)   Bool    = Just $ BoolLit b
typedReduce (Abs x e targ1 tret1) (Arr targ2 tret2)
  | targ2 <: targ1 && tret1 <: tret2 = Just $ Abs x e targ1 tret2
typedReduce (Merge v1 v2) t = typedReduce v1 t <|> typedReduce v2 t
typedReduce (RecLit l v) (Rec l' t) | l == l' = RecLit l <$> typedReduce v t
typedReduce _ _ = Nothing

paraApp :: Expr -> Expr -> Expr
paraApp UnitLit _ = UnitLit
paraApp (Abs x e targ tret) v = Anno (subst x v' e) tret
  where v' = unsafePartial (fromJust (typedReduce v targ))
paraApp (Merge v1 v2) v = Merge (paraApp v1 v) (paraApp v2 v)
paraApp v1 v2 = unsafeCrashWith $
  "Zord.Semantics.paraApp: impossible application of " <> show v1 <> " to " <> show v2

paraApp' :: Expr -> Ty -> Expr
paraApp' (RecLit l v) (Rec l' _) | l == l' = v
paraApp' (TyAbs a td e t) ta = Anno (subst' a ta e) (tsubst a ta t)
paraApp' (Merge v1 v2) t = Merge (paraApp' v1 t) (paraApp' v2 t)
paraApp' v t = unsafeCrashWith $
  "Zord.Semantics.paraApp': impossible application of " <> show v <> " to " <> show t

isValue :: Expr -> Boolean
isValue (IntLit _)    = true
isValue (DoubleLit _) = true
isValue (StrLit _)    = true
isValue (BoolLit _)   = true
isValue (UnitLit)     = true
isValue (Abs _ _ _ _) = true
isValue (Merge e1 e2) = isValue e1 && isValue e2
isValue (RecLit _ e)  = isValue e
isValue (TyAbs _ _ _ _) = true
isValue _ = false

subst :: Name -> Expr -> Expr -> Expr
subst x v (Unary op e) = Unary op (subst x v e)
subst x v (Binary op e1 e2) = Binary op (subst x v e1) (subst x v e2)
subst x v (Var x') = if x == x' then v else Var x'
subst x v (App e1 e2) = App (subst x v e1) (subst x v e2)
subst x v (Abs x' e targ tret) =
  Abs x' (if x == x' then e else subst x v e) targ tret
subst x v (Fix x' e t) = Fix x' (if x == x' then e else subst x v e) t
subst x v (Anno e t) = Anno (subst x v e) t
subst x v (Merge e1 e2) = Merge (subst x v e1) (subst x v e2)
subst x v (RecLit l e) = RecLit l (subst x v e)
subst x v (RecPrj e l) = RecPrj (subst x v e) l
subst x v (TyApp e t) = TyApp (subst x v e) t
subst x v (TyAbs a td e t) = TyAbs a td (subst x v e) t
subst x v (If e1 e2 e3) = If (subst x v e1) (subst x v e2) (subst x v e3)
subst x v (Let x' e1 e2) = Let x' (subst x v e1) (subst x v e2)
subst x v (Open e1 e2) = Open (subst x v e1) (subst x v e2)
subst _ _ e = e

subst' :: Name -> Ty -> Expr -> Expr
subst' a s (Abs x e targ tret) = Abs x e (tsubst a s targ) (tsubst a s tret)
subst' a s (Fix x e t) = Fix x e (tsubst a s t)
subst' a s (Anno e t) = Anno e (tsubst a s t)
subst' a s (TyApp e t) = TyApp e (tsubst a s t)
subst' a s (TyAbs a' td e t) =
  TyAbs a' (tsubst a s td) e (if a == a' then t else tsubst a s t)
subst' _ _ e = e

unop :: UnOp -> Expr -> Expr
unop Neg (IntLit i)    = IntLit    (negate i)
unop Neg (DoubleLit n) = DoubleLit (negate n)
unop Not (BoolLit b)   = BoolLit   (not b)
unop op v = unsafeCrashWith $
  "Zord.Semantics.binop: impossible unary operation " <> show op <> " on " <> show v

binop :: BinOp -> Expr -> Expr -> Expr
binop (Arith Add) (IntLit i1) (IntLit i2) = IntLit (i1 + i2)
binop (Arith Sub) (IntLit i1) (IntLit i2) = IntLit (i1 - i2)
binop (Arith Mul) (IntLit i1) (IntLit i2) = IntLit (i1 * i2)
binop (Arith Div) (IntLit i1) (IntLit i2) = IntLit (i1 / i2)
binop (Arith Mod) (IntLit i1) (IntLit i2) = IntLit (i1 `mod` i2)
binop (Arith Add) (DoubleLit n1) (DoubleLit n2) = DoubleLit (n1 + n2)
binop (Arith Sub) (DoubleLit n1) (DoubleLit n2) = DoubleLit (n1 - n2)
binop (Arith Mul) (DoubleLit n1) (DoubleLit n2) = DoubleLit (n1 * n2)
binop (Arith Div) (DoubleLit n1) (DoubleLit n2) = DoubleLit (n1 / n2)
binop (Arith Mod) (DoubleLit n1) (DoubleLit n2) = DoubleLit (n1 % n2)
binop (Comp Eql) (IntLit i1) (IntLit i2) = BoolLit (i1 == i2)
binop (Comp Neq) (IntLit i1) (IntLit i2) = BoolLit (i1 /= i2)
binop (Comp Lt ) (IntLit i1) (IntLit i2) = BoolLit (i1 <  i2)
binop (Comp Le ) (IntLit i1) (IntLit i2) = BoolLit (i1 <= i2)
binop (Comp Gt ) (IntLit i1) (IntLit i2) = BoolLit (i1 >  i2)
binop (Comp Ge ) (IntLit i1) (IntLit i2) = BoolLit (i1 >= i2)
binop (Comp Eql) (DoubleLit n1) (DoubleLit n2) = BoolLit (n1 == n2)
binop (Comp Neq) (DoubleLit n1) (DoubleLit n2) = BoolLit (n1 /= n2)
binop (Comp Lt ) (DoubleLit n1) (DoubleLit n2) = BoolLit (n1 <  n2)
binop (Comp Le ) (DoubleLit n1) (DoubleLit n2) = BoolLit (n1 <= n2)
binop (Comp Gt ) (DoubleLit n1) (DoubleLit n2) = BoolLit (n1 >  n2)
binop (Comp Ge ) (DoubleLit n1) (DoubleLit n2) = BoolLit (n1 >= n2)
binop (Comp Eql) (StrLit s1) (StrLit s2) = BoolLit (s1 == s2)
binop (Comp Neq) (StrLit s1) (StrLit s2) = BoolLit (s1 /= s2)
binop (Comp Lt ) (StrLit s1) (StrLit s2) = BoolLit (s1 <  s2)
binop (Comp Le ) (StrLit s1) (StrLit s2) = BoolLit (s1 <= s2)
binop (Comp Gt ) (StrLit s1) (StrLit s2) = BoolLit (s1 >  s2)
binop (Comp Ge ) (StrLit s1) (StrLit s2) = BoolLit (s1 >= s2)
binop (Comp Eql) (BoolLit b1) (BoolLit b2) = BoolLit (b1 == b2)
binop (Comp Neq) (BoolLit b1) (BoolLit b2) = BoolLit (b1 /= b2)
binop (Comp Lt ) (BoolLit b1) (BoolLit b2) = BoolLit (b1 <  b2)
binop (Comp Le ) (BoolLit b1) (BoolLit b2) = BoolLit (b1 <= b2)
binop (Comp Gt ) (BoolLit b1) (BoolLit b2) = BoolLit (b1 >  b2)
binop (Comp Ge ) (BoolLit b1) (BoolLit b2) = BoolLit (b1 >= b2)
binop (Logic And) (BoolLit b1) (BoolLit b2) = BoolLit (b1 && b2)
binop (Logic Or ) (BoolLit b1) (BoolLit b2) = BoolLit (b1 || b2)
binop op v1 v2 = unsafeCrashWith $
  "Zord.Semantics.binop: impossible binary operation " <> show op <>
  " between " <> show v1 <> " and " <> show v2
