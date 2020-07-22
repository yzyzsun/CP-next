module Zord.Semantics where

import Prelude

import Control.Alt ((<|>))
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (Tuple(..))
import Math ((%))
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Zord.Kinding (tyBReduce, tySubst)
import Zord.Subtyping (isTopLike, split, (<:))
import Zord.Syntax (ArithOp(..), BinOp(..), CompOp(..), Expr(..), LogicOp(..), Name, Ty(..), UnOp(..), stripPos)

eval :: Expr -> Expr
eval e | isValue e = e
       | otherwise = eval $ step e

tracedEval :: Expr -> String
tracedEval = stripPos >>> trace
  where trace :: Expr -> String
        trace e | isValue e = show e
                | otherwise = show e <> "\n↓\n" <> trace (step e)

step :: Expr -> Expr
step (TmUnary op e) | isValue e = unop op e
                    | otherwise = TmUnary op (step e)
step (TmBinary op e1 e2) | isValue e1 && isValue e2 = binop op e1 e2
                         | isValue e1 = TmBinary op e1 (step e2)
                         | otherwise  = TmBinary op (step e1) e2
step (TmApp e1 e2) | isValue e1 && isValue e2 = paraApp e1 e2
                   | isValue e1 = TmApp e1 (step e2)
                   | otherwise  = TmApp (step e1) e2
step (TmFix x e t) = TmAnno (tmSubst x (TmFix x e t) e) t
step (TmAnno e t)
  -- TODO: do type-level beta-reduction elsewhere
  | isValue e = unsafePartial (fromJust (typedReduce e (tyBReduce t)))
  | otherwise = TmAnno (step e) t
step (TmMerge e1 e2) | isValue e1 = TmMerge e1 (step e2)
                     | isValue e2 = TmMerge (step e1) e2
                     | otherwise  = TmMerge (step e1) (step e2)
step (TmRec l e) = TmRec l (step e)
step (TmPrj e l) | isValue e = paraApp' e (TyRec l TyTop)
                 | otherwise = TmPrj (step e) l
step (TmTApp e t) | isValue e = paraApp' e t
                  | otherwise = TmTApp (step e) t
step (TmIf (TmBool true)  e2 e3) = e2
step (TmIf (TmBool false) e2 e3) = e3
step (TmIf e1 e2 e3) = TmIf (step e1) e2 e3
step (TmLet x e1 e2) | isValue e1 = tmSubst x e1 e2
                     | otherwise  = TmLet x (step e1) e2
step (TmOpen e1 e2) | not (isValue e1) = TmOpen (step e1) e2
                    | otherwise = open e1 e2
  where open :: Expr -> Expr -> Expr
        open (TmRec l v) e  = tmSubst l v e
        open (TmMerge v1 v2) e = open v1 (open v2 e)
        open v e = unsafeCrashWith $
          "Zord.Semantics.step: impossible open " <> show v <> " in " <> show e
step (TmPos _ e) = e
step e = unsafeCrashWith $
  "Zord.Semantics.step: well-typed programs don't get stuck, but got " <> show e

typedReduce :: Expr -> Ty -> Maybe Expr
typedReduce e _ | not (isValue e) = unsafeCrashWith $
  "Zord.Semantics.typedReduce: " <> show e <> " is not a value"
typedReduce _ t | isTopLike t = Just $ TmUnit
typedReduce v t | Just (Tuple t1 t2) <- split t = do
  v1 <- typedReduce v t1
  v2 <- typedReduce v t2
  Just $ TmMerge v1 v2
typedReduce (TmInt i)    TyInt    = Just $ TmInt i
typedReduce (TmDouble n) TyDouble = Just $ TmDouble n
typedReduce (TmString s) TyString = Just $ TmString s
typedReduce (TmBool b)   TyBool   = Just $ TmBool b
typedReduce (TmAbs x e targ1 tret1) (TyArr targ2 tret2)
  | targ2 <: targ1 && tret1 <: tret2 = Just $ TmAbs x e targ1 tret2
typedReduce (TmMerge v1 v2) t = typedReduce v1 t <|> typedReduce v2 t
typedReduce (TmRec l v) (TyRec l' t) | l == l' = TmRec l <$> typedReduce v t
typedReduce _ _ = Nothing

paraApp :: Expr -> Expr -> Expr
paraApp TmUnit _ = TmUnit
paraApp (TmAbs x e targ tret) v = TmAnno (tmSubst x v' e) tret
  where v' = unsafePartial (fromJust (typedReduce v targ))
paraApp (TmMerge v1 v2) v = TmMerge (paraApp v1 v) (paraApp v2 v)
paraApp v1 v2 = unsafeCrashWith $
  "Zord.Semantics.paraApp: impossible application of " <> show v1 <> " to " <> show v2

paraApp' :: Expr -> Ty -> Expr
paraApp' (TmRec l v) (TyRec l' _) | l == l' = v
paraApp' (TmTAbs a td e t) ta = TmAnno (tmTSubst a ta e) (tySubst a ta t)
paraApp' (TmMerge v1 v2) t = TmMerge (paraApp' v1 t) (paraApp' v2 t)
paraApp' v t = unsafeCrashWith $
  "Zord.Semantics.paraApp': impossible application of " <> show v <> " to " <> show t

isValue :: Expr -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue (TmUnit)     = true
isValue (TmAbs _ _ _ _) = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmRec _ e)  = isValue e
isValue (TmTAbs _ _ _ _) = true
isValue _ = false

tmSubst :: Name -> Expr -> Expr -> Expr
tmSubst x v (TmUnary op e) = TmUnary op (tmSubst x v e)
tmSubst x v (TmBinary op e1 e2) = TmBinary op (tmSubst x v e1) (tmSubst x v e2)
tmSubst x v (TmVar x') = if x == x' then v else TmVar x'
tmSubst x v (TmApp e1 e2) = TmApp (tmSubst x v e1) (tmSubst x v e2)
tmSubst x v (TmAbs x' e targ tret) =
  TmAbs x' (if x == x' then e else tmSubst x v e) targ tret
tmSubst x v (TmFix x' e t) = TmFix x' (if x == x' then e else tmSubst x v e) t
tmSubst x v (TmAnno e t) = TmAnno (tmSubst x v e) t
tmSubst x v (TmMerge e1 e2) = TmMerge (tmSubst x v e1) (tmSubst x v e2)
tmSubst x v (TmRec l e) = TmRec l (tmSubst x v e)
tmSubst x v (TmPrj e l) = TmPrj (tmSubst x v e) l
tmSubst x v (TmTApp e t) = TmTApp (tmSubst x v e) t
tmSubst x v (TmTAbs a td e t) = TmTAbs a td (tmSubst x v e) t
tmSubst x v (TmIf e1 e2 e3) =
  TmIf (tmSubst x v e1) (tmSubst x v e2) (tmSubst x v e3)
tmSubst x v (TmLet x' e1 e2) = TmLet x' (tmSubst x v e1) (tmSubst x v e2)
tmSubst x v (TmOpen e1 e2) = TmOpen (tmSubst x v e1) (tmSubst x v e2)
tmSubst x v (TmPos p e) = TmPos p (tmSubst x v e)
tmSubst _ _ e = e

tmTSubst :: Name -> Ty -> Expr -> Expr
tmTSubst a s (TmAbs x e targ tret) =
  TmAbs x e (tySubst a s targ) (tySubst a s tret)
tmTSubst a s (TmFix x e t) = TmFix x e (tySubst a s t)
tmTSubst a s (TmAnno e t) = TmAnno e (tySubst a s t)
tmTSubst a s (TmTApp e t) = TmTApp e (tySubst a s t)
tmTSubst a s (TmTAbs a' td e t) =
  TmTAbs a' (tySubst a s td) e (if a == a' then t else tySubst a s t)
tmTSubst _ _ e = e

unop :: UnOp -> Expr -> Expr
unop Neg (TmInt i)    = TmInt    (negate i)
unop Neg (TmDouble n) = TmDouble (negate n)
unop Not (TmBool b)   = TmBool   (not b)
unop op v = unsafeCrashWith $
  "Zord.Semantics.binop: impossible unary operation " <> show op <> " on " <> show v

binop :: BinOp -> Expr -> Expr -> Expr
binop (Arith Add) (TmInt i1) (TmInt i2) = TmInt (i1 + i2)
binop (Arith Sub) (TmInt i1) (TmInt i2) = TmInt (i1 - i2)
binop (Arith Mul) (TmInt i1) (TmInt i2) = TmInt (i1 * i2)
binop (Arith Div) (TmInt i1) (TmInt i2) = TmInt (i1 / i2)
binop (Arith Mod) (TmInt i1) (TmInt i2) = TmInt (i1 `mod` i2)
binop (Arith Add) (TmDouble n1) (TmDouble n2) = TmDouble (n1 + n2)
binop (Arith Sub) (TmDouble n1) (TmDouble n2) = TmDouble (n1 - n2)
binop (Arith Mul) (TmDouble n1) (TmDouble n2) = TmDouble (n1 * n2)
binop (Arith Div) (TmDouble n1) (TmDouble n2) = TmDouble (n1 / n2)
binop (Arith Mod) (TmDouble n1) (TmDouble n2) = TmDouble (n1 % n2)
binop (Comp Eql) (TmInt i1) (TmInt i2) = TmBool (i1 == i2)
binop (Comp Neq) (TmInt i1) (TmInt i2) = TmBool (i1 /= i2)
binop (Comp Lt ) (TmInt i1) (TmInt i2) = TmBool (i1 <  i2)
binop (Comp Le ) (TmInt i1) (TmInt i2) = TmBool (i1 <= i2)
binop (Comp Gt ) (TmInt i1) (TmInt i2) = TmBool (i1 >  i2)
binop (Comp Ge ) (TmInt i1) (TmInt i2) = TmBool (i1 >= i2)
binop (Comp Eql) (TmDouble n1) (TmDouble n2) = TmBool (n1 == n2)
binop (Comp Neq) (TmDouble n1) (TmDouble n2) = TmBool (n1 /= n2)
binop (Comp Lt ) (TmDouble n1) (TmDouble n2) = TmBool (n1 <  n2)
binop (Comp Le ) (TmDouble n1) (TmDouble n2) = TmBool (n1 <= n2)
binop (Comp Gt ) (TmDouble n1) (TmDouble n2) = TmBool (n1 >  n2)
binop (Comp Ge ) (TmDouble n1) (TmDouble n2) = TmBool (n1 >= n2)
binop (Comp Eql) (TmString s1) (TmString s2) = TmBool (s1 == s2)
binop (Comp Neq) (TmString s1) (TmString s2) = TmBool (s1 /= s2)
binop (Comp Lt ) (TmString s1) (TmString s2) = TmBool (s1 <  s2)
binop (Comp Le ) (TmString s1) (TmString s2) = TmBool (s1 <= s2)
binop (Comp Gt ) (TmString s1) (TmString s2) = TmBool (s1 >  s2)
binop (Comp Ge ) (TmString s1) (TmString s2) = TmBool (s1 >= s2)
binop (Comp Eql) (TmBool b1) (TmBool b2) = TmBool (b1 == b2)
binop (Comp Neq) (TmBool b1) (TmBool b2) = TmBool (b1 /= b2)
binop (Comp Lt ) (TmBool b1) (TmBool b2) = TmBool (b1 <  b2)
binop (Comp Le ) (TmBool b1) (TmBool b2) = TmBool (b1 <= b2)
binop (Comp Gt ) (TmBool b1) (TmBool b2) = TmBool (b1 >  b2)
binop (Comp Ge ) (TmBool b1) (TmBool b2) = TmBool (b1 >= b2)
binop (Logic And) (TmBool b1) (TmBool b2) = TmBool (b1 && b2)
binop (Logic Or ) (TmBool b1) (TmBool b2) = TmBool (b1 || b2)
binop op v1 v2 = unsafeCrashWith $
  "Zord.Semantics.binop: impossible binary operation " <> show op <>
  " between " <> show v1 <> " and " <> show v2
