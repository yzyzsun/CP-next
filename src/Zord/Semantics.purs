module Zord.Semantics where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Writer (Writer, runWriter, tell)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math ((%))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Kinding (tyBReduce, tySubst)
import Zord.Subtyping (isTopLike, split, (<:))
import Zord.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), LogicOp(..), Name, UnOp(..), fromJust)
import Zord.Syntax.Core (Tm(..), Ty(..))

type Eval a = Writer String a

runEval :: forall a. Eval a -> Tuple a String
runEval = runWriter

computation :: String -> Eval Unit
computation w = tell $ "↓ Step-" <> w <> "\n"

congruence :: String -> Eval Unit
congruence w = tell $ "→ Step-" <> w <> "\n"

eval :: Tm -> Eval Tm
eval e | isValue e = tell (show e <> "\n") $> e
       | otherwise = tell (show e <> "\n") *> step e >>= eval

step :: Tm -> Eval Tm
step (TmUnary op e) | isValue e = computation "UnaryV" $> unop op e
                    | otherwise = congruence "Unary" $> TmUnary op <*> step e
step (TmBinary op e1 e2) | isValue e1 && isValue e2 = computation "BinaryV" $> binop op e1 e2
                         | isValue e1 = congruence "BinaryR" $> TmBinary op e1 <*> step e2
                         | otherwise  = congruence "BinaryL" $> TmBinary op <*> step e1 <@> e2
step (TmIf (TmBool true)  e2 e3) = computation "IfTrue"  $> e2
step (TmIf (TmBool false) e2 e3) = computation "IfFalse" $> e3
step (TmIf e1 e2 e3) = congruence "If" $> TmIf <*> step e1 <@> e2 <@> e3
step (TmApp e1 e2) | isValue e1 && isValue e2 = computation "PApp" $> paraApp e1 e2
                   | isValue e1 = congruence "AppR" $> TmApp e1 <*> step e2
                   | otherwise  = congruence "AppL" $> TmApp <*> step e1 <@> e2
step (TmFix x e t) = computation "Fix" $> TmAnno (tmSubst x (TmFix x e t) e) t
step (TmAnno e t)
  -- TODO: do type-level beta-reduction elsewhere
  | isValue e = computation "AnnoV" $> fromJust (typedReduce e (tyBReduce t))
  | otherwise = congruence "Anno" $> TmAnno <*> step e <@> t
step (TmMerge e1 e2) | isValue e1 = congruence "MergeR" $> TmMerge e1 <*> step e2
                     | isValue e2 = congruence "MergeL" $> TmMerge <*> step e1 <@> e2
                     | otherwise  = congruence "Merge"  $> TmMerge <*> step e1 <*> step e2
step (TmRcd l e) = congruence "Rcd" $> TmRcd l <*> step e
step (TmPrj e l) | isValue e = computation "PProj" $> paraApp' e (TyRcd l TyTop)
                 | otherwise = congruence "Proj" $> TmPrj <*> step e <@> l
step (TmTApp e t) | isValue e = computation "PTApp" $> paraApp' e t
                  | otherwise = congruence "TApp" $> TmTApp <*> step e <@> t
step e = unsafeCrashWith $
  "Zord.Semantics.step: well-typed programs don't get stuck, but got " <> show e

typedReduce :: Tm -> Ty -> Maybe Tm
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
typedReduce (TmAbs x e targ1 tret1) (TyArr targ2 tret2 _)
  | targ2 <: targ1 && tret1 <: tret2 = Just $ TmAbs x e targ1 tret2
typedReduce (TmMerge v1 v2) t = typedReduce v1 t <|> typedReduce v2 t
typedReduce (TmRcd l v) (TyRcd l' t) | l == l' = TmRcd l <$> typedReduce v t
typedReduce (TmTAbs a1 td1 e t1) (TyForall a2 td2 t2)
  | td2 <: td1 && tySubst a1 (TyVar a2) t1 <: t2 = Just $ TmTAbs a2 td1 e t2
typedReduce _ _ = Nothing

paraApp :: Tm -> Tm -> Tm
paraApp TmUnit _ = TmUnit
paraApp (TmAbs x e targ tret) v = TmAnno (tmSubst x v' e) tret
  where v' = fromJust (typedReduce v targ)
paraApp (TmMerge v1 v2) v = TmMerge (paraApp v1 v) (paraApp v2 v)
paraApp v1 v2 = unsafeCrashWith $
  "Zord.Semantics.paraApp: impossible application of " <> show v1 <> " to " <> show v2

paraApp' :: Tm -> Ty -> Tm
paraApp' TmUnit _ = TmUnit
paraApp' (TmRcd _ v) (TyRcd _ _) = v
paraApp' (TmTAbs a _ e t) ta = TmAnno (tmTSubst a ta e) (tySubst a ta t)
paraApp' (TmMerge v1 v2) t = TmMerge (paraApp' v1 t) (paraApp' v2 t)
paraApp' v t = unsafeCrashWith $
  "Zord.Semantics.paraApp': impossible application of " <> show v <> " to " <> show t

isValue :: Tm -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue (TmUnit)     = true
isValue (TmAbs _ _ _ _) = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmRcd _ e)  = isValue e
isValue (TmTAbs _ _ _ _) = true
isValue _ = false

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
tmSubst x v (TmRcd l e) = TmRcd l (tmSubst x v e)
tmSubst x v (TmPrj e l) = TmPrj (tmSubst x v e) l
tmSubst x v (TmTApp e t) = TmTApp (tmSubst x v e) t
tmSubst x v (TmTAbs a td e t) = TmTAbs a td (tmSubst x v e) t
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
tmTSubst a s (TmRcd l e) = TmRcd l (tmTSubst a s e)
tmTSubst a s (TmPrj e l) = TmPrj (tmTSubst a s e) l
tmTSubst a s (TmTApp e t) = TmTApp (tmTSubst a s e) (tySubst a s t)
tmTSubst a s (TmTAbs a' td e t) = TmTAbs a' (tySubst a s td) (tmTSubst a s e)
                                  (if a == a' then t else tySubst a s t)
tmTSubst _ _ e = e

unop :: UnOp -> Tm -> Tm
unop Neg (TmInt i)    = TmInt    (negate i)
unop Neg (TmDouble n) = TmDouble (negate n)
unop Not (TmBool b)   = TmBool   (not b)
unop op v = unsafeCrashWith $
  "Zord.Semantics.binop: impossible unary operation " <> show op <> " on " <> show v

binop :: BinOp -> Tm -> Tm -> Tm
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
