module Zord.Semantics where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Writer (Writer, runWriter, tell)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math ((%))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Subtyping (isTopLike, split, (<:))
import Zord.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), Label, LogicOp(..), UnOp(..), fromJust)
import Zord.Syntax.Core (Tm(..), Ty(..), tmSubst, tmTSubst, tySubst)

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
step (TmApp e1 e2) | isValue e1 = computation "PApp" $> paraApp e1 e2
                   | otherwise  = congruence "AppL" $> TmApp <*> step e1 <@> e2
step (TmFix x e t) = computation "Fix" $> TmAnno (tmSubst x (TmFix x e t) e) t
step (TmAnno e t) | isValue e = computation "AnnoV" $> fromJust (typedReduce e t)
                  | otherwise = congruence "Anno" $> TmAnno <*> step e <@> t
step (TmMerge e1 e2) | isValue e1 = congruence "MergeR" $> TmMerge e1 <*> step e2
                     | isValue e2 = congruence "MergeL" $> TmMerge <*> step e1 <@> e2
                     | otherwise  = congruence "Merge"  $> TmMerge <*> step e1 <*> step e2
step (TmPrj e l) | isValue e = computation "PProj" $> selectLabel e l
                 | otherwise = congruence "Proj" $> TmPrj <*> step e <@> l
step (TmTApp e t) | isValue e = computation "PTApp" $> paraApp' e t
                  | otherwise = congruence "TApp" $> TmTApp <*> step e <@> t
step (TmToString e) | isValue e = computation "ToStringV" $> toString e
                    | otherwise = congruence "ToString" $> TmToString <*> step e
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
typedReduce (TmRcd l t e) (TyRcd l' t')
  | l == l' && t <: t' = Just $ TmRcd l t' (TmAnno e t')
typedReduce (TmTAbs a1 td1 e t1) (TyForall a2 td2 t2)
  | td2 <: td1 && tySubst a1 (TyVar a2) t1 <: t2
  = Just $ TmTAbs a2 td1 (tmTSubst a1 (TyVar a2) e) t2
typedReduce _ _ = Nothing

paraApp :: Tm -> Tm -> Tm
paraApp TmUnit _ = TmUnit
paraApp (TmAbs x e1 targ tret) e2 = TmAnno (tmSubst x (TmAnno e2 targ) e1) tret
paraApp (TmMerge v1 v2) e = TmMerge (paraApp v1 e) (paraApp v2 e)
paraApp v e = unsafeCrashWith $
  "Zord.Semantics.paraApp: impossible application of " <> show v <> " to " <> show e

paraApp' :: Tm -> Ty -> Tm
paraApp' TmUnit _ = TmUnit
paraApp' (TmTAbs a _ e t) ta = TmAnno (tmTSubst a ta e) (tySubst a ta t)
paraApp' (TmMerge v1 v2) t = TmMerge (paraApp' v1 t) (paraApp' v2 t)
paraApp' v t = unsafeCrashWith $
  "Zord.Semantics.paraApp': impossible application of " <> show v <> " to " <> show t

selectLabel :: Tm -> Label -> Tm
selectLabel (TmMerge e1 e2) l = case selectLabel e1 l, selectLabel e2 l of
  TmUnit, TmUnit -> TmUnit
  TmUnit, e2' -> e2'
  e1', TmUnit -> e1'
  e1', e2' -> TmMerge e1' e2'
selectLabel (TmRcd l' _ e) l | l == l' = e
selectLabel _ _ = TmUnit

isValue :: Tm -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue (TmUnit)     = true
isValue (TmAbs _ _ _ _) = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmRcd _ _ _) = true
isValue (TmTAbs _ _ _ _) = true
isValue _ = false


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
binop Append (TmString s1) (TmString s2) = TmString (s1 <> s2)
binop op v1 v2 = unsafeCrashWith $
  "Zord.Semantics.binop: impossible binary operation " <> show op <>
  " between " <> show v1 <> " and " <> show v2

toString :: Tm -> Tm
toString (TmInt i)    = TmString (show i)
toString (TmDouble n) = TmString (show n)
toString (TmString s) = TmString (show s)
toString (TmBool b)   = TmString (show b)
toString v = unsafeCrashWith $
  "Zord.Semantics.toString: impossible from " <> show v <> " to string"
