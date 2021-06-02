module Zord.Semantics.Subst where

import Prelude

import Control.Alt ((<|>))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Common (Arg(..), binop, selectLabel, toString, unop)
import Zord.Subtyping (isTopLike, split, (<:))
import Zord.Syntax.Core (Tm(..), Ty(..), tmSubst, tmTSubst, tySubst)
import Zord.Util (unsafeFromJust)

eval :: Tm -> Tm
eval e | isValue e = e
       | otherwise = eval (step e)

step :: Tm -> Tm
step (TmUnary op e) | isValue e = unop op e
                    | otherwise = TmUnary op (step e)
step (TmBinary op e1 e2) | isValue e1 && isValue e2 = binop op e1 e2
                         | isValue e1 = TmBinary op e1 (step e2)
                         | otherwise  = TmBinary op (step e1) e2
step (TmIf (TmBool true)  e _) = e
step (TmIf (TmBool false) _ e) = e
step (TmIf e1 e2 e3) = TmIf (step e1) e2 e3
step (TmApp e1 e2 coercive)
  | isValue e1 = paraApp e1 ((if coercive then TmAnnoArg else TmArg) e2)
  | otherwise  = TmApp (step e1) e2 coercive
step fix@(TmFix x e _) = tmSubst x fix e
step (TmAnno (TmAnno e _) t) = TmAnno e t
step (TmAnno e t) | isValue e = unsafeFromJust (typedReduce e t)
                  | otherwise = TmAnno (step e) t
step (TmMerge e1 e2) | isValue e1 = TmMerge e1 (step e2)
                     | isValue e2 = TmMerge (step e1) e2
                     | otherwise  = TmMerge (step e1) (step e2)
step (TmPrj e l) | isValue e = selectLabel e l
                 | otherwise = TmPrj (step e) l
step (TmTApp e t) | isValue e = paraApp e (TyArg t)
                  | otherwise = TmTApp (step e) t
step (TmToString e) | isValue e = toString e
                    | otherwise = TmToString (step e)
step e = unsafeCrashWith $ "Zord.Semantics.Subst.step: " <>
  "well-typed programs don't get stuck, but got " <> show e

typedReduce :: Tm -> Ty -> Maybe Tm
typedReduce e _ | not (isValue e) = unsafeCrashWith $
  "Zord.Semantics.Subst.typedReduce: " <> show e <> " is not a value"
typedReduce _ t | isTopLike t = Just TmUnit
typedReduce v t | Just (Tuple t1 t2) <- split t = do
  v1 <- typedReduce v t1
  v2 <- typedReduce v t2
  Just $ TmMerge v1 v2
typedReduce (TmInt i)    TyInt    = Just $ TmInt i
typedReduce (TmDouble n) TyDouble = Just $ TmDouble n
typedReduce (TmString s) TyString = Just $ TmString s
typedReduce (TmBool b)   TyBool   = Just $ TmBool b
typedReduce (TmAbs x e targ1 tret1) (TyArrow _ tret2 _)
  | tret1 <: tret2 = Just $ TmAbs x e targ1 tret2
typedReduce (TmMerge v1 v2) t = typedReduce v1 t <|> typedReduce v2 t
typedReduce (TmRcd l t e) (TyRcd l' t')
  | l == l' && t <: t' = Just $ TmRcd l t' e
typedReduce (TmTAbs a1 td1 e t1) (TyForall a2 td2 t2)
  | td2 <: td1 && tySubst a1 (TyVar a2) t1 <: t2
  = Just $ TmTAbs a2 td1 (tmTSubst a1 (TyVar a2) e) t2
typedReduce (TmArray t arr) (TyArray t') | t <: t' = Just $ TmArray t' arr
typedReduce _ _ = Nothing

paraApp :: Tm -> Arg -> Tm
paraApp TmUnit _ = TmUnit
paraApp (TmAbs x e1 _ _) (TmArg e2) = tmSubst x e2 e1
paraApp (TmAbs x e1 targ tret) (TmAnnoArg e2) =
  TmAnno (tmSubst x (TmAnno e2 targ) e1) tret
paraApp (TmTAbs a _ e _) (TyArg ta) = tmTSubst a ta e
paraApp (TmMerge v1 v2) arg = TmMerge (paraApp v1 arg) (paraApp v2 arg)
paraApp v arg = unsafeCrashWith $ "Zord.Semantics.Subst.paraApp: " <>
  "impossible application " <> show v <> " • " <> show arg

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
isValue (TmArray _ _) = true
isValue _ = false
