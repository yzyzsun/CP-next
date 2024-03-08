module Language.CP.Semantics.Subst where

import Prelude

import Control.Alt ((<|>))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Language.CP.Semantics.Common (Arg(..), binop, genTopLike, selectLabel, toString, unop)
import Language.CP.Subtyping (isTopLike, split, (<:))
import Language.CP.Syntax.Core (Tm(..), Ty(..), tmSubst, tmTSubst, tySubst, unfold)
import Language.CP.Util (unsafeFromJust)
import Partial.Unsafe (unsafeCrashWith)

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
step (TmAnno e t) | isValue e = unsafeFromJust (cast e t)
                  | otherwise = TmAnno (step e) t
step (TmMerge e1 e2) | isValue e1 = TmMerge e1 (step e2)
                     | isValue e2 = TmMerge (step e1) e2
                     | otherwise  = TmMerge (step e1) (step e2)
step (TmPrj e l) | isValue e = selectLabel e l
                 | otherwise = TmPrj (step e) l
step (TmOptPrj e1 l t e2)
  | isValue e1 = case cast e1 (TyRcd l t false) of Just e -> TmPrj e l
                                                   Nothing -> e2
  | otherwise  = TmOptPrj (step e1) l t e2
step (TmTApp e t) | isValue e = paraApp e (TyArg t)
                  | otherwise = TmTApp (step e) t
step (TmDef x e1 e2) = tmSubst x e1 e2
step (TmFold t e) = TmFold t (step e)
step (TmUnfold t e) | isTopLike t = TmTop
                    | TmFold _ e' <- e = TmAnno e' (unfold t)
                    | TmMerge _ _ <- e = TmUnfold t (TmAnno e t)
                    | otherwise = TmUnfold t (step e)
step (TmToString e) | isValue e = toString e
                    | otherwise = TmToString (step e)
step (TmMain e) = step e
step e = unsafeCrashWith $ "CP.Semantics.Subst.step: " <>
  "well-typed programs don't get stuck, but got " <> show e

cast :: Tm -> Ty -> Maybe Tm
cast e _ | not (isValue e) = unsafeCrashWith $
  "CP.Semantics.Subst.cast: " <> show e <> " is not a value"
cast v t | Just (t1 /\ t2) <- split t = do
  let m1 = isOptionalRcd t1
      m2 = isOptionalRcd t2
      v1 = cast v t1
      v2 = cast v t2
  (TmMerge <$> v1 <*> v2) <|> (m1 *> v2) <|> (m2 *> v1) <|> (m1 *> m2)
  where isOptionalRcd (TyRcd _ _ true) = Just TmTop
        isOptionalRcd _ = Nothing
cast _ t | isTopLike t = Just $ genTopLike t
cast (TmInt i)    TyInt    = Just $ TmInt i
cast (TmDouble n) TyDouble = Just $ TmDouble n
cast (TmString s) TyString = Just $ TmString s
cast (TmBool b)   TyBool   = Just $ TmBool b
cast (TmAbs x e targ1 tret1 _ b) (TyArrow _ tret2 _)
  | tret1 <: tret2 = Just $ TmAbs x e targ1 tret2 true b
cast (TmMerge v1 v2) t = cast v1 t <|> cast v2 t
cast (TmRcd l t e) (TyRcd l' t' _)
  | l == l' && t <: t' = Just $ TmRcd l t' e
cast (TmTAbs a1 td1 e t1 _) (TyForall a2 td2 t2)
  | td2 <: td1 && tySubst a1 (TyVar a2) t1 <: t2
  = Just $ TmTAbs a2 td1 (tmTSubst a1 (TyVar a2) e) t2 true
cast (TmFold t v) t'@(TyRec _ _) | t <: t' = Just $ TmFold t' v
cast (TmArray t arr) (TyArray t') | t <: t' = Just $ TmArray t' arr
cast _ _ = Nothing

paraApp :: Tm -> Arg -> Tm
paraApp (TmAbs x e1 _ _ false _) (TmArg e2) = tmSubst x e2 e1
paraApp (TmAbs x e1 _ tret true _) (TmArg e2) = TmAnno (tmSubst x e2 e1) tret
paraApp (TmAbs x e1 targ tret _ _) (TmAnnoArg e2) =
  TmAnno (tmSubst x (TmAnno e2 targ) e1) tret
paraApp (TmTAbs a _ e _ false) (TyArg ta) = tmTSubst a ta e
paraApp (TmTAbs a _ e t true) (TyArg ta) =
  TmAnno (tmTSubst a ta e) (tySubst a ta t)
paraApp (TmMerge v1 v2) arg = TmMerge (paraApp v1 arg) (paraApp v2 arg)
paraApp v arg = unsafeCrashWith $ "CP.Semantics.Subst.paraApp: " <>
  "impossible application " <> show v <> " • " <> show arg

isValue :: Tm -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue TmUnit       = true
isValue TmTop        = true
isValue (TmAbs _ _ _ _ _ _) = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmRcd _ _ _) = true
isValue (TmTAbs _ _ _ _ _) = true
isValue (TmFold _ e) = isValue e
isValue (TmArray _ _) = true
isValue _ = false
