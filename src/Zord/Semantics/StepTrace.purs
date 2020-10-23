module Zord.Semantics.StepTrace where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Writer (Writer, runWriter, tell)
import Data.Bifunctor (rmap)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Monoid.Endo (Endo(..))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Common (binop, toString, unop)
import Zord.Subtyping (isTopLike, split, (<:))
import Zord.Syntax.Common (Label, fromJust)
import Zord.Syntax.Core (Tm(..), Ty(..), tmSubst, tmTSubst, tySubst)

type ShowS = String -> String
type EndoS = Endo Function String
type Eval a = Writer EndoS a

endoS :: String -> EndoS
endoS s = Endo (s <> _)

computation :: String -> Eval Unit
computation w = tell <<< endoS $ "↓ Step-" <> w <> "\n"

congruence :: String -> Eval Unit
congruence w = tell <<< endoS $ "→ Step-" <> w <> "\n"

eval :: Tm -> Tuple Tm ShowS
eval = go >>> runWriter >>> rmap unwrap
  where go :: Tm -> Eval Tm
        go e | isValue e = tell (endoS $ show e <> "\n") $> e
             | otherwise = tell (endoS $ show e <> "\n") *> step e >>= go

step :: Tm -> Eval Tm
step (TmUnary op e)
  | isValue e = computation "UnaryV" $> unop op e
  | otherwise = congruence  "Unary"  $> TmUnary op <*> step e
step (TmBinary op e1 e2)
  | isValue e1 && isValue e2 = computation "BinaryV" $> binop op e1 e2
  | isValue e1 = congruence "BinaryR" $> TmBinary op e1 <*> step e2
  | otherwise  = congruence "BinaryL" $> TmBinary op <*> step e1 <@> e2
step (TmIf (TmBool true)  e2 e3) = computation "IfTrue"  $> e2
step (TmIf (TmBool false) e2 e3) = computation "IfFalse" $> e3
step (TmIf e1 e2 e3) = congruence "If" $> TmIf <*> step e1 <@> e2 <@> e3
step (TmApp e1 e2)
  | isValue e1 = computation "PApp" $> paraApp e1 (Left e2)
  | otherwise  = congruence  "AppL" $> TmApp <*> step e1 <@> e2
step (TmFix x e t) = computation "Fix" $> TmAnno (tmSubst x (TmFix x e t) e) t
step (TmAnno (TmAnno e t') t) = computation "AnnoAnno" $> TmAnno e t
step (TmAnno e t)
  | isValue e = computation "AnnoV" $> fromJust (typedReduce e t)
  | otherwise = congruence  "Anno"  $> TmAnno <*> step e <@> t
step (TmMerge e1 e2)
  | isValue e1 = congruence "MergeR" $> TmMerge e1 <*> step e2
  | isValue e2 = congruence "MergeL" $> TmMerge <*> step e1 <@> e2
  | otherwise  = congruence "Merge"  $> TmMerge <*> step e1 <*> step e2
step (TmPrj e l)
  | isValue e = computation "PProj" $> selectLabel e l
  | otherwise = congruence  "Proj"  $> TmPrj <*> step e <@> l
step (TmTApp e t)
  | isValue e = computation "PTApp" $> paraApp e (Right t)
  | otherwise = congruence  "TApp"  $> TmTApp <*> step e <@> t
step (TmToString e)
  | isValue e = computation "ToStringV" $> toString e
  | otherwise = congruence  "ToString"  $> TmToString <*> step e
step e = unsafeCrashWith $ "Zord.Semantics.StepTrace.step: " <>
  "well-typed programs don't get stuck, but got " <> show e

typedReduce :: Tm -> Ty -> Maybe Tm
typedReduce e _ | not (isValue e) = unsafeCrashWith $
  "Zord.Semantics.StepTrace.typedReduce: " <> show e <> " is not a value"
typedReduce _ t | isTopLike t = Just TmUnit
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

paraApp :: Tm -> Either Tm Ty -> Tm
paraApp TmUnit _ = TmUnit
paraApp (TmAbs x e1 targ tret) (Left e2) =
  TmAnno (tmSubst x (TmAnno e2 targ) e1) tret
paraApp (TmTAbs a _ e t) (Right ta) = TmAnno (tmTSubst a ta e) (tySubst a ta t)
paraApp (TmMerge v1 v2) et = TmMerge (paraApp v1 et) (paraApp v2 et)
paraApp v e = unsafeCrashWith $ "Zord.Semantics.StepTrace.paraApp: " <>
  "impossible application " <> show v <> " • " <> show e

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
