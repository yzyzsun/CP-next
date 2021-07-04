module Zord.Syntax.Core where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (intercalate)
import Data.Map (Map, empty, insert, lookup)
import Data.Maybe (Maybe(..))
import Zord.Syntax.Common (BinOp, Label, Name, UnOp, angles, braces, brackets, parens)
import Zord.Util ((<+>))

foreign import data TmRef :: Type
foreign import new :: Tm -> TmRef
foreign import done :: TmRef -> Boolean
foreign import read :: TmRef -> Tm
foreign import write :: Tm -> TmRef -> Tm

-- Types --

data Ty = TyInt
        | TyDouble
        | TyString
        | TyBool
        | TyTop
        | TyBot
        | TyArrow Ty Ty Boolean
        | TyAnd Ty Ty
        | TyRcd Label Ty
        | TyVar Name
        | TyForall Name Ty Ty
        | TyArray Ty

instance Show Ty where
  show TyInt    = "Int"
  show TyDouble = "Double"
  show TyString = "String"
  show TyBool   = "Bool"
  show TyTop    = "⊤"
  show TyBot    = "⊥"
  show (TyArrow ti to true) = "Trait" <> angles (show ti <+> "%" <+> show to)
  show (TyArrow t1 t2 false) = parens $ show t1 <+> "→" <+> show t2
  show (TyAnd t1 t2) = parens $ show t1 <+> "&" <+> show t2
  show (TyRcd l t) = braces $ l <+> ":" <+> show t
  show (TyVar a) = a
  show (TyForall a td t) = parens $
    "∀" <> a <+> "*" <+> show td <> "." <+> show t
  show (TyArray t) = brackets $ show t

derive instance Eq Ty

-- Terms --

data Tm = TmInt Int
        | TmDouble Number
        | TmString String
        | TmBool Boolean
        | TmUnit
        | TmUndefined
        | TmUnary UnOp Tm
        | TmBinary BinOp Tm Tm
        | TmIf Tm Tm Tm
        | TmVar Name
        | TmApp Tm Tm Boolean
        | TmAbs Name Tm Ty Ty Boolean
        | TmHAbs (Tm -> Tm) Ty Ty Boolean
        | TmFix Name Tm Ty
        | TmHFix (Tm -> Tm) Ty
        | TmAnno Tm Ty
        | TmMerge Tm Tm
        | TmRcd Label Ty Tm
        | TmPrj Tm Label
        | TmTApp Tm Ty
        | TmTAbs Name Ty Tm Ty
        | TmHTAbs (Ty -> Tm) Ty (Ty -> Ty)
        | TmToString Tm
        | TmArray Ty (Array Tm)
        | TmClosure EvalEnv Tm
        | TmRef TmRef

instance Show Tm where
  show (TmInt i)    = show i
  show (TmDouble n) = show n
  show (TmString s) = show s
  show (TmBool b)   = show b
  show TmUnit       = "()"
  show TmUndefined  = "undefined"
  show (TmUnary op e) = show op <> show e
  show (TmBinary op e1 e2) = parens $ show e1 <+> show op <+> show e2
  show (TmIf e1 e2 e3) = parens $
    "if" <+> show e1 <+> "then" <+> show e2 <+> "else" <+> show e3
  show (TmVar x) = x
  show (TmApp e1 e2 _coercive) = parens $ show e1 <+> show e2
  show (TmAbs x e targ tret _refined) = parens $
    "λ" <> x <> "." <+> show e <+> ":" <+> show targ <+> "→" <+> show tret
  show (TmHAbs _abs targ tret _refined) = angles $
    "HOAS" <+> show targ <+> "→" <+> show tret
  show (TmFix x e t) = parens $ "fix" <+> x <> "." <+> show e <+> ":" <+> show t
  show (TmHFix _fix t) = angles $ "HOAS fix" <+> show t
  show (TmAnno e t) = parens $ show e <+> ":" <+> show t
  show (TmMerge e1 e2) = parens $ show e1 <+> "," <+> show e2
  show (TmRcd l t e) = braces $ l <+> ":" <+> show t <+> "=" <+> show e
  show (TmPrj e l) = show e <> "." <> l
  show (TmTApp e t) = parens $ show e <+> "@" <> show t
  show (TmTAbs a td e t) = parens $ "Λ" <> a <> "." <+> show e <+>
    ":" <+> "∀" <> a <+> "*" <+> show td <> "." <+> show t
  show (TmHTAbs _tabs td _tf) = angles $ "HOAS ∀*" <+> show td
  show (TmToString e) = parens $ "toString" <+> show e
  show (TmArray t arr) = parens $
    brackets (intercalate "; " (show <$> arr)) <+> ":" <+> brackets (show t)
  show (TmClosure _env e) = angles $ "Closure" <+> show e
  show (TmRef _ref) = angles $ "Ref"

-- HOAS --

tmHoas :: Tm -> Tm
tmHoas = tmConvert empty

-- convert a type containing a named variable to a HOAS type-level function
tyHoas :: Name -> Ty -> Ty -> Ty
tyHoas = tyHoas' empty

tyHoas' :: HoasEnv -> Name -> Ty -> Ty -> Ty
tyHoas' env a t = \ty -> tyConvert (insert a (Right ty) env) t

tyConvert :: HoasEnv -> Ty -> Ty
tyConvert env (TyArrow t1 t2 b) = TyArrow (tyConvert env t1) (tyConvert env t2) b
tyConvert env (TyAnd t1 t2) = TyAnd (tyConvert env t1) (tyConvert env t2)
tyConvert env (TyRcd l t) = TyRcd l (tyConvert env t)
tyConvert env (TyVar a) = case lookup a env of Just (Right t) -> t
                                               _ -> TyVar a
tyConvert env (TyForall a td t) = TyForall a (tyConvert env td) (tyConvert env t)
tyConvert env (TyArray t) = TyArray (tyConvert env t)
tyConvert _ t = t

tmConvert :: HoasEnv -> Tm -> Tm
tmConvert env (TmUnary op e) = TmUnary op (tmConvert env e)
tmConvert env (TmBinary op e1 e2) =
  TmBinary op (tmConvert env e1) (tmConvert env e2)
tmConvert env (TmIf e1 e2 e3) =
  TmIf (tmConvert env e1) (tmConvert env e2) (tmConvert env e3)
tmConvert env (TmVar x) = case lookup x env of Just (Left e) -> e
                                               _ -> TmVar x
tmConvert env (TmApp e1 e2 b) = TmApp (tmConvert env e1) (tmConvert env e2) b
tmConvert env (TmAbs x e targ tret b) =
  TmHAbs (\tm -> tmConvert (insert x (Left tm) env) e)
         (tyConvert env targ) (tyConvert env tret) b
tmConvert env (TmFix x e t) =
  TmHFix (\tm -> tmConvert (insert x (Left tm) env) e) (tyConvert env t)
tmConvert env (TmAnno e t) = TmAnno (tmConvert env e) (tyConvert env t)
tmConvert env (TmMerge e1 e2) = TmMerge (tmConvert env e1) (tmConvert env e2)
tmConvert env (TmRcd l t e) = TmRcd l (tyConvert env t) (tmConvert env e)
tmConvert env (TmPrj e l) = TmPrj (tmConvert env e) l
tmConvert env (TmTApp e t) = TmTApp (tmConvert env e) (tyConvert env t)
tmConvert env (TmTAbs a td e t) =
  TmHTAbs (\ty -> tmConvert (insert a (Right ty) env) e)
          (tyConvert env td) (tyHoas' env a t)
tmConvert env (TmToString e) = TmToString (tmConvert env e)
tmConvert env (TmArray t arr) = TmArray (tyConvert env t) (tmConvert env <$> arr)
tmConvert _ e = e

type HoasEnv = Map Name (Either Tm Ty)

-- Substitution --

-- TODO: capture-avoiding
tySubst :: Name -> Ty -> Ty -> Ty
tySubst a s (TyArrow t1 t2 b) = TyArrow (tySubst a s t1) (tySubst a s t2) b
tySubst a s (TyAnd t1 t2) = TyAnd (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyRcd l t) = TyRcd l (tySubst a s t)
tySubst a s (TyVar a') = if a == a' then s else TyVar a'
tySubst a s (TyForall a' td t) =
  TyForall a' (tySubst a s td) (if a == a' then t else tySubst a s t)
tySubst a s (TyArray t) = TyArray (tySubst a s t)
tySubst _ _ t = t

tmSubst :: Name -> Tm -> Tm -> Tm
tmSubst x v (TmUnary op e) = TmUnary op (tmSubst x v e)
tmSubst x v (TmBinary op e1 e2) = TmBinary op (tmSubst x v e1) (tmSubst x v e2)
tmSubst x v (TmIf e1 e2 e3) =
  TmIf (tmSubst x v e1) (tmSubst x v e2) (tmSubst x v e3)
tmSubst x v (TmVar x') = if x == x' then v else TmVar x'
tmSubst x v (TmApp e1 e2 b) = TmApp (tmSubst x v e1) (tmSubst x v e2) b
tmSubst x v (TmAbs x' e targ tret b) =
  TmAbs x' (if x == x' then e else tmSubst x v e) targ tret b
tmSubst x v (TmFix x' e t) = TmFix x' (if x == x' then e else tmSubst x v e) t
tmSubst x v (TmAnno e t) = TmAnno (tmSubst x v e) t
tmSubst x v (TmMerge e1 e2) = TmMerge (tmSubst x v e1) (tmSubst x v e2)
tmSubst x v (TmRcd l t e) = TmRcd l t (tmSubst x v e)
tmSubst x v (TmPrj e l) = TmPrj (tmSubst x v e) l
tmSubst x v (TmTApp e t) = TmTApp (tmSubst x v e) t
tmSubst x v (TmTAbs a td e t) = TmTAbs a td (tmSubst x v e) t
tmSubst x v (TmToString e) = TmToString (tmSubst x v e)
tmSubst x v (TmArray t arr) = TmArray t (tmSubst x v <$> arr)
tmSubst _ _ e = e

tmTSubst :: Name -> Ty -> Tm -> Tm
tmTSubst a s (TmUnary op e) = TmUnary op (tmTSubst a s e)
tmTSubst a s (TmBinary op e1 e2) =
  TmBinary op (tmTSubst a s e1) (tmTSubst a s e2)
tmTSubst a s (TmIf e1 e2 e3) =
  TmIf (tmTSubst a s e1) (tmTSubst a s e2) (tmTSubst a s e3)
tmTSubst a s (TmApp e1 e2 b) = TmApp (tmTSubst a s e1) (tmTSubst a s e2) b
tmTSubst a s (TmAbs x e targ tret b) =
  TmAbs x (tmTSubst a s e) (tySubst a s targ) (tySubst a s tret) b
tmTSubst a s (TmFix x e t) = TmFix x (tmTSubst a s e) (tySubst a s t)
tmTSubst a s (TmAnno e t) = TmAnno (tmTSubst a s e) (tySubst a s t)
tmTSubst a s (TmMerge e1 e2) = TmMerge (tmTSubst a s e1) (tmTSubst a s e2)
tmTSubst a s (TmRcd l t e) = TmRcd l (tySubst a s t) (tmTSubst a s e)
tmTSubst a s (TmPrj e l) = TmPrj (tmTSubst a s e) l
tmTSubst a s (TmTApp e t) = TmTApp (tmTSubst a s e) (tySubst a s t)
tmTSubst a s (TmTAbs a' td e t) = TmTAbs a' (tySubst a s td) (tmTSubst a s e)
                                  (if a == a' then t else tySubst a s t)
tmTSubst a s (TmToString e) = TmToString (tmTSubst a s e)
tmTSubst a s (TmArray t arr) = TmArray (tySubst a s t) (tmTSubst a s <$> arr)
tmTSubst _ _ e = e

-- Environment --

type EvalEnv = Map Name EvalBind

data EvalBind = TmBind Tm | TyBind (Maybe Ty)

instance Show EvalBind where
  show (TmBind e) = show e
  show (TyBind (Just t)) = show t
  show (TyBind Nothing) = "*"
