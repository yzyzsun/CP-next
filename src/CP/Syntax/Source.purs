module Language.CP.Syntax.Source where

import Prelude

import Data.Bifunctor (rmap)
import Data.Either (Either(..))
import Data.Foldable (class Foldable, any, foldMap, intercalate, null)
import Data.List (List)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Syntax.Common (BinOp, Label, Name, UnOp, angles, braces, brackets, parens)
import Language.CP.Util (isCapitalized, (<+>))
import Parsing (Position)

-- Types --

data Ty = TyInt
        | TyDouble
        | TyString
        | TyBool
        | TyUnit
        | TyTop
        | TyBot
        | TyArrow Ty Ty
        | TyAnd Ty Ty
        | TyRcd RcdTyList
        | TyVar Name
        | TyForall TyParamList Ty
        | TyRec Name Ty
        | TyRef Ty
        | TyApp Ty Ty
        | TyAbs Name Ty
        | TyTrait (Maybe Ty) Ty
        | TySort Ty (Maybe Ty)
        | TySig Name Name Ty
        | TyArray Ty
        | TyDiff Ty Ty

instance Show Ty where
  show TyInt    = "Int"
  show TyDouble = "Double"
  show TyString = "String"
  show TyBool   = "Bool"
  show TyUnit   = "()"
  show TyTop    = "Top"
  show TyBot    = "Bot"
  show (TyArrow t1 t2) = parens $ show t1 <+> "->" <+> show t2
  show (TyAnd t1 t2) = parens $ show t1 <+> "&" <+> show t2
  show (TyRcd xs) = braces $ showRcdTy xs
  show (TyVar a) = a
  show (TyForall xs t) = parens $
    "forall" <+> showTyParams xs <> "." <+> show t
  show (TyRec a t) = parens $ "mu" <+> a <> "." <+> show t
  show (TyRef t) = parens $ "Ref" <+> show t
  show (TyApp t1 t2) = parens $ show t1 <+> show t2
  show (TyAbs a t) = parens $ "\\" <> a <+> "->" <+> show t
  show (TyTrait ti to) = "Trait" <> angles (showMaybe "" ti " => " <> show to)
  show (TySort ti to) = angles $ show ti <> showMaybe " => " to ""
  show (TySig a b t) = -- \<a, b> accepts an expanded form of original <I => O>
    parens $ "\\" <> angles (a <> "," <+> b) <+> "->" <+> show t
  show (TyArray t) = brackets $ show t
  show (TyDiff t1 t2) = parens $ show t1 <+> "\\" <+> show t2

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
        | TmApp Tm Tm
        | TmAbs TmParamList Tm
        | TmFix Name Tm Ty
        | TmAnno Tm Ty
        | TmMerge Bias Tm Tm
        | TmRcd (List RcdField)
        | TmPrj Tm Label
        | TmOptPrj Tm Label Tm
        | TmTApp Tm Ty
        | TmTAbs TyParamList Tm
        | TmLet Name TyParamList TmParamList Tm Tm
        | TmLetrec Name TyParamList TmParamList Ty Tm Tm
        | TmOpen Tm Tm
        | TmUpdate Tm (List (Label /\ Tm))
        | TmTrait SelfAnno (Maybe Ty) (Maybe Tm) Tm
        | TmNew Tm
        | TmForward Tm Tm
        | TmExclude Tm Ty
        | TmRemoval Tm Label
        | TmDiff Tm Tm
        | TmRename Tm Label Label
        | TmFold Ty Tm
        | TmUnfold Ty Tm
        | TmRef Tm
        | TmDeref Tm
        | TmAssign Tm Tm
        | TmSeq Tm Tm
        | TmToString Tm
        | TmArray (Array Tm)
        | TmDoc Tm
        | TmPos Position Tm

data Bias = Neutral | Leftist | Rightist
derive instance Eq Bias

instance Show Bias where
  show Neutral  = ","
  show Leftist  = "+,"
  show Rightist = ",+"

-- TODO: add type parameters and support recursion
data RcdField = RcdField Boolean Label TmParamList (Either Tm MethodPattern)
              | DefaultPattern MethodPattern
data MethodPattern = MethodPattern SelfAnno Label TmParamList Tm

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
  show (TmVar x) = if isCapitalized x then "$" <> x else x
  show (TmApp e1 e2) = parens $ show e1 <+> show e2
  show (TmAbs xs e) = parens $ "\\" <> showTmParams xs <> "->" <+> show e
  show (TmFix x e t) = parens $ "fix" <+> x <+> ":" <+> show t <> "." <+> show e
  show (TmAnno e t) = parens $ show e <+> ":" <+> show t
  show (TmMerge bias e1 e2) = parens $ show e1 <+> show bias <+> show e2
  show (TmRcd xs) = braces $ showRcdTm xs
  show (TmPrj e l) = show e <> "." <> l
  show (TmOptPrj e1 l e2) = show e1 <> "." <> l <+> "??" <+> show e2
  show (TmTApp e t) = parens $ show e <+> "@" <> show t
  show (TmTAbs xs e) = parens $ "/\\" <> showTyParams xs <> "." <+> show e
  show (TmLet x tyParams tmParams e1 e2) = parens $
    "let" <+> x <+> showTyParams tyParams <> showTmParams tmParams <>
    "=" <+> show e1 <+> "in" <+> show e2
  show (TmLetrec x tyParams tmParams t e1 e2) = parens $
    "letrec" <+> x <+> showTyParams tyParams <> showTmParams tmParams <>
    ":" <+> show t <+> "=" <+> show e1 <+> "in" <+> show e2
  show (TmOpen e1 e2) = parens $ "open" <+> show e1 <+> "in" <+> show e2
  show (TmUpdate rcd fields) = braces $ show rcd <+> "with" <+>
    intercalate "; " (fields <#> \(l /\ e) -> l <+> "=" <+> show e)
  show (TmTrait self sig e1 e2) = parens $ "trait" <>
    maybe "" (" " <> _) (showSelfAnno self) <+>
    showMaybe "implements " sig " " <> showMaybe "inherits " e1 " " <>
    "=>" <+> show e2
  show (TmNew e) = parens $ "new" <+> show e
  show (TmForward e1 e2) = parens $ show e1 <+> "^" <+> show e2
  show (TmExclude e t) = parens $ show e <+> "\\\\" <+> show t
  show (TmRemoval e l) = parens $ show e <+> "\\" <+> l
  show (TmDiff e1 e2) = parens $ show e1 <+> "\\-" <+> show e2
  show (TmRename e old new) = parens $ show e <+> brackets (old <+> "<-" <+> new)
  show (TmFold t e) = parens $ "fold @" <> show t <+> show e
  show (TmUnfold t e) = parens $ "unfold @" <> show t <+> show e
  show (TmRef e) = parens $ "ref" <+> show e
  show (TmDeref e) = "!" <> show e
  show (TmAssign e1 e2) = parens $ show e1 <+> ":=" <+> show e2
  show (TmSeq e1 e2) = show e1 <+> ">>" <+> show e2
  show (TmToString e) = parens $ "toString" <+> show e
  show (TmArray arr) = brackets $ intercalate "; " (show <$> arr)
  show (TmDoc e) = show e
  show (TmPos _pos e) = show e

showDoc :: Tm -> String
showDoc (TmDoc e) = "`" <> showDoc e <> "`"
showDoc (TmPos _ (TmDoc e)) = "[" <> showDoc e <> "]"
showDoc (TmPos _ e) = showDoc e
showDoc (TmNew e) = showDoc e
showDoc (TmVar "Endl") = "\\\\"
showDoc (TmVar x) = "\\" <> x
showDoc (TmApp (TmApp (TmVar "Comp") e1) e2) = showDoc e1 <> showDoc e2
showDoc (TmApp (TmVar "Str") (TmString s)) = s
showDoc (TmApp (TmVar "Str") (TmToString s)) = "\\(" <> show s <> ")"
showDoc (TmApp e1 e2) = showDoc e1 <> showDoc e2
showDoc e = "(" <> show e <> ")"

-- Definitions --
data TypeDef = TypeAlias | Interface | InterfaceExtends Ty

data Def = TyDef TypeDef Name (List Name) (List Name) Ty
         | TmDef Name TyParamList TmParamList (Maybe Ty) Tm

instance Show Def where
  show (TyDef def a sorts params t) =
    let keyword = case def of TypeAlias -> "type"
                              _ -> "interface"
        extends = case def of InterfaceExtends super -> "extends" <+> show super
                              _ -> ""
    in keyword <+> a <+>
    intercalate' " " (angles <$> sorts) <> intercalate' " " params <>
    extends <+> "=" <+> show t <> ";"
  show (TmDef x tyParams tmParams t e) = x <+>
    showTyParams tyParams <> showTmParams tmParams <>
    showMaybe ": " t " " <> "=" <+> show e <> ";"

-- Program --
data Prog = Prog (List Def) Tm

instance Show Prog where
  show (Prog defs e) = intercalate' "\n" (map show defs) <> "\n" <> show e

-- Substitution --

-- TODO: capture-avoiding
tySubst :: Name -> Ty -> Ty -> Ty
tySubst a s (TyArrow t1 t2) = TyArrow (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyAnd t1 t2) = TyAnd (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyRcd xs) =
  TyRcd (xs <#> \(RcdTy l t opt) -> RcdTy l (tySubst a s t) opt)
tySubst a s (TyVar a') = if a == a' then s else TyVar a'
tySubst a s (TyForall xs t) = TyForall (rmap (map (tySubst a s)) <$> xs)
  (if any ((_ == a) <<< fst) xs then t else tySubst a s t)
tySubst a s (TyRec a' t) = TyRec a' (if a == a' then t else tySubst a s t)
tySubst a s (TyRef t) = TyRef (tySubst a s t)
tySubst a s (TyApp t1 t2) = TyApp (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyAbs a' t) = TyAbs a' (if a == a' then t else tySubst a s t)
tySubst a s (TyTrait ti to) = TyTrait (tySubst a s <$> ti) (tySubst a s to)
tySubst a s (TySort ti to) = TySort (tySubst a s ti) (tySubst a s <$> to)
tySubst a s (TySig a' b' t) = TySig a' b'
  (if a == a' || a == b' then t else tySubst a s t)
tySubst a s (TyArray t) = TyArray (tySubst a s t)
tySubst a s (TyDiff t1 t2) = TyDiff (tySubst a s t1) (tySubst a s t2)
tySubst _ _ t = t

-- Helpers --

intercalate' :: forall f m. Foldable f => Monoid m => m -> f m -> m
intercalate' sep xs = if null xs then mempty else intercalate sep xs <> sep

showMaybe :: forall a. Show a => String -> Maybe a -> String -> String
showMaybe l m r = maybe "" (\x -> l <> show x <> r) m

type TyParamList = List TyParam
type TyParam = Name /\ Maybe Ty

showTyParams :: TyParamList -> String
showTyParams params = intercalate' " " $ params <#> \param ->
  maybe (fst param) (\t -> parens $ fst param <+> "*" <+> show t) (snd param)

type TmParamList = List TmParam
data TmParam = TmParam Name (Maybe Ty)
             | WildCard DefaultFields
type DefaultFields = List (Label /\ Tm)

showTmParams :: TmParamList -> String
showTmParams params = intercalate' " " $ params <#> case _ of
  TmParam x (Just t) -> parens $ x <+> ":" <+> show t
  TmParam x Nothing -> x
  WildCard defaults -> "{" <> foldMap showField defaults <> "..}"
  where showField (x /\ e) = x <+> "=" <+> show e <> "; "

type RcdTyList = List RcdTy
data RcdTy = RcdTy Label Ty Boolean
derive instance Eq RcdTy

showRcdTy :: RcdTyList -> String
showRcdTy xs = intercalate "; " $ xs <#> \(RcdTy l t opt) ->
  l <> (if opt then "?" else "") <+> ":" <+> show t

showRcdTm :: List RcdField -> String
showRcdTm xs = intercalate "; " $ xs <#> case _ of
  RcdField o l p e -> (if o then "override " else "") <> showField l p e
  DefaultPattern (MethodPattern self l p e) ->
    fromMaybe "_" (showSelfAnno self) <> showMethod l p e
  where showField :: Label -> TmParamList -> Either Tm MethodPattern -> String
        showField l p (Left e) = l <+> showTmParams p <> "=" <+> show e
        showField l p (Right (MethodPattern self l' p' e)) =
          maybe "" (_ <> "@") (showSelfAnno self) <>
          parens (" " <> l <+> showTmParams p) <> showMethod l' p' e
        showMethod :: Label -> TmParamList -> Tm -> String
        showMethod l p e = "." <> l <+> showTmParams p <> "=" <+> show e

type SelfAnno = Maybe (Name /\ Maybe Ty)

showSelfAnno :: SelfAnno -> Maybe String
showSelfAnno = map \(x /\ mt) -> brackets $ case mt of
  Just t  -> x <+> ":" <+> show t
  Nothing -> x
