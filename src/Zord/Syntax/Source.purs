module Zord.Syntax.Source where

import Prelude

import Data.Bifunctor (rmap)
import Data.Either (Either(..))
import Data.Foldable (class Foldable, any, intercalate, null)
import Data.List (List)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..), fst, snd)
import Text.Parsing.Parser.Pos (Position)
import Zord.Syntax.Common (BinOp, Label, Name, UnOp, angles, braces, brackets, parens)
import Zord.Util ((<+>))

-- Types --

data Ty = TyInt
        | TyDouble
        | TyString
        | TyBool
        | TyTop
        | TyBot
        | TyArrow Ty Ty
        | TyAnd Ty Ty
        | TyRcd RcdTyList
        | TyVar Name
        | TyForall TyParamList Ty
        | TyApp Ty Ty
        | TyAbs Name Ty
        | TyTrait (Maybe Ty) Ty
        | TySort Ty (Maybe Ty)
        | TySig Name Name Ty
        | TyArray Ty

instance showTy :: Show Ty where
  show TyInt    = "Int"
  show TyDouble = "Double"
  show TyString = "String"
  show TyBool   = "Bool"
  show TyTop    = "Top"
  show TyBot    = "Bot"
  show (TyArrow t1 t2) = parens $ show t1 <+> "->" <+> show t2
  show (TyAnd t1 t2) = parens $ show t1 <+> "&" <+> show t2
  show (TyRcd xs) = braces $ showRcdTy xs
  show (TyVar a) = a
  show (TyForall xs t) = parens $
    "forall" <+> showTyParams xs <> "." <+> show t
  show (TyApp t1 t2) = parens $ show t1 <+> show t2
  show (TyAbs a t) = parens $ "\\" <> a <+> "->" <+> show t
  show (TyTrait ti to) = "Trait" <> angles (showMaybe "" ti " % " <> show to)
  show (TySort ti to) = angles $ show ti <> showMaybe " % " to ""
  show (TySig a b t) = parens $
    "\\" <> angles (a <+> "%" <+> b) <+> "->" <+> show t
  show (TyArray t) = brackets $ show t

derive instance eqTy :: Eq Ty

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
        | TmAnno Tm Ty
        | TmMerge Tm Tm
        | TmRcd (List RcdField)
        | TmPrj Tm Label
        | TmTApp Tm Ty
        | TmTAbs TyParamList Tm
        | TmLet Name Tm Tm
        | TmLetrec Name Ty Tm Tm
        | TmOpen Tm Tm
        | TmTrait SelfAnno (Maybe Ty) (Maybe Tm) Tm
        | TmNew Tm
        | TmForward Tm Tm
        | TmExclude Tm Ty
        | TmToString Tm
        | TmArray (Array Tm)
        | TmPos Position Tm
        | TmType Name (List Name) (List Name) (Maybe Ty) Ty Tm
        | TmDef Name TyParamList TmParamList (Maybe Ty) Tm Tm

data RcdField = RcdField Boolean Label TmParamList (Either Tm MethodPattern)
              | DefaultPattern MethodPattern
data MethodPattern = MethodPattern SelfAnno Label TmParamList Tm

instance showTm :: Show Tm where
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
  show (TmApp e1 e2) = parens $ show e1 <+> show e2
  show (TmAbs xs e) = parens $ "\\" <> showTmParams xs <> "->" <+> show e
  show (TmAnno e t) = parens $ show e <+> ":" <+> show t
  show (TmMerge e1 e2) = parens $ show e1 <+> "," <+> show e2
  show (TmRcd xs) = braces $ showRcdTm xs
  show (TmPrj e l) = show e <> "." <> l
  show (TmTApp e t) = parens $ show e <+> "@" <> show t
  show (TmTAbs xs e) = parens $ "/\\" <> showTyParams xs <> "." <+> show e
  show (TmLet x e1 e2) = parens $
    "let" <+> x <+> "=" <+> show e1 <+> "in" <+> show e2
  show (TmLetrec x t e1 e2) = parens $
    "letrec" <+> x <+> ":" <+> show t <+> "=" <+> show e1 <+> "in" <+> show e2
  show (TmOpen e1 e2) = parens $ "open" <+> show e1 <+> "in" <+> show e2
  show (TmTrait self sig e1 e2) = parens $ "trait" <> showSelf "" self <+>
    showMaybe "implements " sig " " <> showMaybe "inherits " e1 " " <>
    "=>" <+> show e2
  show (TmNew e) = parens $ "new" <+> show e
  show (TmForward e1 e2) = parens $ show e1 <+> "^" <+> show e2
  show (TmExclude e t) = parens $ show e <+> "\\" <+> show t
  show (TmToString e) = parens $ "toString" <+> show e
  show (TmArray arr) = brackets $ intercalate "; " (show <$> arr)
  show (TmPos _pos e) = show e
  show (TmType a sorts params t1 t2 e) = "type" <+> a <+>
    intercalate' " " (angles <$> sorts) <> intercalate' " " params <>
    showMaybe "extends " t1 " " <> "=" <+> show t2 <> ";" <+> show e
  show (TmDef x tyParams tmParams t e1 e2) = x <+>
    showTyParams tyParams <> showTmParams tmParams <>
    showMaybe ": " t " " <> "=" <+> show e1 <> ";" <+> show e2

-- Substitution --

-- TODO: capture-avoiding
tySubst :: Name -> Ty -> Ty -> Ty
tySubst a s (TyArrow t1 t2) = TyArrow (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyAnd t1 t2) = TyAnd (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyRcd xs) = TyRcd (rmap (tySubst a s) <$> xs)
tySubst a s (TyVar a') = if a == a' then s else TyVar a'
tySubst a s (TyForall xs t) = TyForall (rmap (map (tySubst a s)) <$> xs)
  (if any ((_ == a) <<< fst) xs then t else tySubst a s t)
tySubst a s (TyApp t1 t2) = TyApp (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyAbs a' t) = TyAbs a' (if a == a' then t else tySubst a s t)
tySubst a s (TyTrait ti to) = TyTrait (tySubst a s <$> ti) (tySubst a s to)
tySubst a s (TySort ti to) = TySort (tySubst a s ti) (tySubst a s <$> to)
tySubst a s (TySig a' b' t) = TySig a' b'
  (if a == a' || a == b' then t else tySubst a s t)
tySubst a s (TyArray t) = TyArray (tySubst a s t)
tySubst _ _ t = t

-- Helpers --

intercalate' :: forall f m. Foldable f => Monoid m => m -> f m -> m
intercalate' sep xs = if null xs then mempty else intercalate sep xs <> sep

showMaybe :: forall a. Show a => String -> Maybe a -> String -> String
showMaybe l m r = maybe "" (\x -> l <> show x <> r) m

type TyParamList = List TyParam
type TyParam = Tuple Name (Maybe Ty)

showTyParams :: TyParamList -> String
showTyParams params = intercalate' " " $ params <#> \param ->
  maybe (fst param) (\t -> parens $ fst param <+> "*" <+> show t) (snd param)

type TmParamList = List TmParam
data TmParam = TmParam Name (Maybe Ty) | WildCard

showTmParams :: TmParamList -> String
showTmParams params = intercalate' " " $ params <#> case _ of
  TmParam x (Just t) -> parens $ x <+> ":" <+> show t
  TmParam x Nothing -> x
  WildCard -> "{..}"

type RcdTyList = List (Tuple Label Ty)

showRcdTy :: RcdTyList -> String
showRcdTy xs = intercalate "; " $ xs <#> \(Tuple l t) -> l <+> ":" <+> show t

showRcdTm :: List RcdField -> String
showRcdTm xs = intercalate "; " $ xs <#> case _ of
  RcdField o l p e -> (if o then "override " else "") <> showField l p e
  DefaultPattern (MethodPattern self l p e) ->
    showSelf "_" self <> "." <> l <+> showTmParams p <> "=" <+> show e
  where showField :: Label -> TmParamList -> Either Tm MethodPattern -> String
        showField l p (Left e) = l <+> showTmParams p <> "=" <+> show e
        showField l p (Right (MethodPattern self l' p' e)) =
          parens (" " <> l <+> showTmParams p <> showSelf "" self) <>
          "." <> l' <+> showTmParams p' <> "=" <+> show e

type SelfAnno = Maybe (Tuple Name Ty)

showSelf :: String -> SelfAnno -> String
showSelf = flip maybe \(Tuple x t) -> brackets $ x <+> ":" <+> show t
