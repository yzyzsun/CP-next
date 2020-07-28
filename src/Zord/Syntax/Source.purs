module Zord.Syntax.Source where

import Prelude

import Data.List (List, intercalate)
import Data.Maybe (Maybe, maybe)
import Data.Tuple (Tuple(..), fst, snd)
import Text.Parsing.Parser.Pos (Position)
import Zord.Syntax.Common (BinOp, Label, Name, UnOp, braces, parens, (<+>))

-- Types --

data Ty = TyInt
        | TyDouble
        | TyString
        | TyBool
        | TyTop
        | TyBot
        | TyArr Ty Ty
        | TyAnd Ty Ty
        | TyRcd (RcdList Ty)
        | TyVar Name
        | TyForall ParamList Ty
        | TyApp Ty Ty
        | TyAbs Name Ty
        | TyTrait (Maybe Ty) Ty

instance showTy :: Show Ty where
  show TyInt    = "Int"
  show TyDouble = "Double"
  show TyString = "String"
  show TyBool   = "Bool"
  show TyTop    = "Top"
  show TyBot    = "Bot"
  show (TyArr t1 t2) = parens $ show t1 <+> "->" <+> show t2
  show (TyAnd t1 t2) = parens $ show t1 <+> "&" <+> show t2
  show (TyRcd xs) = braces $ showRcd ":" xs
  show (TyVar a) = a
  show (TyForall xs t) = parens $
    "forall" <+> showParams "*" xs <> "." <+> show t
  show (TyApp t1 t2) = parens $ show t1 <+> show t2
  show (TyAbs a t) = parens $ "\\" <> a <+> "->" <+> show t
  show (TyTrait ti to) = parens $
    "Trait" <+> showMaybe "" ti "#" <> show to

derive instance eqTy :: Eq Ty

-- Terms --

data Tm = TmInt Int
        | TmDouble Number
        | TmString String
        | TmBool Boolean
        | TmUnit
        | TmUnary UnOp Tm
        | TmBinary BinOp Tm Tm
        | TmIf Tm Tm Tm
        | TmVar Name
        | TmApp Tm Tm
        | TmAbs ParamList Tm
        | TmAnno Tm Ty
        | TmMerge Tm Tm
        | TmRcd (RcdList Tm)
        | TmPrj Tm Label
        | TmTApp Tm Ty
        | TmTAbs ParamList Tm
        | TmLet Name Tm Tm
        | TmLetrec Name Ty Tm Tm
        | TmOpen Tm Tm
        | TmTrait (Maybe (Tuple Name Ty)) (Maybe Tm) Tm
        | TmNew Tm
        | TmPos Position Tm

instance showTm :: Show Tm where
  show (TmInt i)    = show i
  show (TmDouble n) = show n
  show (TmString s) = show s
  show (TmBool b)   = show b
  show (TmUnit)     = "()"
  show (TmUnary op e) = show op <> show e
  show (TmBinary op e1 e2) = parens $ show e1 <+> show op <+> show e2
  show (TmIf e1 e2 e3) = parens $
    "if" <+> show e1 <+> "then" <+> show e2 <+> "else" <+> show e3
  show (TmVar x) = x
  show (TmApp e1 e2) = parens $ show e1 <+> show e2
  show (TmAbs xs e) = parens $ "\\" <> showParams ":" xs <+> "->" <+> show e
  show (TmAnno e t) = parens $ show e <+> ":" <+> show t
  show (TmMerge e1 e2) = parens $ show e1 <+> "," <+> show e2
  show (TmRcd xs) = braces $ showRcd "=" xs
  show (TmPrj e l) = show e <> "." <> l
  show (TmTApp e t) = parens $ show e <+> "@" <> show t
  show (TmTAbs xs e) = parens $ "/\\" <> showParams "*" xs <> "." <+> show e
  show (TmLet x e1 e2) = parens $
    "let" <+> x <+> "=" <+> show e1 <+> "in" <+> show e2
  show (TmLetrec x t e1 e2) = parens $
    "letrec" <+> x <+> ":" <+> show t <+> "=" <+> show e1 <+> "in" <+> show e2
  show (TmOpen e1 e2) = parens $ "open" <+> show e1 <+> "in" <+> show e2
  show (TmPos p e) = show e
  show (TmTrait self e1 e2) = parens $ "trait" <+>
    maybe "" (\(Tuple x t) -> "[" <> x <+> ":" <+> show t <> "] ") self <>
    showMaybe "inherits " e1 " " <> "=>" <+> show e2
  show (TmNew e) = "new" <+> show e

-- Helpers --

showMaybe :: forall a. Show a => String -> Maybe a -> String -> String
showMaybe l m r = maybe "" (\x -> l <> show x <> r) m

type ParamList = List (Tuple Name (Maybe Ty))

showParams :: String -> ParamList -> String
showParams s xs = intercalate " " (xs <#> \x ->
  maybe (fst x) (\t -> parens $ fst x <+> s <+> show t) (snd x)
)

type RcdList a = List (Tuple Label a)

showRcd :: forall a. Show a => String -> RcdList a -> String
showRcd s xs = intercalate "; " (xs <#> \x -> fst x <+> s <+> show (snd x))
