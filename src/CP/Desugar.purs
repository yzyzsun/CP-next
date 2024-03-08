module Language.CP.Desugar where

import Prelude

import Control.Alt ((<|>))
import Data.Bifunctor (rmap)
import Data.Either (Either(..), either)
import Data.List (List(..), foldr, singleton)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple.Nested ((/\))
import Language.CP.Syntax.Source (Bias(..), Def(..), MethodPattern(..), Prog(..), RcdField(..), Tm(..), TmParam(..), Ty(..))
import Language.CP.Util (foldl1)

-- typing-related desugaring is delayed until type inference
desugar :: Tm -> Tm

desugar (TmAbs xs e) = foldr (\x s -> TmAbs (singleton x) s) (desugar e) xs
desugar (TmTAbs xs e) =
  foldr (\x s -> TmTAbs (singleton (rmap disjointness x)) s) (desugar e) xs
  where disjointness t = Just (fromMaybe TyTop t)
desugar (TmRcd Nil) = TmRcd Nil
desugar (TmRcd xs) =
  foldl1 (TmMerge Neutral) (xs <#> \x -> TmRcd (singleton (desugarField x)))
  where
    desugarField :: RcdField -> RcdField
    -- TODO: override inner traits instead of outer ones
    desugarField (RcdField o l p f) =
      RcdField o l Nil $ Left $ desugar $ TmAbs p $ either identity deMP f
    -- desugaring of default patterns is done in `inferFromSig`
    desugarField def@(DefaultPattern _) = def
desugar (TmTrait (Just (x /\ t)) sig e1 e2) =
  TmTrait (Just (x /\ (t <|> sig))) (sig <|> Just TyTop)
          (desugar <$> e1) (desugar e2)
desugar (TmTrait Nothing sig e1 e2) =
  desugar (TmTrait (Just ("$self" /\ Just TyTop)) sig e1 e2)
desugar (TmLet x tyParams tmParams e1 e2) =
  TmLet x Nil Nil (desugar (TmTAbs tyParams (TmAbs tmParams e1))) (desugar e2)
desugar (TmLetrec x tyParams tmParams t e1 e2) =
  TmLetrec x Nil Nil t' (desugar (TmTAbs tyParams (TmAbs tmParams e1))) (desugar e2)
  where t' = TyForall tyParams (foldr TyArrow t (tyOf <$> tmParams))
        tyOf = case _ of TmParam _ (Just ty) -> ty
                         TmParam _ Nothing -> TyBot
                         WildCard _ -> TyBot

desugar (TmUnary op e) = TmUnary op (desugar e)
desugar (TmBinary op e1 e2) = TmBinary op (desugar e1) (desugar e2)
desugar (TmIf e1 e2 e3) = TmIf (desugar e1) (desugar e2) (desugar e3)
desugar (TmApp e1 e2) = TmApp (desugar e1) (desugar e2)
desugar (TmFix x e t) = TmFix x (desugar e) t
desugar (TmAnno e t) = TmAnno (desugar e) t
desugar (TmMerge bias e1 e2) = TmMerge bias (desugar e1) (desugar e2)
desugar (TmPrj e l) = TmPrj (desugar e) l
desugar (TmOptPrj e1 l e2) = TmOptPrj (desugar e1) l (desugar e2)
desugar (TmTApp e t) = TmTApp (desugar e) t
desugar (TmOpen e1 e2) = TmOpen (desugar e1) (desugar e2)
desugar (TmUpdate e xs) = TmUpdate (desugar e) (rmap desugar <$> xs)
desugar (TmNew e) = TmNew (desugar e)
desugar (TmForward e1 e2) = TmForward (desugar e1) (desugar e2)
desugar (TmExclude e t) = TmExclude (desugar e) t
desugar (TmRemoval e l) = TmRemoval (desugar e) l
desugar (TmDiff e1 e2) = TmDiff (desugar e1) (desugar e2)
desugar (TmRename e l1 l2) = TmRename (desugar e) l1 l2
desugar (TmFold t e) = TmFold t (desugar e)
desugar (TmUnfold t e) = TmUnfold t (desugar e)
desugar (TmRef e) = TmRef (desugar e)
desugar (TmDeref e) = TmDeref (desugar e)
desugar (TmAssign e1 e2) = TmAssign (desugar e1) (desugar e2)
desugar (TmSeq e1 e2) = TmSeq (desugar e1) (desugar e2)
desugar (TmToString e) = TmToString (desugar e)
desugar (TmArray arr) = TmArray (desugar <$> arr)
desugar (TmDoc e) = TmDoc (desugar e)
desugar (TmPos p e) = TmPos p (desugar e)
desugar e = e

deMP :: MethodPattern -> Tm
deMP (MethodPattern self l p e) =
  TmTrait self Nothing Nothing (TmRcd (singleton (RcdField false l p (Left e))))

desugarDef :: Def -> Def
desugarDef (TmDef x tyParams tmParams Nothing e) = TmDef x Nil Nil Nothing $
  desugar (TmTAbs tyParams (TmAbs tmParams e))
desugarDef (TmDef x tyParams tmParams (Just t) e) = TmDef x Nil Nil (Just t') $
  desugar (TmTAbs tyParams (TmAbs tmParams e))
  where t' = TyForall tyParams (foldr TyArrow t (tyOf <$> tmParams))
        tyOf = case _ of TmParam _ (Just ty) -> ty
                         TmParam _ Nothing -> TyBot
                         WildCard _ -> TyBot
desugarDef d = d

desugarProg :: Prog -> Prog
desugarProg (Prog defs e) = Prog (map desugarDef defs) (desugar e)