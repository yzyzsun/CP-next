module Zord.Desugar where

import Prelude

import Data.Bifunctor (rmap)
import Data.Either (Either(..))
import Data.List (List(..), foldr, singleton)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Zord.Syntax.Source (MethodPattern(..), RcdField(..), Tm(..), TmParam(..), Ty(..))
import Zord.Util (foldl1)

-- typing-related desugaring is delayed until type inference
desugar :: Tm -> Tm

desugar (TmAbs xs e) = foldr (\x s -> TmAbs (singleton x) s) (desugar e) xs
desugar (TmTAbs xs e) =
  foldr (\x s -> TmTAbs (singleton (rmap disjointness x)) s) (desugar e) xs
  where disjointness t = Just (fromMaybe TyTop t)
desugar (TmRcd Nil) = TmUnit
desugar (TmRcd xs) =
  foldl1 TmMerge (xs <#> \x -> TmRcd (singleton (desugarField x)))
  where
    desugarField :: RcdField -> RcdField
    -- TODO: override inner traits instead of outer ones
    desugarField (RcdField o l p f) =
      RcdField o l Nil $ Left $ desugar $ TmAbs p $ case f of
        Left e -> e
        Right pat -> desugarMethodPattern pat
    desugarField (DefaultPattern (MethodPattern self l p e)) =
      let self' = fromMaybe (Tuple "self" TyTop) self in
      DefaultPattern (MethodPattern (Just self') l Nil (desugar $ TmAbs p e))
desugar (TmTrait self sig e1 e2) =
  let self'@(Tuple x _) = fromMaybe (Tuple "self" TyTop) self in
  TmTrait (Just self') (Just (fromMaybe TyTop sig))
          (desugar <$> e1) (TmOpen (TmVar x) (desugar e2))
-- TODO: it may be better to always desugar def to letrec
desugar (TmDef x tyParams tmParams t e1 e2) = desugar $
  case t of Just t' -> TmLetrec x tyParams tmParams t' e1 e2
            Nothing -> TmLet x tyParams tmParams e1 e2
desugar (TmLet x tyParams tmParams e1 e2) =
  TmLet x Nil Nil (desugar (TmTAbs tyParams (TmAbs tmParams e1))) (desugar e2)
desugar (TmLetrec x tyParams tmParams t e1 e2) =
  TmLetrec x Nil Nil t' (desugar (TmTAbs tyParams (TmAbs tmParams e1))) (desugar e2)
  where t' = TyForall tyParams (foldr TyArrow t (tyOf <$> tmParams))
        tyOf = case _ of TmParam _ (Just ty) -> ty
                         TmParam _ Nothing -> TyBot
                         WildCard -> TyBot

desugar (TmUnary op e) = TmUnary op (desugar e)
desugar (TmBinary op e1 e2) = TmBinary op (desugar e1) (desugar e2)
desugar (TmIf e1 e2 e3) = TmIf (desugar e1) (desugar e2) (desugar e3)
desugar (TmApp e1 e2) = TmApp (desugar e1) (desugar e2)
desugar (TmAnno e t) = TmAnno (desugar e) t
desugar (TmMerge e1 e2) = TmMerge (desugar e1) (desugar e2)
desugar (TmPrj e l) = TmPrj (desugar e) l
desugar (TmTApp e t) = TmTApp (desugar e) t
desugar (TmOpen e1 e2) = TmOpen (desugar e1) (desugar e2)
desugar (TmNew e) = TmNew (desugar e)
desugar (TmForward e1 e2) = TmForward (desugar e1) (desugar e2)
desugar (TmExclude e t) = TmExclude (desugar e) t
desugar (TmFold t e) = TmFold t (desugar e)
desugar (TmUnfold t e) = TmUnfold t (desugar e)
desugar (TmToString e) = TmToString (desugar e)
desugar (TmArray arr) = TmArray (desugar <$> arr)
desugar (TmPos p e) = TmPos p (desugar e)
desugar (TmType a sorts params t e) = TmType a sorts params t (desugar e)
desugar e = e

desugarMethodPattern :: MethodPattern -> Tm
desugarMethodPattern (MethodPattern self l p e) =
  TmTrait self Nothing Nothing (TmRcd (singleton (RcdField false l p (Left e))))
