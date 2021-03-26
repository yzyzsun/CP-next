module Zord.Desugar where

import Prelude

import Data.Bifunctor (rmap)
import Data.Either (Either(..))
import Data.List (List(..), foldr, singleton)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Zord.Syntax.Common (foldl1)
import Zord.Syntax.Source (MethodPattern(..), RcdField(..), Tm(..), TmParam(..), Ty(..))

-- typing-related desugaring is delayed until type inference
desugar :: Tm -> Tm

desugar (TmAbs xs e) = foldr desugarParams (desugar e) xs
  where desugarParams x s = case x of
          TmParam _ _ -> abs x s
          WildCard -> abs (TmParam wildcard Nothing) (TmOpen (TmVar wildcard) s)
        abs param body = TmAbs (singleton param) body
        wildcard = "#wildcard"
desugar (TmTAbs xs e) =
  foldr (\x s -> TmTAbs (singleton (rmap disjointness x)) s) (desugar e) xs
  where disjointness t = Just (fromMaybe TyTop t)
desugar (TmRcd Nil) = TmUnit
desugar (TmRcd xs) =
  foldl1 TmMerge (xs <#> \x -> TmRcd (singleton (desugarField x)))
  where
    desugarField :: RcdField -> RcdField
    desugarField (RcdField o l (Left e)) = RcdField o l (Left (desugar e))
    desugarField (RcdField o l (Right (MethodPattern params self l' e))) =
      RcdField o l <<< Left <<< desugar $
        TmAbs params (TmTrait self Nothing Nothing
          (TmRcd (singleton (RcdField false l' (Left e)))))
    desugarField (DefaultPattern self l e) =
      let self' = fromMaybe (Tuple "self" TyTop) self in
      DefaultPattern (Just self') l (desugar e)
desugar (TmTrait self sig e1 e2) =
  let self'@(Tuple x _) = fromMaybe (Tuple "self" TyTop) self in
  TmTrait (Just self') (Just (fromMaybe TyTop sig))
          (desugar <$> e1) (TmOpen (TmVar x) (desugar e2))
desugar (TmType a sorts params (Just t1) t2 e) =
  TmType a sorts params Nothing (TyAnd t1 t2) (desugar e)
-- TODO: def should always be desugared to letrec
desugar (TmDef x tyParams tmParams t e1 e2) =
  case t of Just t' -> TmLetrec x (ty t') tm (desugar e2)
            Nothing -> TmLet x tm (desugar e2)
  where tm = desugar (TmTAbs tyParams (TmAbs tmParams e1))
        ty t' = TyForall tyParams (foldr TyArrow t' (tyOf <$> tmParams))
        -- TODO: param types should be inferred
        tyOf p = case p of TmParam _ (Just t') -> t'
                           TmParam _ Nothing -> TyTop
                           WildCard -> TyTop

desugar (TmUnary op e) = TmUnary op (desugar e)
desugar (TmBinary op e1 e2) = TmBinary op (desugar e1) (desugar e2)
desugar (TmIf e1 e2 e3) = TmIf (desugar e1) (desugar e2) (desugar e3)
desugar (TmApp e1 e2) = TmApp (desugar e1) (desugar e2)
desugar (TmAnno e t) = TmAnno (desugar e) t
desugar (TmMerge e1 e2) = TmMerge (desugar e1) (desugar e2)
desugar (TmPrj e l) = TmPrj (desugar e) l
desugar (TmTApp e t) = TmTApp (desugar e) t
desugar (TmLet x e1 e2) = TmLet x (desugar e1) (desugar e2)
desugar (TmLetrec x t e1 e2) = TmLetrec x t (desugar e1) (desugar e2)
desugar (TmOpen e1 e2) = TmOpen (desugar e1) (desugar e2)
desugar (TmNew e) = TmNew (desugar e)
desugar (TmArray arr) = TmArray (desugar <$> arr)
desugar (TmPos p e) = TmPos p (desugar e)
desugar (TmType a sorts params Nothing t2 e) =
  TmType a sorts params Nothing t2 (desugar e)
desugar e = e
