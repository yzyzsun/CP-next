module Zord.Desugar where

import Prelude

import Data.Bifunctor (rmap)
import Data.List (List(..), foldr, singleton)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Zord.Syntax.Common (foldl1)
import Zord.Syntax.Source (Tm(..), Ty(..))

-- typing-related desugaring is delayed until synthesizing
desugar :: Tm -> Tm

desugar (TmAbs xs e) = foldr (\x s -> TmAbs (singleton x) s) (desugar e) xs
desugar (TmTAbs xs e) =
  foldr (\x s -> TmTAbs (singleton (rmap disjointness x)) s) (desugar e) xs
  where disjointness t = Just (fromMaybe TyTop t)
desugar (TmRcd Nil) = TmUnit
desugar (TmRcd xs) =
  foldl1 TmMerge (xs <#> \x -> TmRcd (singleton (rmap desugar x)))
desugar (TmTrait self e1 e2) =
  let self'@(Tuple x _) = fromMaybe (Tuple "self" TyTop) self in
  TmTrait (Just self') (desugar <$> e1) (TmOpen (TmVar x) (desugar e2))

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
desugar (TmPos p e) = TmPos p (desugar e)
desugar e = e
