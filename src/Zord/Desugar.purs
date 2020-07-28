module Zord.Desugar where

import Prelude

import Data.Bifunctor (rmap)
import Data.List (List(..), foldr, singleton)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..), fst, snd)
import Zord.Syntax.Common (foldl1)
import Zord.Syntax.Core as C
import Zord.Syntax.Source as S

-- typing-related desugaring is delayed until synthesizing
desugar :: S.Tm -> S.Tm

desugar (S.TmAbs xs e) = foldr (\x s -> S.TmAbs (singleton x) s) (desugar e) xs
desugar (S.TmTAbs xs e) =
  foldr (\x s -> S.TmTAbs (singleton (rmap disjointness x)) s) (desugar e) xs
  where disjointness t = Just (fromMaybe S.TyTop t)
desugar (S.TmRcd Nil) = S.TmUnit
desugar (S.TmRcd xs) =
  foldl1 S.TmMerge (xs <#> \x -> S.TmRcd (singleton (rmap desugar x)))
desugar (S.TmTrait self e1 e2) =
  let self'@(Tuple x _) = fromMaybe (Tuple "self" S.TyTop) self in
  S.TmTrait (Just self') (desugar <$> e1) (S.TmOpen (S.TmVar x) (desugar e2))

desugar (S.TmUnary op e) = S.TmUnary op (desugar e)
desugar (S.TmBinary op e1 e2) = S.TmBinary op (desugar e1) (desugar e2)
desugar (S.TmIf e1 e2 e3) = S.TmIf (desugar e1) (desugar e2) (desugar e3)
desugar (S.TmApp e1 e2) = S.TmApp (desugar e1) (desugar e2)
desugar (S.TmAnno e t) = S.TmAnno (desugar e) t
desugar (S.TmMerge e1 e2) = S.TmMerge (desugar e1) (desugar e2)
desugar (S.TmPrj e l) = S.TmPrj (desugar e) l
desugar (S.TmTApp e t) = S.TmTApp (desugar e) t
desugar (S.TmLet x e1 e2) = S.TmLet x (desugar e1) (desugar e2)
desugar (S.TmLetrec x t e1 e2) = S.TmLetrec x t (desugar e1) (desugar e2)
desugar (S.TmOpen e1 e2) = S.TmOpen (desugar e1) (desugar e2)
desugar (S.TmNew e) = S.TmNew (desugar e)
desugar (S.TmPos p e) = S.TmPos p (desugar e)
desugar e = e

transform :: S.Ty -> C.Ty
transform S.TyInt    = C.TyInt
transform S.TyDouble = C.TyDouble
transform S.TyString = C.TyString
transform S.TyBool   = C.TyBool
transform S.TyTop    = C.TyTop
transform S.TyBot    = C.TyBot
transform (S.TyArr t1 t2) = C.TyArr (transform t1) (transform t2) false
transform (S.TyAnd t1 t2) = C.TyAnd (transform t1) (transform t2)
transform (S.TyRcd Nil) = C.TyTop
transform (S.TyRcd xs) =
  foldl1 C.TyAnd (xs <#> \x -> C.TyRcd (fst x) (transform (snd x)))
transform (S.TyVar a) = C.TyVar a
transform (S.TyForall xs t) =
  foldr (\x s -> C.TyForall (fst x) (disjointness (snd x)) s) (transform t) xs
  where disjointness :: Maybe S.Ty -> C.Ty
        disjointness (Just s) = transform s
        disjointness Nothing  = C.TyTop
transform (S.TyApp t1 t2) = C.TyApp (transform t1) (transform t2)
transform (S.TyAbs a t) = C.TyAbs a (transform t)
transform (S.TyTrait (Just ti) to) = C.TyArr (transform ti) (transform to) true
transform (S.TyTrait Nothing to) = C.TyArr C.TyTop (transform to) true
