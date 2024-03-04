module Language.CP.Subtyping where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Syntax.Core (Ty(..), tySubst)

subtype :: Ty -> Ty -> Boolean
subtype TyBot _ = true
subtype _ t | isTopLike t = true
subtype t1 t2 | Just (t3 /\ t4) <- split t2 = t1 <: t3 && t1 <: t4
subtype (TyArrow targ1 tret1 _) (TyArrow targ2 tret2 _) = targ2 <: targ1 &&
                                                          tret1 <: tret2
subtype (TyAnd t1 t2) t3 = t1 <: t3 || t2 <: t3
subtype _ (TyRcd _ _ true) = true
subtype (TyRcd l1 t1 false) (TyRcd l2 t2 false) = l1 == l2 && t1 <: t2
subtype (TyForall a1 td1 t1) (TyForall a2 td2 t2) =
  td2 <: td1 && t1 <: tySubst a2 (TyVar a1) t2
subtype (TyRec a1 t1) (TyRec a2 t2) =
  tySubst a1 (TyRcd a1 t1 false) t1 <: tySubst a2 (TyRcd a1 t2' false) t2
  where t2' = tySubst a2 (TyVar a1) t2
subtype (TyRef t1) (TyRef t2) = t1 <: t2 && t2 <: t1
subtype (TyArray t1) (TyArray t2) = t1 <: t2
subtype t1 t2 | t1 == t2  = true
              | otherwise = false

infix 4 subtype as <:

supertype :: Ty -> Ty -> Boolean
supertype = flip subtype

infix 4 supertype as :>

isTopLike :: Ty -> Boolean
isTopLike TyTop = true
isTopLike (TyArrow _ t _) = isTopLike t
isTopLike (TyAnd t1 t2) = isTopLike t1 && isTopLike t2
isTopLike (TyRcd _ t _) = isTopLike t
isTopLike (TyForall _ _ t) = isTopLike t
isTopLike (TyRec _ t) = isTopLike t
isTopLike _ = false

-- TODO: add distributive subtyping to recursive types
split :: Ty -> Maybe (Ty /\ Ty)
split (TyAnd t1 t2) = Just $ t1 /\ t2
split (TyArrow targ tret b) = split tret >>= \(tret1 /\ tret2) ->
  Just $ TyArrow targ tret1 b /\ TyArrow targ tret2 b
split (TyRcd l t b) = split t >>= \(t1 /\ t2) ->
  Just $ TyRcd l t1 b /\ TyRcd l t2 b
split (TyForall a td t) = split t >>= \(t1 /\ t2) ->
  Just $ TyForall a td t1 /\ TyForall a td t2
split _ = Nothing

aeq :: Ty -> Ty -> Boolean
aeq (TyArrow t1 t2 _) (TyArrow t3 t4 _) = t1 === t3 && t2 === t4
aeq (TyAnd t1 t2) (TyAnd t3 t4) = t1 === t3 && t2 === t4
aeq (TyRcd l1 t1 opt1) (TyRcd l2 t2 opt2) =
  l1 == l2 && t1 === t2 && opt1 == opt2
aeq (TyForall a1 td1 t1) (TyForall a2 td2 t2) =
  td1 === td2 && t1 === tySubst a2 (TyVar a1) t2
aeq (TyRec a1 t1) (TyRec a2 t2) = t1 === tySubst a2 (TyVar a1) t2
aeq (TyRef t1) (TyRef t2) = t1 === t2
aeq (TyArray t1) (TyArray t2) = t1 === t2
aeq t1 t2 | t1 == t2  = true
          | otherwise = false

infix 4 aeq as ===
