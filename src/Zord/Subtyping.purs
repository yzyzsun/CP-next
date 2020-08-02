module Zord.Subtyping where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Zord.Syntax.Core (Ty(..), tySubst)

subtype :: Ty -> Ty -> Boolean
subtype TyBot _ = true
subtype _ t | isTopLike t = true
subtype t1 t2 | Just (Tuple t3 t4) <- split t2 = t1 <: t3 && t1 <: t4
subtype (TyArr targ1 tret1 _) (TyArr targ2 tret2 _) = targ2 <: targ1 &&
                                                      tret1 <: tret2
subtype (TyAnd t1 t2) t3 = t1 <: t3 || t2 <: t3
subtype (TyRcd l1 t1) (TyRcd l2 t2) = l1 == l2 && t1 <: t2
subtype (TyForall a1 td1 t1) (TyForall a2 td2 t2) =
  td2 <: td1 && tySubst a1 freshVar t1 <: tySubst a2 freshVar t2
  where freshVar = TyVar "__fresh__"
subtype t1 t2 | t1 == t2  = true
              | otherwise = false

infix 4 subtype as <:

supertype :: Ty -> Ty -> Boolean
supertype = flip subtype

infix 4 supertype as :>

isTopLike :: Ty -> Boolean
isTopLike TyTop = true
isTopLike (TyArr _ t _) = isTopLike t
isTopLike (TyAnd t1 t2) = isTopLike t1 && isTopLike t2
isTopLike (TyRcd _ t) = isTopLike t
isTopLike (TyForall _ _ t) = isTopLike t
isTopLike _ = false

split :: Ty -> Maybe (Tuple Ty Ty)
split (TyAnd t1 t2) = Just $ Tuple t1 t2
split (TyArr targ tret b) = split tret >>= \(Tuple tret1 tret2) ->
  Just $ Tuple (TyArr targ tret1 b) (TyArr targ tret2 b)
split (TyRcd l t) = split t >>= \(Tuple t1 t2) ->
  Just $ Tuple (TyRcd l t1) (TyRcd l t2)
split (TyForall a td t) = split t >>= \(Tuple t1 t2) ->
  Just $ Tuple (TyForall a td t1) (TyForall a td t2)
split _ = Nothing

aeq :: Ty -> Ty -> Boolean
aeq (TyArr t1 t2 _) (TyArr t3 t4 _) = t1 === t3 && t2 === t4
aeq (TyAnd t1 t2) (TyAnd t3 t4) = t1 === t3 && t2 === t4
aeq (TyRcd l1 t1) (TyRcd l2 t2) = l1 == l2 && t1 === t2
aeq (TyForall a1 td1 t1) (TyForall a2 td2 t2) =
  td1 === td2 && tySubst a1 freshVar t1 === tySubst a2 freshVar t2
  where freshVar = TyVar "__fresh__"
aeq t1 t2 | t1 == t2  = true
          | otherwise = false

infix 4 aeq as ===
