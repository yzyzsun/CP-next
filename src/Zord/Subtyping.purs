module Zord.Subtyping where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Zord.Kinding (tyBReduce, tySubst)
import Zord.Syntax.Core (Ty(..))

subtype :: Ty -> Ty -> Boolean
subtype l r = case tyBReduce l, tyBReduce r of
  TyBot, _ -> true
  _, t | isTopLike t -> true
  t1, t2 | Just (Tuple t3 t4) <- split t2 -> t1 <: t3 && t1 <: t4
  TyArr targ1 tret1, TyArr targ2 tret2 -> targ2 <: targ1 && tret1 <: tret2
  TyAnd t1 t2, t3 -> t1 <: t3 || t2 <: t3
  TyRec l1 t1, TyRec l2 t2 -> l1 == l2 && t1 <: t2
  TyForall a1 td1 t1, TyForall a2 td2 t2 -> td2 <: td1 &&
                                            t1 <: tySubst a2 (TyVar a1) t2
  t1, t2 | t1 == t2  -> true
         | otherwise -> false

infix 4 subtype as <:

supertype :: Ty -> Ty -> Boolean
supertype = flip subtype

infix 4 supertype as :>

isTopLike :: Ty -> Boolean
isTopLike TyTop = true
isTopLike (TyArr _ t) = isTopLike t
isTopLike (TyAnd t1 t2) = isTopLike t1 && isTopLike t2
isTopLike (TyRec _ t) = isTopLike t
isTopLike (TyForall _ _ t) = isTopLike t
isTopLike _ = false

split :: Ty -> Maybe (Tuple Ty Ty)
split (TyAnd t1 t2) = Just $ Tuple t1 t2
split (TyArr targ tret) = split tret >>= \(Tuple tret1 tret2) ->
  Just $ Tuple (TyArr targ tret1) (TyArr targ tret2)
split (TyRec l t) = split t >>= \(Tuple t1 t2) ->
  Just $ Tuple (TyRec l t1) (TyRec l t2)
split (TyForall a td t) = split t >>= \(Tuple t1 t2) ->
  Just $ Tuple (TyForall a td t1) (TyForall a td t2)
split _ = Nothing
