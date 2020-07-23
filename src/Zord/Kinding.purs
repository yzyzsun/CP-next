module Zord.Kinding where

import Prelude

import Zord.Context (Typing, addTyBind, lookupTyBind, throwTypeError)
import Zord.Syntax.Core (Kind(..), Name, Ty(..), (<+>))

kindOf :: Ty -> Typing Kind
kindOf TyInt    = pure KnStar
kindOf TyDouble = pure KnStar
kindOf TyString = pure KnStar
kindOf TyBool   = pure KnStar
kindOf TyTop    = pure KnStar
kindOf TyBot    = pure KnStar
kindOf (TyArr t1 t2) = do
  checkProperTy t1
  checkProperTy t2
  pure KnStar
kindOf (TyAnd t1 t2) = do
  checkProperTy t1
  checkProperTy t2
  pure KnStar
kindOf (TyRec l t) = do
  checkProperTy t
  pure KnStar
kindOf (TyVar a) = lookupTyBind a $> KnStar
kindOf (TyForall a td t) = addTyBind a td $ kindOf t
kindOf (TyApp t1 t2) = do
  checkProperTy t2
  k1 <- kindOf t1
  case k1 of KnArr KnStar kret -> pure kret
             _ -> throwTypeError $ show k1 <+> "is not applicable"
kindOf (TyAbs a t) = do
  k <- addTyBind a TyTop $ kindOf t
  pure $ KnArr KnStar k

checkProperTy :: Ty -> Typing Unit
checkProperTy t = do
  k <- kindOf t
  if k == KnStar then pure unit
  else throwTypeError $ show t <+> "is not a proper type"

tyAEq :: Ty -> Ty -> Boolean
tyAEq l r = case tyBReduce l, tyBReduce r of
  TyArr t1 t2, TyArr t3 t4 -> t1 === t3 && t2 === t4
  TyAnd t1 t2, TyAnd t3 t4 -> t1 === t3 && t2 === t4
  TyRec l1 t1, TyRec l2 t2 -> l1 == l2 && t1 === t2
  TyForall a1 td1 t1, TyForall a2 td2 t2 -> td1 === td2 &&
                                            t1 === tySubst a2 (TyVar a1) t2
  t1, t2 | t1 == t2  -> true
         | otherwise -> false

infix 4 tyAEq as ===

tyBReduce :: Ty -> Ty
tyBReduce (TyArr t1 t2) = TyArr (tyBReduce t1) (tyBReduce t2)
tyBReduce (TyAnd t1 t2) = TyAnd (tyBReduce t1) (tyBReduce t2)
tyBReduce (TyRec l t) = TyRec l (tyBReduce t)
tyBReduce (TyForall a td t) = TyForall a (tyBReduce td) (tyBReduce t)
tyBReduce (TyApp (TyAbs a t1) t2) = tyBReduce (tySubst a t2 t1)
tyBReduce t = t

-- TODO: capture-avoiding
tySubst :: Name -> Ty -> Ty -> Ty
tySubst a s (TyArr t1 t2) = TyArr (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyAnd t1 t2) = TyAnd (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyRec l t) = TyRec l (tySubst a s t)
tySubst a s (TyVar a') = if a == a' then s else TyVar a'
tySubst a s (TyForall a' td t) =
  TyForall a' (tySubst a s td) (if a == a' then t else tySubst a s t)
tySubst _ _ t = t
