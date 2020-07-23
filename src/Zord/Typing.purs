module Zord.Typing where

import Prelude

import Zord.Context (Pos(..), Typing, addTmBind, addTyBind, emptyCtx, lookupTmBind, lookupTyBind, openRecInCtx, setPos, throwTypeError)
import Zord.Kinding (tySubst, (===))
import Zord.Subtyping (isTopLike, (<:))
import Zord.Syntax.Core (BinOp(..), Expr(..), Ty(..), UnOp(..), (<+>))

typeOf :: Expr -> Typing Ty
typeOf (TmInt _)    = pure TyInt
typeOf (TmDouble _) = pure TyDouble
typeOf (TmString _) = pure TyString
typeOf (TmBool _)   = pure TyBool
typeOf (TmUnit)     = pure TyTop
typeOf (TmUnary Neg e) = do
  t <- typeOf e
  case t of TyInt    -> pure TyInt
            TyDouble -> pure TyDouble
            _        -> throwTypeError $ "Neg is not defined for" <+> show t
typeOf (TmUnary Not e) = do
  t <- typeOf e
  case t of TyBool -> pure TyBool
            _      -> throwTypeError $ "Not is not defined for" <+> show t
typeOf (TmBinary (Arith _) e1 e2) = do
  t1 <- typeOf e1
  t2 <- typeOf e2
  case t1, t2 of TyInt,    TyInt    -> pure TyInt
                 TyDouble, TyDouble -> pure TyDouble
                 _,        _        -> throwTypeError $ "\
    \ArithOp is not defined between" <+> show t1 <+> "and" <+> show t2
typeOf (TmBinary (Comp _) e1 e2) = do
  t1 <- typeOf e1
  t2 <- typeOf e2
  case t1, t2 of TyInt,    TyInt    -> pure TyBool
                 TyDouble, TyDouble -> pure TyBool
                 TyString, TyString -> pure TyBool
                 TyBool,   TyBool   -> pure TyBool
                 _,        _        -> throwTypeError $ "\
    \CompOp is not defined between" <+> show t1 <+> "and" <+> show t2
typeOf (TmBinary (Logic _) e1 e2) = do
  t1 <- typeOf e1
  t2 <- typeOf e2
  case t1, t2 of TyBool, TyBool -> pure TyBool
                 _,      _      -> throwTypeError $ "\
    \LogicOp is not defined between" <+> show t1 <+> "and" <+> show t2
typeOf (TmVar x) = lookupTmBind x
typeOf (TmApp e1 e2) = do
  t1 <- typeOf e1
  t2 <- typeOf e2
  emptyCtx $ appSS t1 t2
typeOf (TmAbs x e targ tret) = do
  tret' <- addTmBind x targ $ typeOf e
  if tret' <: tret then pure $ TyArr targ tret else throwTypeError $
    "the return type" <+> show tret <+> "is not a supertype of" <+> show tret'
typeOf (TmFix x e t) = do
  t' <- addTmBind x t $ typeOf e
  if t' <: t then pure t else throwTypeError $
    "fixpoint is annotated as" <+> show t <> ", but got" <+> show t'
typeOf (TmAnno e t) = do
  t' <- typeOf e
  if t' <: t then pure t else throwTypeError $
    "the annotated type" <+> show t <+> "is not a supertype of" <+> show t'
typeOf (TmMerge e1 e2) = do
  t1 <- typeOf e1
  t2 <- typeOf e2
  disjoint t1 t2
  pure $ TyAnd t1 t2
typeOf (TmRec l e) = TyRec l <$> typeOf e
typeOf (TmPrj e l) = do
  t <- typeOf e
  emptyCtx $ appSS t (TyRec l TyTop)
typeOf (TmTApp e ta) = do
  tf <- typeOf e
  appSS tf ta
typeOf (TmTAbs a td e t) = do
  t' <- addTyBind a td $ typeOf e
  if t' <: t then pure $ TyForall a td t else throwTypeError $
    "the return type" <+> show t <+> "is not a supertype of" <+> show t'
typeOf (TmIf e1 e2 e3) = do
  t1 <- typeOf e1
  if t1 === TyBool then do
    t2 <- typeOf e2
    t3 <- typeOf e3
    if t2 === t3 then pure t2
    else throwTypeError $ "if-branches expected the same type, but got" <+>
                          show t2 <+> "and" <+> show t3
  else throwTypeError $ "if-condition expected Bool, but got" <+> show t1
typeOf (TmLet x e1 e2) = do
  t1 <- typeOf e1
  addTmBind x t1 $ typeOf e2
typeOf (TmOpen e1 e2) = do
  t1 <- typeOf e1
  openRecInCtx t1 $ typeOf e2
typeOf (TmPos p e) = setPos (Pos p e) $ typeOf e

appSS :: Ty -> Ty -> Typing Ty
appSS TyTop _ = pure TyTop
appSS f@(TyArr targ tret) t | t <: targ = pure tret
                            | otherwise = throwTypeError $
  show f <+> "expected a subtype of its parameter type, but got" <+> show t
appSS r@(TyRec l t) (TyRec l' _) | l == l'   = pure t
                                 | otherwise = throwTypeError $
  show r <+> "has no label named" <+> show l'
appSS (TyForall a td t) ta = disjoint ta td $> tySubst a ta t
appSS (TyAnd t1 t2) t = do
  t1' <- appSS t1 t
  t2' <- appSS t2 t
  pure $ TyAnd t1' t2'
appSS t _ = throwTypeError $ show t <+> "is not applicable"

disjoint :: Ty -> Ty -> Typing Unit
disjoint t _ | isTopLike t = pure unit
disjoint _ t | isTopLike t = pure unit
disjoint (TyArr _ t1) (TyArr _ t2) = disjoint t1 t2
disjoint (TyAnd t1 t2) t3 = disjoint t1 t3 *> disjoint t2 t3
disjoint t1 (TyAnd t2 t3) = disjoint (TyAnd t2 t3) t1
disjoint (TyRec l1 t1) (TyRec l2 t2) | l1 == l2 = disjoint t1 t2
                                     | otherwise = pure unit
disjoint (TyVar a) t = do
  t' <- lookupTyBind a
  if t' <: t then pure unit else throwTypeError $
    "type variable" <+> show a <+> "is not disjoint from" <+> show t
disjoint t (TyVar a) = disjoint (TyVar a) t
disjoint (TyForall a1 td1 t1) (TyForall a2 td2 t2) =
  addTyBind a1 (TyAnd td1 td2) $ disjoint t1 (tySubst a2 (TyVar a1) t2)
disjoint t1 t2 | t1 /= t2  = pure unit
               | otherwise = throwTypeError $
  show t1 <+> "and" <+> show t2 <+> "are not disjoint"
