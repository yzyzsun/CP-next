module Zord.Typing where

import Prelude

import Data.Either (Either(..))
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), lookup)
import Zord.Subtyping (isTopLike, (<:))
import Zord.Syntax (BinOp(..), Binding(..), Ctx, Expr(..), Name, Ty(..), UnOp(..))

data TypeError = TypeError String

instance showTypeError :: Show TypeError where
  show (TypeError str) = "TypeError: " <> str

typeOf :: Ctx -> Expr -> Either TypeError Ty
typeOf _ (TmInt _)    = Right TyInt
typeOf _ (TmDouble _) = Right TyDouble
typeOf _ (TmString _) = Right TyString
typeOf _ (TmBool _)   = Right TyBool
typeOf _ (TmUnit)     = Right TyTop
typeOf ctx (TmUnary Neg e)  = do
  t <- typeOf ctx e
  case t of TyInt    -> Right TyInt
            TyDouble -> Right TyDouble
            _        -> Left <<< TypeError $ "Neg is not defined for " <> show t
typeOf ctx (TmUnary Not e)  = do
  t <- typeOf ctx e
  case t of TyBool -> Right TyBool
            _      -> Left <<< TypeError $ "Not is not defined for " <> show t
typeOf ctx (TmBinary (Arith _) e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  case t1, t2 of TyInt,    TyInt    -> Right TyInt
                 TyDouble, TyDouble -> Right TyDouble
                 _,        _        -> Left <<< TypeError $ "\
    \ArithOp is not defined between " <> show t1 <> " and " <> show t2
typeOf ctx (TmBinary (Comp _) e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  case t1, t2 of TyInt,    TyInt    -> Right TyBool
                 TyDouble, TyDouble -> Right TyBool
                 TyString, TyString -> Right TyBool
                 TyBool,   TyBool   -> Right TyBool
                 _,        _        -> Left <<< TypeError $ "\
    \CompOp is not defined between " <> show t1 <> " and " <> show t2
typeOf ctx (TmBinary (Logic _) e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  case t1, t2 of TyBool, TyBool -> Right TyBool
                 _,      _      -> Left <<< TypeError $ "\
    \LogicOp is not defined between " <> show t1 <> " and " <> show t2
typeOf ctx (TmVar x) = case lookup x ctx of
  Just (TmBinding t) -> Right t
  _ -> Left <<< TypeError $ "Variable " <> show x <> " is not defined"
typeOf ctx (TmApp e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  appSS Nil t1 t2
typeOf ctx (TmAbs x e targ tret) = typeOf ctx' e >>= \tret' ->
  if tret' <: tret then Right $ TyArr targ tret else Left <<< TypeError $
    "The return type " <> show tret <> " is not a supertype of " <> show tret'
  where ctx' = Tuple x (TmBinding targ) : ctx
typeOf ctx (TmFix x e t) = typeOf ctx' e >>= \t' ->
  if t' <: t then Right t else Left <<< TypeError $
    "Fixpoint is annotated as " <> show t <> ", but got " <> show t'
  where ctx' = Tuple x (TmBinding t) : ctx
typeOf ctx (TmAnno e t) = typeOf ctx e >>= \t' ->
  if t' <: t then Right t else Left <<< TypeError $
    "The annotated type " <> show t <> " is not a supertype of " <> show t'
typeOf ctx (TmMerge e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  disjoint ctx t1 t2
  Right $ TyAnd t1 t2
typeOf ctx (TmRec l e) = TyRec l <$> typeOf ctx e
typeOf ctx (TmPrj e l) = typeOf ctx e >>= \t -> appSS Nil t (TyRec l TyTop)
typeOf ctx (TmTApp e ta) = typeOf ctx e >>= \tf -> appSS ctx tf ta
typeOf ctx (TmTAbs a td e t) = typeOf ctx' e >>= \t' ->
  if t' <: t then Right $ TyForall a td t else Left <<< TypeError $
    "The return type " <> show t <> " is not a supertype of " <> show t'
  where ctx' = Tuple a (TyBinding td) : ctx
typeOf ctx (TmIf e1 e2 e3) = do
  t1 <- typeOf ctx e1
  if t1 == TyBool then do
    t2 <- typeOf ctx e2
    t3 <- typeOf ctx e3
    if t2 == t3 then Right t2 else Left <<< TypeError $
      "If-branches expected the same type, but got " <>
      show t2 <> " and " <> show t3
  else Left <<< TypeError $
    "If-condition expected Bool, but got " <> show t1
typeOf ctx (TmLet x e1 e2) = typeOf ctx e1 >>= \t1 ->
  typeOf (Tuple x (TmBinding t1) : ctx) e2
typeOf ctx (TmOpen e1 e2) = do
  t1 <- typeOf ctx e1
  ctx' <- open t1
  typeOf (ctx' <> ctx) e2
  where open :: Ty -> Either TypeError Ctx
        open (TyRec l t) = Right $ Tuple l (TmBinding t) : Nil
        open (TyAnd t1 t2) = do ctx1 <- open t1
                                ctx2 <- open t2
                                Right $ ctx1 <> ctx2
        open t = Left <<< TypeError $ show t <> " cannot be opened"

appSS :: Ctx -> Ty -> Ty -> Either TypeError Ty
appSS _ TyTop _ = Right TyTop
appSS _ f@(TyArr targ tret) t | t <: targ = Right tret
                              | otherwise = Left <<< TypeError $
  show f <> " expected a subtype of its parameter type, but got " <> show t
appSS _ r@(TyRec l t) (TyRec l' _) | l == l'   = Right t
                                   | otherwise = Left <<< TypeError $
  show r <> " has no label named " <> show l'
appSS ctx (TyForall a td t) ta = disjoint ctx ta td $> tySubst a ta t
appSS ctx (TyAnd t1 t2) t = do
  t1' <- appSS ctx t1 t
  t2' <- appSS ctx t2 t
  Right $ TyAnd t1' t2'
appSS _ t _ = Left <<< TypeError $ show t <> " is not applicable"

disjoint :: Ctx -> Ty -> Ty -> Either TypeError Unit
disjoint _ t _ | isTopLike t = Right unit
disjoint _ _ t | isTopLike t = Right unit
disjoint ctx (TyArr _ t1) (TyArr _ t2) = disjoint ctx t1 t2
disjoint ctx (TyAnd t1 t2) t3 = disjoint ctx t1 t3 *> disjoint ctx t2 t3
disjoint ctx t1 (TyAnd t2 t3) = disjoint ctx (TyAnd t2 t3) t1
disjoint ctx (TyRec l1 t1) (TyRec l2 t2) | l1 == l2 = disjoint ctx t1 t2
                                         | otherwise = Right unit
disjoint ctx (TyVar a) t = case lookup a ctx of
  Just (TyBinding t') -> if t' <: t then Right unit else Left <<< TypeError $
    "Type " <> show a <> " is not disjoint from " <> show t
  _ -> Left <<< TypeError $ "Type " <> show a <> " is not defined"
disjoint ctx t (TyVar a) = disjoint ctx (TyVar a) t
disjoint ctx (TyForall a1 td1 t1) (TyForall a2 td2 t2) =
  disjoint ctx' t1 (tySubst a2 (TyVar a1) t2)
    where ctx' = Tuple a1 (TyBinding (TyAnd td1 td2)) : ctx
disjoint _ t1 t2 | t1 /= t2  = Right unit
                 | otherwise = Left <<< TypeError $
  show t1 <> " and " <> show t2 <> " are not disjoint"

tySubst :: Name -> Ty -> Ty -> Ty
tySubst a s (TyArr t1 t2) = TyArr (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyAnd t1 t2) = TyAnd (tySubst a s t1) (tySubst a s t2)
tySubst a s (TyRec l t) = TyRec l (tySubst a s t)
tySubst a s (TyVar a') = if a == a' then s else TyVar a'
tySubst a s (TyForall a' td t) =
  TyForall a' (tySubst a s td) (if a == a' then t else tySubst a s t)
tySubst _ _ t = t
