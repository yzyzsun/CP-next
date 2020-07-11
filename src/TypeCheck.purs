module Zord.TypeCheck where

import Prelude

import Data.Either (Either(..))
import Data.List ((:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), lookup)
import Zord.Subtyping (isTopLike, (<:))
import Zord.Syntax (BinOp(..), Ctx, CtxEntry(..), Expr(..), Name, Ty(..), UnOp(..))

data TypeError = TypeError String

instance showTypeError :: Show TypeError where
  show (TypeError str) = "TypeError: " <> str

typeOf :: Ctx -> Expr -> Either TypeError Ty
typeOf _ (IntLit _)    = Right Integer
typeOf _ (DoubleLit _) = Right Double
typeOf _ (StrLit _)    = Right Str
typeOf _ (BoolLit _)   = Right Bool
typeOf _ (UnitLit)     = Right Top
typeOf ctx (Unary Neg e)  = do
  t <- typeOf ctx e
  case t of Integer -> Right Integer
            Double  -> Right Double
            _       -> Left <<< TypeError $ "Neg is not defined for " <> show t
typeOf ctx (Unary Not e)  = do
  t <- typeOf ctx e
  case t of Bool -> Right Bool
            _    -> Left <<< TypeError $ "Not is not defined for " <> show t
typeOf ctx (Binary (Arith _) e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  case t1, t2 of Integer, Integer -> Right Integer
                 Double,  Double  -> Right Double
                 _,       _       -> Left <<< TypeError $ "\
    \Arith is not defined between " <> show t1 <> " and " <> show t2
typeOf ctx (Binary (Comp _) e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  case t1, t2 of Integer, Integer -> Right Bool
                 Double,  Double  -> Right Bool
                 Str,     Str     -> Right Bool
                 Bool,    Bool    -> Right Bool
                 _,       _       -> Left <<< TypeError $ "\
    \Comp is not defined between " <> show t1 <> " and " <> show t2
typeOf ctx (Binary (Logic _) e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  case t1, t2 of Bool, Bool -> Right Bool
                 _,    _    -> Left <<< TypeError $ "\
    \Logic is not defined between " <> show t1 <> " and " <> show t2
typeOf ctx (Var x) = case lookup x ctx of
  Just (TermEntry t) -> Right t
  _ -> Left <<< TypeError $ "Variable " <> show x <> " is not defined"
typeOf ctx (App e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  case appSS t1 t2 of
    Just t  -> Right t
    Nothing -> Left <<< TypeError $
      show t1 <> " cannot be applied to " <> show t2
typeOf ctx (Abs x e targ tret) = typeOf ctx' e >>= \tret' ->
  if tret' <: tret then Right $ Arr targ tret else Left <<< TypeError $
    "The return type " <> show tret <> " is not a supertype of " <> show tret'
  where ctx' = Tuple x (TermEntry targ) : ctx
typeOf ctx (Fix x e t) = typeOf ctx' e >>= \t' ->
  if t' <: t then Right t else Left <<< TypeError $
    "Fixpoint is annotated as " <> show t <> ", but got " <> show t'
  where ctx' = Tuple x (TermEntry t) : ctx
typeOf ctx (Anno e t) = typeOf ctx e >>= \t' ->
  if t' <: t then Right t else Left <<< TypeError $
    "The annotated type " <> show t <> " is not a supertype of " <> show t'
typeOf ctx (Merge e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  disjoint ctx t1 t2
  Right $ Intersect t1 t2
typeOf ctx (RecLit l e) = Rec l <$> typeOf ctx e
typeOf ctx (RecPrj e l) = typeOf ctx e >>= \t ->
  case appSS t (Rec l Top) of
    Just t' -> Right t'
    Nothing -> Left <<< TypeError $ show t <> " has no label named " <> show l
typeOf ctx (TyApp e ta) = typeOf ctx e >>= \tf -> case tf of
  Forall a td t -> disjoint ctx ta td $> tsubst a ta t
  _ -> Left <<< TypeError $ show tf <> " is not type-applicable"
typeOf ctx (TyAbs a td e t) = typeOf ctx' e >>= \t' ->
  if t' <: t then Right $ Forall a td t else Left <<< TypeError $
    "The return type " <> show t <> " is not a supertype of " <> show t'
  where ctx' = Tuple a (TypeEntry td) : ctx

appSS :: Ty -> Ty -> Maybe Ty
appSS Top _ = Just Top
appSS (Arr targ tret) t | t <: targ = Just tret
appSS (Rec l t) (Rec l' _) | l == l' = Just t
appSS (Intersect t1 t2) t | Just t1' <- appSS t1 t
                          , Just t2' <- appSS t2 t = Just $ Intersect t1' t2'
appSS _ _ = Nothing

disjoint :: Ctx -> Ty -> Ty -> Either TypeError Unit
disjoint _ t _ | isTopLike t = Right unit
disjoint _ _ t | isTopLike t = Right unit
disjoint ctx (Arr _ t1) (Arr _ t2) = disjoint ctx t1 t2
disjoint ctx (Intersect t1 t2) t3 = disjoint ctx t1 t3 *> disjoint ctx t2 t3
disjoint ctx t1 (Intersect t2 t3) = disjoint ctx (Intersect t2 t3) t1
disjoint ctx (Rec l1 t1) (Rec l2 t2) | l1 == l2 = disjoint ctx t1 t2
                                     | otherwise = Right unit
disjoint ctx (TyVar a) t = case lookup a ctx of
  Just (TypeEntry t') -> if t' <: t then Right unit else Left <<< TypeError $
    "Type " <> show a <> " is not disjoint from " <> show t
  _ -> Left <<< TypeError $ "Type " <> show a <> " is not defined"
disjoint ctx t (TyVar a) = disjoint ctx (TyVar a) t
disjoint ctx (Forall a1 td1 t1) (Forall a2 td2 t2) =
  disjoint ctx' t1 (tsubst a2 (TyVar a1) t2)
    where ctx' = Tuple a1 (TypeEntry (Intersect td1 td2)) : ctx
disjoint _ t1 t2 | t1 /= t2  = Right unit
                 | otherwise = Left <<< TypeError $
  show t1 <> " and " <> show t2 <> " are not disjoint"

tsubst :: Name -> Ty -> Ty -> Ty
tsubst a s (Arr t1 t2) = Arr (tsubst a s t1) (tsubst a s t2)
tsubst a s (Intersect t1 t2) = Intersect (tsubst a s t1) (tsubst a s t2)
tsubst a s (Rec l t) = Rec l (tsubst a s t)
tsubst a s (TyVar a') = if a == a' then s else TyVar a'
tsubst a s (Forall a' td t) =
  Forall a' (tsubst a s td) (if a == a' then t else tsubst a s t)
tsubst _ _ t = t
