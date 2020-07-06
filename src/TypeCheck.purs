module Zord.TypeCheck where

import Prelude

import Data.Either (Either(..))
import Data.List ((:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), lookup)
import Zord.Subtyping ((<:))
import Zord.Syntax (BinOp(..), Ctx, Expr(..), Ty(..), UnOp(..))

data TypeError = TypeError String

instance showTypeError :: Show TypeError where
  show (TypeError str) = "TypeError: " <> str

typeOf :: Ctx -> Expr -> Either TypeError Ty
typeOf ctx (IntLit _)    = Right Integer
typeOf ctx (DoubleLit _) = Right Double
typeOf ctx (StrLit _)    = Right Str
typeOf ctx (BoolLit _)   = Right Bool
typeOf ctx (UnitLit)     = Right Top
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
  Just t -> Right t
  _ -> Left <<< TypeError $ "Variable " <> show x <> " is not defined"
typeOf ctx (App e1 e2) = typeOf ctx e1 >>= \t1 -> case t1 of
  Arr targ tret -> typeOf ctx e2 >>= \t2 ->
    if t2 <: targ then Right tret else Left <<< TypeError $
      "The argument type " <> show t2 <> " is not a subtype of " <> show targ
  _ -> Left <<< TypeError $ show t1 <> " is not applicable"
typeOf ctx (Abs x e targ tret) = typeOf (Tuple x targ : ctx) e >>= \tret' ->
  if tret' <: tret then Right $ Arr targ tret else Left <<< TypeError $
    "The return type " <> show tret <> " is not a supertype of " <> show tret'
typeOf ctx (Fix x e t) = typeOf (Tuple x t : ctx) e >>= \t' ->
  if t' == t then Right t else Left <<< TypeError $
    "Fixpoint is annotated as " <> show t <> ", but got " <> show t'
typeOf ctx (Anno e t) = typeOf ctx e >>= \t' ->
  if t' <: t then Right t else Left <<< TypeError $
    "The annotated type " <> show t <> " is not a supertype of " <> show t'
typeOf ctx (Merge e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  if disjoint t1 t2 then Right $ Intersect t1 t2 else Left <<< TypeError $
    show t1 <> " and " <> show t2 <> " are not disjoint so cannot be merged"

disjoint :: Ty -> Ty -> Boolean
disjoint Top _ = true
disjoint _ Top = true
disjoint (Arr _ t1) (Arr _ t2) = disjoint t1 t2
disjoint (Intersect t1 t2) t3 = disjoint t1 t3 && disjoint t2 t3
disjoint t1 (Intersect t2 t3) = disjoint t1 t2 && disjoint t1 t3
disjoint t1 t2 | t1 /= t2  = true
               | otherwise = false
