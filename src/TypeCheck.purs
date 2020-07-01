module Zord.TypeCheck where

import Prelude

import Data.List ((:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), lookup)
import Zord.Syntax (BinOp(..), Ctx, Expr(..), Ty(..), UnOp(..))

typeOf :: Ctx -> Expr -> Maybe Ty
typeOf ctx (IntLit _)    = Just Integer
typeOf ctx (DoubleLit _) = Just Double
typeOf ctx (StrLit _)    = Just Str
typeOf ctx (BoolLit _)   = Just Bool
typeOf ctx (UnitLit)     = Just Top
typeOf ctx (Unary Neg e)  = do
  t <- typeOf ctx e
  case t of Integer -> Just Integer
            Double  -> Just Double
            _       -> Nothing
typeOf ctx (Unary Not e)  = do
  t <- typeOf ctx e
  case t of Bool -> Just Bool
            _    -> Nothing
typeOf ctx (Binary (Arith _) e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  case t1, t2 of Integer, Integer -> Just Integer
                 Double,  Double  -> Just Double
                 _,       _       -> Nothing
typeOf ctx (Binary (Comp _) e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  case t1, t2 of Integer, Integer -> Just Bool
                 Double,  Double  -> Just Bool
                 Str,     Str     -> Just Bool
                 Bool,    Bool    -> Just Bool
                 _,       _       -> Nothing
typeOf ctx (Binary (Logic _) e1 e2) = do
  t1 <- typeOf ctx e1
  t2 <- typeOf ctx e2
  case t1, t2 of Bool, Bool -> Just Bool
                 _,    _    -> Nothing
typeOf ctx (Var x) = lookup x ctx
typeOf ctx (Abs x t e) = Arr t <$> typeOf (Tuple x t : ctx) e
typeOf ctx (App e1 e2) = typeOf ctx e1 >>= \t1 -> case t1 of
  Arr targ tret -> typeOf ctx e2 >>= \t2 ->
    if t2 == targ then Just tret else Nothing
  _ -> Nothing
typeOf ctx (Anno e t) = typeOf ctx e >>= \t' ->
  if t == t' then Just t else Nothing
