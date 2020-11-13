module Zord.Semantics.Natural where

import Prelude hiding (bind, pure)

import Control.Alt ((<|>))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Common (binop, selectLabel, toString, unop)
import Zord.Subtyping (isTopLike, split, (<:))
import Zord.Syntax.Common (fromJust)
import Zord.Syntax.Core (Tm(..), Ty(..), done, new, read, tmHoas, tyHoas, write)
import Zord.Trampoline (Trampoline, bind, pure, runTrampoline)

eval :: Tm -> Tm
eval = runTrampoline <<< go <<< tmHoas
  where
    go :: Tm -> Trampoline Tm
    go e@(TmInt _)    = pure e
    go e@(TmDouble _) = pure e
    go e@(TmString _) = pure e
    go e@(TmBool _)   = pure e
    go TmUnit = pure TmUnit
    go (TmUnary op e) = do
      e' <- go e
      pure $ unop op e'
    go (TmBinary op e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      pure $ binop op e1' e2'
    go (TmIf e1 e2 e3) = do
      e1' <- go e1
      case e1' of
        TmBool true  -> go e2
        TmBool false -> go e3
        _ -> unsafeCrashWith $
          "Zord.Semantics.Natural.eval: impossible if " <> show e1' <> " ..."
    go (TmApp e1 e2) = do
      e1' <- go e1
      go $ paraApp e1' (Left e2)
    go e@(TmHAbs _ _ _) = pure e
    go e@(TmHFix fix t) = go $ TmAnno (fix e) t
    go (TmAnno e t) = do
      e' <- go' e
      go $ fromJust (typedReduce e' t)
      where go' :: Tm -> Trampoline Tm
            go' (TmAnno e' t') = go' e'
            go' e' = go e'
    go (TmMerge e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      pure $ TmMerge e1' e2'
    go e@(TmRcd _ _ _) = pure e
    go (TmPrj e l) = do
      e' <- go e
      go $ selectLabel e' l
    go (TmTApp e t) = do
      e' <- go e
      go $ paraApp e' (Right t)
    go e@(TmHTAbs _ _ _) = pure e
    go (TmToString e) = do
      e' <- go e
      pure $ toString e'
    go (TmRef ref) = if done ref then pure e else do
      e' <- go e
      pure $ write e' ref
      where e = read ref
    go e = unsafeCrashWith $ "Zord.Semantics.Natural.eval: " <>
      "well-typed programs don't get stuck, but got " <> show e

typedReduce :: Tm -> Ty -> Maybe Tm
typedReduce e _ | not (isValue e) = unsafeCrashWith $
  "Zord.Semantics.Natural.typedReduce: " <> show e <> " is not a value"
typedReduce _ t | isTopLike t = Just TmUnit
typedReduce v t | Just (Tuple t1 t2) <- split t =
  case typedReduce v t1, typedReduce v t2 of
    Just v1, Just v2 -> Just $ TmMerge v1 v2
    _, _ -> Nothing
typedReduce (TmInt i)    TyInt    = Just $ TmInt i
typedReduce (TmDouble n) TyDouble = Just $ TmDouble n
typedReduce (TmString s) TyString = Just $ TmString s
typedReduce (TmBool b)   TyBool   = Just $ TmBool b
typedReduce (TmHAbs abs targ1 tret1) (TyArr targ2 tret2 _)
  | targ2 <: targ1 && tret1 <: tret2 = Just $ TmHAbs abs targ1 tret2
typedReduce (TmMerge v1 v2) t = typedReduce v1 t <|> typedReduce v2 t
typedReduce (TmRcd l t e) (TyRcd l' t')
  | l == l' && t <: t' = Just $ TmRcd l t' (TmAnno e t')
typedReduce (TmHTAbs tabs td1 tf1) (TyForall a td2 t2)
  | td2 <: td1 && tf1 (TyVar a) <: t2
  = Just $ TmHTAbs tabs td1 (tyHoas a t2)
typedReduce _ _ = Nothing

paraApp :: Tm -> Either Tm Ty -> Tm
paraApp TmUnit _ = TmUnit
paraApp (TmHAbs abs targ tret) (Left e2) =
  TmAnno (abs (TmRef <<< new $ TmAnno e2 targ)) tret
paraApp (TmHTAbs tabs _ tf) (Right ta) = TmAnno (tabs ta) (tf ta)
paraApp (TmMerge v1 v2) et = TmMerge (paraApp v1 et) (paraApp v2 et)
paraApp v e = unsafeCrashWith $ "Zord.Semantics.Natural.paraApp: " <>
  "impossible application " <> show v <> " • " <> show e

isValue :: Tm -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue (TmUnit)     = true
isValue (TmHAbs _ _ _) = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmRcd _ _ _) = true
isValue (TmHTAbs _ _ _) = true
isValue _ = false
