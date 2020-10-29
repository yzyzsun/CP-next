module Zord.Semantics.Natural where

import Prelude hiding (bind, pure)

import Data.Either (Either(..))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Common (binop, toString, unop)
import Zord.Semantics.Substitution (paraApp, selectLabel, typedReduce)
import Zord.Syntax.Common (fromJust)
import Zord.Syntax.Core (Tm(..), tmSubst)
import Zord.Trampoline (Trampoline, bind, pure, runTrampoline)

eval :: Tm -> Tm
eval = runTrampoline <<< go
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
    go e@(TmAbs _ _ _ _) = pure e
    go (TmFix x e t) = go $ TmAnno (tmSubst x (TmFix x e t) e) t
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
    go e@(TmTAbs _ _ _ _) = pure e
    go (TmToString e) = do
      e' <- go e
      pure $ toString e'
    go e = unsafeCrashWith $ "Zord.Semantics.Natural.eval: " <>
      "well-typed programs don't get stuck, but got " <> show e
