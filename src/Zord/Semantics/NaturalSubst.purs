module Zord.Semantics.NaturalSubst where

import Prelude hiding (bind, pure)

import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Common (Arg(..), binop, selectLabel, toString, unop)
import Zord.Semantics.Subst (paraApp, typedReduce)
import Zord.Syntax.Common (BinOp(..))
import Zord.Syntax.Core (Tm(..), done, new, read, tmSubst, write)
import Zord.Trampoline (Trampoline, bind, pure, runTrampoline)
import Zord.Util (unsafeFromJust)

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
      let e = binop op e1' e2'
      case op of Index -> go e
                 _   -> pure e
    go (TmIf e1 e2 e3) = do
      e1' <- go e1
      case e1' of
        TmBool true  -> go e2
        TmBool false -> go e3
        _ -> unsafeCrashWith $ "Zord.Semantics.NaturalSubst.eval: " <>
                               " impossible if " <> show e1' <> " ..."
    go (TmApp e1 e2 coercive) = do
      e1' <- go e1
      let arg = if coercive then TmAnnoArg else TmArg
      go $ paraApp e1' (arg (TmRef (new e2)))
    go e@(TmAbs _ _ _ _) = pure e
    go fix@(TmFix x e _) = do
      let ref = new fix
      res <- go $ tmSubst x (TmRef ref) e
      pure $ write res ref
    go (TmAnno e t) = do
      e' <- go' e
      go $ unsafeFromJust (typedReduce e' t)
      where go' :: Tm -> Trampoline Tm
            go' (TmAnno e' _) = go' e'
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
      go $ paraApp e' (TyArg t)
    go e@(TmTAbs _ _ _ _) = pure e
    go (TmToString e) = do
      e' <- go e
      pure $ toString e'
    go e@(TmArray _ _) = pure e
    go (TmRef ref) = if done ref then pure e else do
      e' <- go e
      pure $ write e' ref
      where e = read ref
    go e = unsafeCrashWith $ "Zord.Semantics.NaturalSubst.eval: " <>
      "well-typed programs don't get stuck, but got " <> show e
