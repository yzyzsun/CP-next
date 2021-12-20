module Language.CP.Semantics.NaturalSubst where

import Prelude

import Control.Monad.Trampoline (Trampoline, runTrampoline)
import Data.Maybe (Maybe(..))
import Language.CP.Semantics.Common (Arg(..), binop, selectLabel, toString, unop)
import Language.CP.Semantics.Subst (cast, paraApp)
import Language.CP.Subtyping (isTopLike)
import Language.CP.Syntax.Common (BinOp(..))
import Language.CP.Syntax.Core (Tm(..), done, new, read, tmSubst, unfold, write)
import Partial.Unsafe (unsafeCrashWith)

type Eval = Trampoline

eval :: Tm -> Tm
eval = runTrampoline <<< go
  where
    go :: Tm -> Eval Tm
    go e@(TmInt _)    = pure e
    go e@(TmDouble _) = pure e
    go e@(TmString _) = pure e
    go e@(TmBool _)   = pure e
    go TmUnit = pure TmUnit
    go TmUndefined = pure TmUndefined
    go (TmUnary op e) = unop op <$> go e
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
        _ -> unsafeCrashWith $ "CP.Semantics.NaturalSubst.eval: " <>
                               "impossible if " <> show e1' <> " ..."
    go (TmApp e1 e2 coercive) = do
      e1' <- go e1
      let arg = if coercive then TmAnnoArg else TmArg
      go $ paraApp e1' (arg (TmRef (new e2)))
    go e@(TmAbs _ _ _ _ _) = pure e
    go fix@(TmFix x e _) = do
      let ref = new fix
      res <- go $ tmSubst x (TmRef ref) e
      pure $ write res ref
    go anno@(TmAnno e t) = do
      e' <- go' e
      case cast e' t of
        Just e'' -> go e''
        Nothing -> unsafeCrashWith $ "CP.Semantics.NaturalSubst.eval: " <>
                                     "impossible casting " <> show anno
      where go' :: Tm -> Eval Tm
            go' (TmAnno e' _) = go' e'
            go' e' = go e'
    go (TmMerge e1 e2) = TmMerge <$> go e1 <*> go e2
    go (TmRcd l t e) = pure $ TmRcd l t (TmRef (new e))
    go (TmPrj e l) = selectLabel <$> go e <@> l >>= go
    go (TmTApp e t) = paraApp <$> go e <@> TyArg t >>= go
    go e@(TmTAbs _ _ _ _ _) = pure e
    go (TmFold t e) = TmFold t <$> go e
    go (TmUnfold t e) = if isTopLike t then pure TmUnit else go e >>= go'
      where go' :: Tm -> Eval Tm
            go' e'@(TmMerge _ _) = go' <=< go $ TmAnno e' t
            go' (TmFold _ v) = go $ TmAnno v (unfold t)
            go' e' = unsafeCrashWith $ "CP.Semantics.NaturalSubst.eval: " <>
                                       "impossible unfold " <> show e'
    go (TmToString e) = toString <$> go e
    go (TmArray t arr) = pure $ TmArray t (TmRef <<< new <$> arr)
    go (TmRef ref) = if done ref then pure e else do
      e' <- go e
      pure $ write e' ref
      where e = read ref
    go e = unsafeCrashWith $ "CP.Semantics.NaturalSubst.eval: " <>
      "well-typed programs don't get stuck, but got " <> show e
