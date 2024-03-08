module Language.CP.Semantics.NaturalClosure where

import Prelude

import Control.Monad.Reader (ask, local, runReaderT)
import Control.Monad.Trampoline (Trampoline, runTrampoline)
import Data.Map (empty, insert, lookup)
import Data.Maybe (Maybe(..))
import Language.CP.Semantics.Closure (EvalT, binop', cast, closure, expand, paraApp, selectLabel, unop')
import Language.CP.Semantics.Common (Arg(..), toString)
import Language.CP.Subtyping (isTopLike)
import Language.CP.Syntax.Common (BinOp(..))
import Language.CP.Syntax.Core (EvalBind(..), Tm(..), Ty(..), alloc, done, read, unfold, write)
import Partial.Unsafe (unsafeCrashWith)

type Eval = EvalT Trampoline

eval :: Tm -> Tm
eval tm = runTrampoline (runReaderT (go tm) empty)
  where
    go :: Tm -> Eval Tm
    go e@(TmInt _)    = pure e
    go e@(TmDouble _) = pure e
    go e@(TmString _) = pure e
    go e@(TmBool _)   = pure e
    go TmUnit = pure TmUnit
    go TmTop  = pure TmTop
    go (TmUnary op e) = unop' op <$> go e
    go (TmBinary op e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      let e = binop' op e1' e2'
      case op of Index -> go e
                 _   -> pure e
    go (TmIf e1 e2 e3) = do
      e1' <- go e1
      case e1' of
        TmBool true  -> go e2
        TmBool false -> go e3
        _ -> unsafeCrashWith $ "CP.Semantics.NaturalClosure.eval: " <>
                               "impossible if " <> show e1' <> " ..."
    go (TmVar x) = do
      env <- ask
      case lookup x env of
        Just (TmBind e) -> go e
        m -> unsafeCrashWith $ "CP.Semantics.NaturalClosure.eval: " <>
                               "variable " <> show x <> " is " <> show m
    go (TmApp e1 e2 coercive) = do
      e1' <- go e1
      e2' <- closure e2
      let arg = if coercive then TmAnnoArg else TmArg
      go $ paraApp e1' (arg (TmCell (alloc e2')))
    go e@(TmAbs _ _ _ _ _ _) = closure e
    go (TmFix x e _) = local (\env -> insert x (TmBind e) env) (go e)
    go (TmAnno e t) = do
      e' <- go' e
      t' <- expand t
      s <- cast e' t'
      case s of
        Just e'' -> go e''
        Nothing -> unsafeCrashWith $ "CP.Semantics.NaturalClosure.eval: " <>
                       "impossible casting " <> show e' <> " : " <> show t
      where go' :: Tm -> Eval Tm
            go' (TmAnno e' _) = go' e'
            go' e' = go e'
    go (TmMerge e1 e2) = TmMerge <$> go e1 <*> go e2
    go e@(TmRcd _ _ _) = closure e
    go (TmPrj e l) = selectLabel <$> go e <@> l >>= go
    go (TmOptPrj e1 l t e2) = do
      e1' <- go e1
      t' <- expand t
      s <- cast e1' (TyRcd l t' false)
      case s of
        Just e -> go $ TmPrj e l
        Nothing -> go e2
    go (TmTApp e t) = do
      e' <- go e
      t' <- expand t
      go $ paraApp e' (TyArg t')
    go e@(TmTAbs _ _ _ _ _) = closure e
    go (TmDef x e1 e2) = do
      e1' <- closure e1
      local (\env -> insert x (TmBind (TmCell (alloc e1'))) env) (go e2)
    go (TmFold t e) = TmFold t <$> go e
    go (TmUnfold t e) =  if isTopLike t then pure TmTop else go e >>= go'
      where go' :: Tm -> Eval Tm
            go' e'@(TmMerge _ _) = go' <=< go $ TmAnno e' t
            go' (TmFold _ v) = go $ TmAnno v (unfold t)
            go' e' = unsafeCrashWith $ "CP.Semantics.NaturalClosure.eval: " <>
                                       "impossible unfold " <> show e'
    go (TmToString e) = toString <$> go e
    go e@(TmArray _ _) = closure e
    go (TmMain e) = go e
    go (TmCell cell) = if done cell then pure e else do
      e' <- go e
      pure $ write e' cell
      where e = read cell
    go e@(TmClosure _ (TmRcd _ _ _)) = pure e
    go e@(TmClosure _ (TmAbs _ _ _ _ _ _)) = pure e
    go e@(TmClosure _ (TmTAbs _ _ _ _ _)) = pure e
    go e@(TmClosure _ (TmArray _ _)) = pure e
    go (TmClosure env e) = local (const env) (go e)
    go e = unsafeCrashWith $ "CP.Semantics.NaturalClosure.eval: " <>
      "well-typed programs don't get stuck, but got " <> show e
