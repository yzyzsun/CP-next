module Zord.Semantics.NaturalClosure where

import Prelude

import Control.Monad.Reader (ask, local, runReader)
import Data.Either (Either(..))
import Data.Map (empty, insert, lookup)
import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Closure (Eval, binop', closure, expand, paraApp, selectLabel', typedReduce, unop')
import Zord.Semantics.Common (toString)
import Zord.Syntax.Common (BinOp(..), fromJust)
import Zord.Syntax.Core (EvalBind(..), Tm(..))

eval :: Tm -> Tm
eval tm = runReader (go tm) empty
  where
    go :: Tm -> Eval Tm
    go e@(TmInt _)    = pure e
    go e@(TmDouble _) = pure e
    go e@(TmString _) = pure e
    go e@(TmBool _)   = pure e
    go TmUnit = pure TmUnit
    go (TmUnary op e) = unop' op <$> go e
    go (TmBinary op e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      let e = binop' op e1' e2'
      case op of Index -> go e
                 _   -> pure e
    go (TmIf e1 e2 e3) = go e1 >>= \e1' -> case e1' of
      TmBool true  -> go e2
      TmBool false -> go e3
      _ -> unsafeCrashWith $ "Zord.Semantics.NaturalClosure.eval: " <>
        "impossible if " <> show e1' <> " ..."
    go (TmVar x) = ask >>= \env -> case lookup x env of
      Just (TmBind e) -> go e
      m -> unsafeCrashWith $ "Zord.Semantics.NaturalClosure.eval: " <>
        "variable " <> show x <> " is " <> show m
    go (TmApp e1 e2) = do
      e1' <- go e1
      e2' <- closure e2
      go $ paraApp e1' (Left e2')
    go e@(TmAbs _ _ _ _) = closure e
    go fix@(TmFix x e t) =
      local (\env -> insert x (TmBind fix) env) (go $ TmAnno e t)
    go (TmAnno e t) = do
      e' <- go' e
      t' <- expand t
      s <- typedReduce e' t'
      go $ fromJust s
      where go' :: Tm -> Eval Tm
            go' (TmAnno e' t') = go' e'
            go' e' = go e'
    go (TmMerge e1 e2) = TmMerge <$> go e1 <*> go e2
    go e@(TmRcd _ _ _) = closure e
    go (TmPrj e l) = go e >>= \e' -> go $ selectLabel' e' l
    go (TmTApp e t) = do
      e' <- go e
      t' <- expand t
      go $ paraApp e' (Right t')
    go e@(TmTAbs _ _ _ _) = closure e
    go (TmToString e) = toString <$> go e
    go e@(TmClosure _ (TmRcd _ _ _)) = pure e
    go e@(TmClosure _ (TmAbs _ _ _ _)) = pure e
    go e@(TmClosure _ (TmTAbs _ _ _ _)) = pure e
    go e@(TmClosure _ (TmArray _ _)) = pure e
    go (TmClosure env e) = local (const env) (go e)
    go e = unsafeCrashWith $ "Zord.Semantics.NaturalClosure.eval: " <>
      "well-typed programs don't get stuck, but got " <> show e