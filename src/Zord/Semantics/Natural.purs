module Zord.Semantics.Natural where

import Prelude

import Data.Either (Either(..))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Common (binop, toString, unop)
import Zord.Semantics.Substitution (paraApp, selectLabel, typedReduce)
import Zord.Syntax.Common (fromJust)
import Zord.Syntax.Core (Tm(..), tmSubst)
import Zord.Trampoline (Trampoline(..), runTrampoline)

eval :: Tm -> Tm
eval = runTrampoline <<< go
  where
    go :: Tm -> Trampoline Tm
    go e@(TmInt _)    = Done e
    go e@(TmDouble _) = Done e
    go e@(TmString _) = Done e
    go e@(TmBool _)   = Done e
    go TmUnit = Done TmUnit
    go (TmUnary op e) = Bind (go e) \e' -> Done $ unop op e'
    go (TmBinary op e1 e2) =
      Bind (go e1) \e1' -> Bind (go e2) \e2' -> Done $ binop op e1' e2'
    go (TmIf e1 e2 e3) = Bind (go e1) \e1' -> case e1' of
      TmBool true  -> go e2
      TmBool false -> go e3
      _ -> unsafeCrashWith $
        "Zord.Semantics.Natural.eval: impossible if " <> show e1' <> " ..."
    go (TmApp e1 e2) = Bind (go e1) \e1' -> go $ paraApp e1' (Left e2)
    go e@(TmAbs _ _ _ _) = Done e
    go (TmFix x e t) = go $ TmAnno (tmSubst x (TmFix x e t) e) t
    go (TmAnno e t) = Bind (go' e) \e' -> go $ fromJust (typedReduce e' t)
      where go' :: Tm -> Trampoline Tm
            go' (TmAnno e' t') = go' e'
            go' e' = go e'
    go (TmMerge e1 e2) =
      Bind (go e1) \e1' -> Bind (go e2) \e2' -> Done $ TmMerge e1' e2'
    go e@(TmRcd _ _ _) = Done e
    go (TmPrj e l) = Bind (go e) \e' -> go $ selectLabel e' l
    go (TmTApp e t) = Bind (go e) \e' -> go $ paraApp e' (Right t)
    go e@(TmTAbs _ _ _ _) = Done e
    go (TmToString e) = Bind (go e) \e' -> Done $ toString e'
    go e = unsafeCrashWith $ "Zord.Semantics.Natural.eval: " <>
      "well-typed programs don't get stuck, but got " <> show e
