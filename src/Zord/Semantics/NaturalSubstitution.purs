module Zord.Semantics.NaturalSubstitution where

import Prelude

import Data.Either (Either(..))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Common (binop, toString, unop)
import Zord.Semantics.Substitution (paraApp, selectLabel, typedReduce)
import Zord.Syntax.Common (fromJust)
import Zord.Syntax.Core (Tm(..), tmSubst)

eval :: Tm -> Tm
eval e@(TmInt _)    = e
eval e@(TmDouble _) = e
eval e@(TmString _) = e
eval e@(TmBool _)   = e
eval TmUnit = TmUnit
eval (TmUnary op e) = unop op (eval e)
eval (TmBinary op e1 e2) = binop op (eval e1) (eval e2)
eval (TmIf e1 e2 e3) = case eval e1 of
  TmBool true  -> eval e2
  TmBool false -> eval e3
  e1' -> unsafeCrashWith $
    "Zord.Semantics.NaturalSubstitution.eval: impossible if " <> show e1' <> " ..."
eval (TmApp e1 e2) = eval $ paraApp (eval e1) (Left e2)
eval e@(TmAbs _ _ _ _) = e
eval (TmFix x e t) = eval $ TmAnno (tmSubst x (TmFix x e t) e) t
eval (TmAnno e t) = eval $ fromJust (typedReduce (eval' e) t)
  where eval' :: Tm -> Tm
        eval' (TmAnno e' t') = eval' e'
        eval' e' = eval e'
eval (TmMerge e1 e2) = TmMerge (eval e1) (eval e2)
eval e@(TmRcd _ _ _) = e
eval (TmPrj e l) = eval $ selectLabel (eval e) l
eval (TmTApp e t) = eval $ paraApp (eval e) (Right t)
eval e@(TmTAbs _ _ _ _) = e
eval (TmToString e) = toString (eval e)
eval e = unsafeCrashWith $ "Zord.Semantics.NaturalSubstitution.eval: " <>
  "well-typed programs don't get stuck, but got " <> show e
